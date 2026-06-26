// Zero-dependency loader for the Seal wasm compiler (no wasm-bindgen).
//
// The whole compiler runs in the browser; there is no server. Compilation is a
// pure, deterministic function of (source, args), so the address you get here
// is the same one the `seal` CLI derives, and anyone can re-verify it against the
// lockfile.
//
// Usage:
//   import { Seal } from "./seal.js";
//   const bs = await Seal.load("./seal_wasm.wasm");   // path | Response | bytes
//   const r = bs.compile(source, { args, target: "fund", allowUnproven: false });
//   if (r.ok) console.log(r.address); else console.log(r.diagnostics);
//
// `compile` returns the parsed result object:
//   { ok, boundExterns, diagnostics: [{file, code, severity, message,
//       span:{start,end}, start:{line,col}, end:{line,col}, notes}],
//     address?, outputKey?, lockfile?, leaves?, certification?, gate?,
//     costs?, facts? }
// Optional keys are present only when the pipeline produced them.

const TARGETS = { check: 0, lower: 1, certify: 2, cost: 3, fund: 4 };

export class Seal {
  constructor(instance) {
    this.exports = instance.exports;
  }

  // Accepts a URL/path string, a fetch Response, an ArrayBuffer, or a
  // TypedArray/Buffer of the .wasm bytes.
  static async load(source) {
    let bytes;
    if (typeof source === "string") {
      bytes = await (await fetch(source)).arrayBuffer();
    } else if (source && typeof source.arrayBuffer === "function") {
      bytes = await source.arrayBuffer(); // Response
    } else {
      bytes = source; // ArrayBuffer / TypedArray / Buffer
    }
    const { instance } = await WebAssembly.instantiate(bytes, {});
    return new Seal(instance);
  }

  // Always read memory.buffer fresh: a compile may grow wasm memory, which
  // detaches any previously-captured ArrayBuffer.
  get _mem() {
    return this.exports.memory.buffer;
  }

  _writeString(str) {
    const bytes = new TextEncoder().encode(str);
    if (bytes.length === 0) return { ptr: 0, len: 0 };
    const ptr = this.exports.bs_alloc(bytes.length);
    if (ptr === 0) throw new Error("seal: wasm allocation failed");
    new Uint8Array(this._mem, ptr, bytes.length).set(bytes);
    return { ptr, len: bytes.length };
  }

  // Returns the RAW JSON string the compiler emitted. Byte-for-byte identical
  // to `seal --json` for the same input (both call the same result_to_json), so
  // it is the seal for the native/wasm cross-check.
  compileJson(source, opts = {}) {
    const { args = null, target = "fund", allowUnproven = false } = opts;
    const t = TARGETS[target] ?? TARGETS.fund;
    const src = this._writeString(source);
    const a = args == null ? { ptr: 0, len: 0 } : this._writeString(args);

    const out = this.exports.bs_compile(
      src.ptr, src.len, a.ptr, a.len, t, allowUnproven ? 1 : 0,
    );
    if (out === 0) throw new Error("seal: compile returned null (allocation failed)");

    // [u32 LE jsonLen][jsonLen UTF-8 bytes]. Decode before freeing.
    const len = new DataView(this._mem).getUint32(out, true);
    const json = new TextDecoder().decode(new Uint8Array(this._mem, out + 4, len));

    this.exports.bs_free(out, 4 + len);
    if (src.len) this.exports.bs_free(src.ptr, src.len);
    if (a.len) this.exports.bs_free(a.ptr, a.len);

    return json;
  }

  // The parsed result object (see the module header for its shape).
  compile(source, opts = {}) {
    return JSON.parse(this.compileJson(source, opts));
  }
}
