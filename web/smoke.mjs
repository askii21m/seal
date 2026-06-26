// End-to-end wasm smoke test: load the compiled .wasm in a real JS runtime
// (node), compile the corpus contracts through the SAME pipeline the CLI uses,
// and assert the browser path produces the same kind of result.
//
//   node web/smoke.mjs
//
// Requires the debug wasm build:
//   cargo build --manifest-path seal-wasm/Cargo.toml --target wasm32-unknown-unknown

import { readFileSync } from "node:fs";
import { Seal } from "./seal.js";

const root = new URL("..", import.meta.url);
const wasmPath = process.env.WASM
  ? process.env.WASM
  : new URL("seal-wasm/target/wasm32-unknown-unknown/debug/seal_wasm.wasm", root);
const ex = (f) => readFileSync(new URL(`tests/corpus/${f}`, root), "utf8");

const bs = await Seal.load(readFileSync(wasmPath));
let failures = 0;
const check = (cond, msg, ctx) => {
  if (cond) {
    console.log("  ok:", msg);
  } else {
    console.error("  FAIL:", msg, ctx ?? "");
    failures++;
  }
};

// 1. A proven corpus contract: a fundable mainnet address + a clean gate.
{
  const r = bs.compile(ex("multisig.sl"), { args: ex("multisig.args.json"), target: "fund" });
  check(r.ok === true, "multisig ok", r.diagnostics);
  check(typeof r.address === "string" && r.address.startsWith("bc1p"), "multisig address is bc1p", r.address);
  check(r.gate && r.gate.mayProceed === true, "multisig gate mayProceed", r.gate);
  check(Array.isArray(r.certification) && r.certification.length > 0, "multisig has certification", r.certification);
  check(Array.isArray(r.leaves) && r.leaves[0] && typeof r.leaves[0].hex === "string", "multisig has lowered leaves", r.leaves);
}

// 2. Determinism: the browser address must equal a second run byte-for-byte.
{
  const a = bs.compile(ex("vault.sl"), { args: ex("vault.args.json"), target: "fund" });
  const b = bs.compile(ex("vault.sl"), { args: ex("vault.args.json"), target: "fund" });
  check(a.address && a.address === b.address, "vault address is deterministic across runs", [a.address, b.address]);
}

// 3. Fail-closed: an unprovable contract refuses to emit an address.
{
  const src = "contract U {\n  extern const k: PublicKey;\n  " +
    "spend f(relaxed a: Int, relaxed b: Int, s: Signature) {\n    " +
    "require { a < b, k.check(s) }\n  }\n  keypath None;\n}\n";
  const args = '{ "k": "0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c" }\n';
  const r = bs.compile(src, { args, target: "fund" });
  check(r.gate && r.gate.mayProceed === false, "unprovable gate refuses", r.gate);
  check(r.address === undefined, "unprovable emits NO address", r.address);
}

// 4. Diagnostics carry line/col for the editor.
{
  const r = bs.compile("contract {{{ not valid", { target: "check" });
  check(r.ok === false, "broken parse is not ok");
  const d = (r.diagnostics || [])[0];
  check(d && d.start && d.start.line === 1 && typeof d.start.col === "number", "diagnostic has line/col", d);
}

if (failures) {
  console.error(`\nwasm smoke FAILED: ${failures} check(s)`);
  process.exit(1);
}
console.log("\nwasm smoke OK");
