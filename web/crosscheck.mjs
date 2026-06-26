// CI safety net: prove the wasm build is BYTE-FOR-BYTE identical to the audited
// NATIVE build on every corpus contract. Both paths call the same compile() +
// result_to_json(); the only thing that differs is the codegen target. A
// wasm-specific codegen bug that changed an address (a wrong secp/hash/decide
// result under wasm32) would otherwise ship silently -- this catches it by
// comparing the full `--json` output of `seal` against the wasm output.
//
//   node web/crosscheck.mjs
//   BASISC=path/to/seal WASM=path/to.wasm node web/crosscheck.mjs
//
// Defaults: native seal at target/debug/seal; wasm at
// seal-wasm/target/wasm32-unknown-unknown/debug/seal_wasm.wasm.

import { readFileSync, readdirSync } from "node:fs";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { Seal } from "./seal.js";

const root = new URL("..", import.meta.url);
const corpusDir = new URL("tests/corpus/", root);

const seal = process.env.BASISC || fileURLToPath(new URL("target/debug/seal", root));
const wasmPath = process.env.WASM
  ? process.env.WASM
  : fileURLToPath(new URL("seal-wasm/target/wasm32-unknown-unknown/debug/seal_wasm.wasm", root));

// Every example that has both a .sl and a .args.json.
const names = readdirSync(corpusDir)
  .filter((f) => f.endsWith(".sl"))
  .map((f) => f.slice(0, -3))
  .filter((n) => {
    try {
      readFileSync(new URL(`tests/corpus/${n}.args.json`, root));
      return true;
    } catch {
      return false;
    }
  })
  .sort();

if (names.length === 0) {
  console.error("crosscheck: no examples with .sl + .args.json found");
  process.exit(1);
}

const bs = await Seal.load(readFileSync(wasmPath));
let failures = 0;

for (const name of names) {
  const bsFile = fileURLToPath(new URL(`tests/corpus/${name}.sl`, root));
  const argsFile = fileURLToPath(new URL(`tests/corpus/${name}.args.json`, root));
  const source = readFileSync(bsFile, "utf8");
  const args = readFileSync(argsFile, "utf8");

  // Native: `seal <bs> --args <args> --json` -> JSON on stdout (exits 0).
  const native = execFileSync(seal, [bsFile, "--args", argsFile, "--json"], {
    encoding: "utf8",
    maxBuffer: 64 * 1024 * 1024,
  }).trim();
  // Wasm: the same pipeline, in a JS runtime.
  const wasm = bs.compileJson(source, { args, target: "fund" }).trim();

  if (native === wasm) {
    const obj = JSON.parse(wasm);
    const tag = obj.address ? `address ${obj.address}` : `ok=${obj.ok}`;
    console.log(`  ok: ${name}, native == wasm (${native.length} bytes, ${tag})`);
  } else {
    failures++;
    let i = 0;
    while (i < native.length && i < wasm.length && native[i] === wasm[i]) i++;
    console.error(`  MISMATCH: ${name}, native != wasm at byte ${i}`);
    console.error(`    native: ${JSON.stringify(native.slice(Math.max(0, i - 20), i + 40))}`);
    console.error(`    wasm:   ${JSON.stringify(wasm.slice(Math.max(0, i - 20), i + 40))}`);
  }
}

if (failures) {
  console.error(`\nnative/wasm cross-check FAILED: ${failures}/${names.length} examples diverged`);
  process.exit(1);
}
console.log(`\nnative/wasm cross-check OK: ${names.length} corpus contracts byte-identical across targets`);
