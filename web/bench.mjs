// Rough latency probe: per-contract compile time in a real JS engine (node/V8)
// using the DEBUG wasm. Debug is the pessimistic floor -- a release build
// (opt-level=z + LTO) is materially faster. Separates the on-keystroke LINT
// path (target "check": parse+sema+intervals+paths, no lowering/certify) from
// the full compile (target "fund": + lower + certify + taproot + lockfile).
//
//   node web/bench.mjs

import { readFileSync, readdirSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { Seal } from "./seal.js";

const root = new URL("..", import.meta.url);
const wasm = process.env.WASM
  ? process.env.WASM
  : fileURLToPath(
      new URL("seal-wasm/target/wasm32-unknown-unknown/debug/seal_wasm.wasm", root),
    );
const wasmBytes = readFileSync(wasm);
console.log(`wasm: ${wasm}\nsize: ${(wasmBytes.length / 1024).toFixed(1)} KiB\n`);
const bs = await Seal.load(wasmBytes);

const names = readdirSync(new URL("tests/corpus/", root))
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

const median = (xs) => [...xs].sort((a, b) => a - b)[xs.length >> 1];

function bench(src, args, target, iters) {
  for (let i = 0; i < 5; i++) bs.compileJson(src, { args, target }); // warm
  const t = [];
  for (let i = 0; i < iters; i++) {
    const a = performance.now();
    bs.compileJson(src, { args, target });
    t.push(performance.now() - a);
  }
  return median(t);
}

console.log("per-contract latency, wasm in node/V8 (set WASM=... to pick debug vs release)\n");
console.log("contract".padEnd(12) + "check (lint)".padStart(14) + "fund (full)".padStart(14) + "  jsonBytes");
for (const n of names) {
  const src = readFileSync(new URL(`tests/corpus/${n}.sl`, root), "utf8");
  const args = readFileSync(new URL(`tests/corpus/${n}.args.json`, root), "utf8");
  const check = bench(src, args, "check", 100);
  const fund = bench(src, args, "fund", 100);
  const bytes = bs.compileJson(src, { args, target: "fund" }).length;
  console.log(
    n.padEnd(12) +
      `${check.toFixed(2)}ms`.padStart(14) +
      `${fund.toFixed(2)}ms`.padStart(14) +
      `  ${bytes}`,
  );
}
