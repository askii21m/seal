# Seal in the browser (fully client-side)

The compiler runs entirely in the browser as WebAssembly, **there is no
server**. Hosting is static files (the `.wasm` + `seal.js` + your page) on
any CDN/Pages/IPFS. Because compilation is a pure, deterministic function of
`(source, args)`, the address you get in the browser is the same one the `seal`
CLI derives, and anyone can re-verify it against the lockfile (`seal ... --verify`).

## Pieces

- `seal-wasm/`, a thin, **zero-dependency** wasm32 shim (raw `extern "C"`,
  no `wasm-bindgen`). It marshals strings across the wasm boundary and calls the
  same `compile()` + `result_to_json()` the CLI uses, so the web path cannot
  derive a different address. The compiler crate stays dependency-free.
- `web/seal.js`, a small zero-dependency loader (`Seal.load` /
  `.compile`).
- `web/smoke.mjs`, an end-to-end test runner (node).

## Build

The wasm32 target is required once:

```sh
rustup target add wasm32-unknown-unknown
```

Debug build (fast; large `.wasm`, fine for local dev + the smoke test):

```sh
cargo build --manifest-path seal-wasm/Cargo.toml --target wasm32-unknown-unknown
# -> seal-wasm/target/wasm32-unknown-unknown/debug/seal_wasm.wasm
```

Release build (small `.wasm` to actually ship, `opt-level=z` + LTO + strip):

```sh
cargo build --manifest-path seal-wasm/Cargo.toml --target wasm32-unknown-unknown --release
# optional further shrink, if wasm-opt is installed:
wasm-opt -Oz -o seal.wasm \
  seal-wasm/target/wasm32-unknown-unknown/release/seal_wasm.wasm
```

## Smoke test

```sh
node web/smoke.mjs
```

## Use in a page

```js
import { Seal } from "./seal.js";

const bs = await Seal.load("./seal.wasm");
const result = bs.compile(sourceText, {
  args: argsJsonText,        // omit / null for a template-level check
  target: "fund",            // "check" | "lower" | "certify" | "cost" | "fund"
  allowUnproven: false,      // leave false in a public IDE (see note)
});

if (result.ok) {
  console.log("address:", result.address);   // present only when the gate allows it
} else {
  for (const d of result.diagnostics) {
    // d.file ("source" | "args"), d.severity, d.message,
    // d.start/{line,col}, d.end/{line,col}  -> editor squiggles
  }
}
```

`compile` returns the parsed result object: `ok`, `boundExterns`,
`diagnostics`, and (when produced) `address`, `outputKey`, `lockfile`,
`leaves`, `certification`, `gate`, `costs`, `facts`. The `gate` object
(`mayProceed`, `divergence`, `unproven`, `coverageGap`) is the fail-closed
verdict: when `mayProceed` is false, **no address is emitted**, the contract
isn't proven correct over its full domain.

> Note: prefer leaving `allowUnproven` off in a public IDE. It can emit a
> fundable address for a leaf whose script is not proven to match its predicate.
