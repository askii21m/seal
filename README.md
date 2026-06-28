<p align="center">
  <img src="assets/selkie.svg" width="116" alt="Selkie, the Seal mascot" />
</p>

<h1 align="center">Seal</h1>

<p align="center">
  A language for Bitcoin spending conditions you can read, review, and trust.
</p>

<p align="center">
  <a href="#example">Example</a> &nbsp;&middot;&nbsp;
  <a href="#building">Building</a> &nbsp;&middot;&nbsp;
  <a href="#how-it-works">How it works</a> &nbsp;&middot;&nbsp;
  <a href="#compared-to-miniscript">vs. Miniscript</a> &nbsp;&middot;&nbsp;
  <a href="#status">Status</a>
</p>

<p align="center">
  <a href="https://github.com/askii21m/seal/actions/workflows/ci.yml"><img src="https://github.com/askii21m/seal/actions/workflows/ci.yml/badge.svg" alt="CI" /></a>
  &nbsp;
  <img src="https://img.shields.io/badge/license-MIT-blue.svg" alt="License: MIT" />
  &nbsp;
  <img src="https://img.shields.io/badge/status-alpha-ee9a76.svg" alt="Status: alpha" />
</p>

---

Seal is a high-level language for writing Bitcoin spending conditions. The
compiler, `seal`, turns a `.sl` contract into an optimized tapscript tree and a
Pay-to-Taproot address, and it refuses to emit that address unless it has proven
that every spend path enforces exactly what the source says.

The goal is to make on-chain conditions something you can read, review, and trust
without hand-auditing raw Script. You write the policy; the compiler does the
encoding, the optimization, and the per-output correctness proof.

## Example

```
contract Htlc {
    extern const refund_key: PublicKey;
    extern const swap_key:   PublicKey;
    extern const timelock:   LockTime.Absolute;
    extern const hashlock:   Bytes<32>;

    // The counterparty reveals the preimage and signs.
    spend swap(preimage: Bytes<32>, signature: Signature) {
        require {
            sha256(preimage) == hashlock,
            swap_key.check(signature)
        }
    }

    // The swap timed out: the owner reclaims after the locktime.
    spend refund(signature: Signature) {
        require {
            after(timelock),
            refund_key.check(signature)
        }
    }

    // Cooperative close: both parties sign jointly on the key path.
    keypath PublicKey.MuSig2([swap_key, refund_key]);
}
```

```
$ seal examples/htlc.sl --args examples/htlc.args.json --address
certify `swap`: proven -- full symbolic domain (every assignment of 2 witness atoms)
certify `refund`: certified -- 2 witnesses (exhaustive)
address:      bc1pxfryx3afulynuk6qay8cc02l9x84m60chmexayxy2mprxu2zepqqlrhvsu
```

The three contracts in [`examples/`](examples/) are the place to start; the full
test corpus lives in [`tests/corpus/`](tests/corpus/).

## Building

Seal has no third-party dependencies. A stable Rust toolchain (1.87 or newer)
is all you need.

```
cargo build --release        # builds the `seal` binary at target/release/seal
cargo test                   # runs the in-process test suite
```

## Usage

```
seal <file.sl>                        check syntax and semantics
seal <file.sl> --args <file.json>     bind concrete keys and values
seal <file.sl> --args <file.json> --script    print the tapscript per leaf
seal <file.sl> --args <file.json> --certify   prove each leaf against its source
seal <file.sl> --args <file.json> --address   assemble the taproot address
seal <file.sl> --args <file.json> --lock      write a reproducible <file>.lock
seal <file.sl> --args <file.json> --json      emit the full result as JSON
```

Run `seal --help` for the complete list.

## How it works

A contract is a set of named spend paths over typed witnesses. The compiler:

1. Checks types, bounds, and feasibility, rejecting any path that can never be
   satisfied or that leaves a witness unbound to the transaction.
2. Lowers each path to tapscript and optimizes the encoding.
3. Certifies every leaf. For each spend path it proves that the optimized
   script, a naive reference encoding, and the source predicate all agree across
   the full witness domain, exhaustively where the domain is finite and
   symbolically where it is not.
4. Assembles the taproot output behind a fail-closed funding gate: a leaf that is
   not proven, or that is shown to diverge from its source, blocks the address.

Compilation is a pure, deterministic function of the source, the bound values,
and the compiler version. There is no I/O, clock, or ambient randomness anywhere
in the pipeline.

## Compared to Miniscript

Miniscript is the established way to write structured, analyzable Bitcoin Script.
For standard custody (keys, timelocks, hashlocks, thresholds) it is the mature,
peer-reviewed, widely deployed choice, with generic satisfaction and descriptor
and wallet integration. If that is your use case, reach for Miniscript.

Seal sits at a different point in the design space:

- Verified compilation, not correct-by-construction. Miniscript is safe because
  it is a structured view of a known-good subset of Script. Seal compiles a
  higher-level predicate to arbitrary tapscript and then proves, for that
  specific output, that the optimized script, a naive reference encoding, and the
  source predicate all agree across the entire witness domain, with the
  interpreter cross-checked against Bitcoin Core's consensus engine. The
  guarantee is about the exact bytes you would fund, not trust in a compiler.

- A more expressive source. Seal predicates include arithmetic, sums, counts, and
  ranges over witness data, which fall outside Miniscript's fragment set. That
  expressiveness is also why the per-compile proof exists: the language is not
  restricted to constructs that are safe by definition.

Seal is alpha and unaudited, with no wallet integration or standardization, and
Miniscript leads on all three. Treat Seal as a verification-forward experiment,
not a Miniscript replacement.

## Layout

```
examples/        three contracts to read first (HTLC, multisig, vault), each with bound arguments and a committed lockfile
src/
  syntax/        lexing and parsing
  analysis/      type checking, intervals, and feasibility
  codegen/       lowering to tapscript and optimization
  verify/        per-leaf certification and the reference interpreter
  crypto/        zero-dependency secp256k1, Schnorr, and hashes
  output/        taproot assembly, address encoding, and the lockfile
tests/           unit, fuzz, and differential tests
tests/corpus/    sample contracts, each with bound arguments and a committed lockfile
vendor/          Bitcoin Core, as a submodule, for the consensus differential tests
```

## Testing

The standard suite runs in process and needs nothing external:

```
cargo test
```

The differential tests compare the in-tree interpreter against Bitcoin Core's
own consensus engine and spend real outputs through a regtest node. They require
the vendored Core submodule to be built (see [`vendor/README.md`](vendor/README.md)):

```
git submodule update --init --recursive
cargo test --test core_consensus_differential
```

## Status

This is alpha software, and it produces real Bitcoin mainnet addresses. It has not
been independently audited. The certifier is designed to be fail-closed and proves
each leaf against your source, but "proven" means proven by this compiler: a bug in
it, or a contract that does not mean what you intended, can lock your coins
permanently. Bitcoin transactions are irreversible and there is no recourse.

Never fund an address from Seal unless you are prepared to lose those funds
entirely. Read the compiled script (`--script`) and the certification output
yourself before you send anything.

## License

MIT. See [LICENSE](LICENSE).

---

<p align="center"><sub>The seal is <b>Selkie</b>, a nod to the seal-folk of folklore who slip out of their skins to walk ashore.</sub></p>
