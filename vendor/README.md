# Vendored references

## `bitcoin/`: Bitcoin Core (git submodule)

The official Bitcoin Core source, tracked as a git submodule of
`https://github.com/bitcoin/bitcoin`, pinned to a release tag (currently
**v31.0**). It is the reference implementation for **Phase 4** of the
verification program: the faithful check that our in-house interpreter matches
the consensus rules a real node enforces (the consensus differential tests).

This is a verification/test dependency only. It is **not** linked into the
compiler, which stays zero-dependency; nothing under `src/` references it.

### Fetch it after cloning this repo

```
git submodule update --init --depth 1 vendor/bitcoin
```

### Update to a newer official release

```
git -C vendor/bitcoin fetch --depth 1 origin tag vXX.Y
git -C vendor/bitcoin checkout vXX.Y
git add vendor/bitcoin && git commit -m "vendor: bump Bitcoin Core to vXX.Y"
```

Pinning to a release tag (not a moving branch) keeps the consensus reference
reproducible; bumps are deliberate.

### Role in Phase 4: and how to run the differential

Two differentials validate our interpreter against Core:

- `tests/core_differential.rs`, our interpreter vs Core's vendored
  `script_tests.json` corpus. Runs with no build (the corpus is checked in).
- `tests/core_consensus_differential.rs`, OUR generated tapscript leaves +
  witnesses run through Core's REAL interpreter (`tests/core_eval.cpp`, a
  harness over Core's `EvalScript` under `SigVersion::TAPSCRIPT` with a mock
  signature checker). This one needs Core built:

```
# build Core's consensus engine (once; ~30 min cold, ccache speeds rebuilds)
cmake -S vendor/bitcoin -B /tmp/bitcoin-build -DENABLE_WALLET=OFF -DENABLE_IPC=OFF
cmake --build /tmp/bitcoin-build --target bitcoind -j"$(sysctl -n hw.ncpu 2>/dev/null || nproc)"

# run the differential against it
BITCOIN_BUILD=/tmp/bitcoin-build cargo test --test core_consensus_differential -- --nocapture
```

Without `BITCOIN_BUILD` (and no `vendor/bitcoin/build`), that test SKIPS and
passes, so the suite is green on machines without Core.

- `tests/regtest_differential.rs` -- the GOLD STANDARD: real taproot spends
  through a live `bitcoind` regtest node (`testmempoolaccept`), closing T3
  (taproot commitment), T5 (real BIP340 signature over the BIP341 sighash), and
  T4 (tapscript under real consensus) at once. Same gate:
  `BITCOIN_BUILD=/tmp/bitcoin-build cargo test --test regtest_differential --
  --nocapture`. It starts and stops its own regtest node, mining the coinbase
  straight to the contract address (no wallet). Covers both BIP341 spend shapes:
  script-path leaves (single-sig, quorum's CSE leaf, all four timelock forms,
  and the htlc/vault corpus trees spent leaf-by-leaf with real hashlocks) AND a
  key-path spend (single signature under the tweaked output key).

Between them: differential (2) isolates execution (T4) from crypto (T5) with a
mock checker and exhaustively covers timelock-free leaves; differential (3)
exercises the full stack (T3 + T4 + T5) end to end on a real node, across
script-path and key-path spends and all four timelock forms.
