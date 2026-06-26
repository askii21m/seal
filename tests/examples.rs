//! The user-facing `examples/` directory mirrors a curated subset of the tested
//! corpus (`tests/corpus/`). These tests discover every contract in `examples/`
//! from disk and pin two invariants for each: it stays byte-identical to its
//! corpus counterpart, so the showcase cannot silently drift from what the suite
//! actually exercises, and it compiles to a fundable mainnet address whose
//! committed lockfile reproduces exactly. Discovering from disk means a contract
//! dropped into `examples/` is gated automatically, with no list to keep in sync.

use seal::compile::{CompileOptions, Target, compile};

fn manifest() -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn read(dir: &str, file: &str) -> String {
    std::fs::read_to_string(manifest().join(dir).join(file))
        .unwrap_or_else(|e| panic!("read {dir}/{file}: {e}"))
}

/// Every contract stem in `examples/` (its `*.sl` files), sorted for determinism.
fn example_stems() -> Vec<String> {
    let mut stems: Vec<String> = std::fs::read_dir(manifest().join("examples"))
        .unwrap_or_else(|e| panic!("read_dir examples/: {e}"))
        .filter_map(|entry| {
            let name = entry.ok()?.file_name().to_string_lossy().into_owned();
            name.strip_suffix(".sl").map(String::from)
        })
        .collect();
    stems.sort();
    assert!(!stems.is_empty(), "examples/ has no .sl contracts");
    stems
}

#[test]
fn examples_match_the_tested_corpus() {
    for name in example_stems() {
        for ext in ["sl", "args.json", "lock"] {
            let file = format!("{name}.{ext}");
            assert_eq!(
                read("examples", &file),
                read("tests/corpus", &file),
                "examples/{file} has drifted from tests/corpus/{file}; \
                 every example must be a byte-identical copy of a tested corpus contract"
            );
        }
    }
}

#[test]
fn examples_compile_to_a_fundable_address_and_reproduce_their_lockfile() {
    for name in example_stems() {
        let src = read("examples", &format!("{name}.sl"));
        let args = read("examples", &format!("{name}.args.json"));
        let result = compile(&src, Some(&args), Target::Fund, CompileOptions::default());

        let gate = result
            .gate
            .as_ref()
            .unwrap_or_else(|| panic!("examples/{name}.sl: no funding gate ran"));
        assert!(gate.may_proceed, "examples/{name}.sl: gate refused funding");

        let assembled = result
            .assembled
            .as_ref()
            .unwrap_or_else(|| panic!("examples/{name}.sl: no assembled output"));
        assert!(
            assembled.address.starts_with("bc1p"),
            "examples/{name}.sl: expected a mainnet p2tr address, got {}",
            assembled.address
        );
        assert_eq!(
            assembled.lockfile,
            read("examples", &format!("{name}.lock")),
            "examples/{name}.lock does not reproduce from examples/{name}.sl; \
             regenerate it with `seal examples/{name}.sl --args examples/{name}.args.json --lock`"
        );
    }
}
