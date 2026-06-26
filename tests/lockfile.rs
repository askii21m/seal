//! The lockfile gate: the committed corpus lockfiles are the verify-mode
//! regression alarm. Any compiler change that alters emitted bytes, layout,
//! costs, or addresses fails this suite loudly and must be a deliberate,
//! documented decision (an output-changing change is a compiler version
//! change by definition).

use seal::analysis::consteval::{bind_args, instantiate};
use seal::analysis::intervals;
use seal::analysis::paths;
use seal::analysis::sema;
use seal::codegen::lower;
use seal::codegen::optimize;
use seal::diagnostics::Severity;
use seal::json;
use seal::output::bech32m;
use seal::output::lockfile;
use seal::output::taproot;
use seal::syntax::parser;

/// The full pipeline, mirroring the driver; returns the rendered lockfile.
fn build_lock(name: &str, args_override: Option<&str>) -> String {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
    let src = std::fs::read_to_string(dir.join(format!("{name}.sl"))).expect("source");
    let args_src = match args_override {
        Some(s) => s.to_string(),
        None => std::fs::read_to_string(dir.join(format!("{name}.args.json"))).expect("args"),
    };
    let (contract, pd) = parser::parse_source(&src);
    assert!(pd.is_empty(), "{pd:#?}");
    let c = contract.expect("contract");
    let (sd, info) = sema::analyze(&c);
    assert!(sd.is_empty(), "{sd:#?}");
    let mut env = bind_args(&info, &json::parse(&args_src).expect("json")).expect("bind");
    let inst = instantiate(&c, &mut env);
    assert!(
        inst.iter().all(|d| d.severity != Severity::Error),
        "{inst:#?}"
    );
    let (g1, report) = intervals::analyze(&c, &env);
    assert!(g1.is_empty(), "{g1:#?}");
    let (pdiags, _) = paths::analyze(&c, &info, &env);
    assert!(
        pdiags.iter().all(|d| d.severity != Severity::Error),
        "{pdiags:#?}"
    );
    let (ldiags, leaves) = lower::lower(&c, &info, &env, &report);
    // Warnings (e.g. opt/dead-witness) are fine; only errors block lowering.
    assert!(
        ldiags.iter().all(|d| d.severity != Severity::Error),
        "{ldiags:#?}"
    );
    let leaves: Vec<_> = leaves.iter().map(optimize::optimize).collect();
    let out = taproot::assemble_contract(&c, &env, &leaves).expect("assemble");
    let address = bech32m::encode_p2tr("bc", &out.assembled.output_key);
    lockfile::render(&src, &args_src, &info, &env, &leaves, &out, &address)
}

/// Every example must carry a committed lockfile that the rebuild reproduces
/// exactly. The corpus is DISCOVERED from the `.sl` files on disk, not a
/// hardcoded list: a new contract added without a committed lock fails this
/// gate instead of silently escaping it (which is how `cat_bounty.lock` once
/// went stale for three commits, and how `quorum`/`mirage` had no lock at all).
#[test]
fn corpus_lockfiles_verify() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
    let mut names: Vec<String> = std::fs::read_dir(&dir)
        .expect("corpus dir")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|x| x.to_str()) == Some("sl"))
        .filter_map(|p| p.file_stem().and_then(|s| s.to_str()).map(str::to_owned))
        .collect();
    names.sort();
    assert!(
        !names.is_empty(),
        "no example .sl files found in {}",
        dir.display()
    );

    for name in &names {
        let lock_path = dir.join(format!("{name}.lock"));
        let committed = std::fs::read_to_string(&lock_path).unwrap_or_else(|e| {
            panic!(
                "{name}: no committed lockfile at {} -- every example must have one. \
                 Generate it with `seal tests/corpus/{name}.sl --args tests/corpus/{name}.args.json --lock` \
                 (add --allow-unproven only if a leaf is not proven): {e}",
                lock_path.display()
            )
        });
        let rebuilt = build_lock(name, None);
        assert_eq!(
            rebuilt, committed,
            "{name}: the rebuild does not reproduce the committed lockfile, \
             if this change is deliberate, regenerate with `seal --lock` and \
             document why in the commit"
        );
    }
}

#[test]
fn render_is_deterministic() {
    assert_eq!(build_lock("htlc", None), build_lock("htlc", None));
}

#[test]
fn lockfile_pins_the_arguments() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
    let args = std::fs::read_to_string(dir.join("htlc.args.json")).unwrap();
    let mutated = args.replace("900000", "900001");
    assert_ne!(args, mutated, "fixture sanity");
    let a = build_lock("htlc", Some(&args));
    let b = build_lock("htlc", Some(&mutated));
    assert_ne!(a, b, "different args must produce different lockfiles");
    // And the difference is visible in both the args hash and the value.
    assert!(b.contains("height 900001"));
}
