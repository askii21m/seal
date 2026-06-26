//! Per-compile certification (T1 + T2): the independent predicate evaluator
//! must agree with both the naive and the optimized script over the COMPLETE
//! finite witness domain of every certifiable leaf. This also VALIDATES the
//! evaluator: its agreement with the heavily-tested corpus corroborates the
//! oracle before any disagreement elsewhere is read as a real defect.

use seal::analysis::consteval::{Env, bind_args, instantiate};
use seal::analysis::intervals;
use seal::analysis::paths;
use seal::analysis::sema;
use seal::analysis::sema::ContractInfo;
use seal::codegen::lower::{LoweredLeaf, lower};
use seal::codegen::optimize::optimize;
use seal::diagnostics::Severity;
use seal::json;
use seal::syntax::ast::Contract;
use seal::syntax::parser;
use seal::verify::certify::{CertStatus, LeafReport, certify};
use seal::verify::interp::Context;

const MARKER: [u8; 64] = [0xAA; 64];
const KEY: &str = "0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c";

fn pipeline(src: &str, args: &str) -> (Contract, ContractInfo, Env, Vec<LoweredLeaf>) {
    let (contract, pd) = parser::parse_source(src);
    assert!(pd.is_empty(), "parse: {pd:#?}");
    let c = contract.expect("contract");
    let (sd, info) = sema::analyze(&c);
    assert!(sd.is_empty(), "sema: {sd:#?}");
    let mut env = bind_args(&info, &json::parse(args).expect("json")).expect("bind");
    let id = instantiate(&c, &mut env);
    assert!(
        id.iter().all(|d| d.severity != Severity::Error),
        "instantiate: {id:#?}"
    );
    let (b, report) = intervals::analyze(&c, &env);
    assert!(b.is_empty(), "bounds: {b:#?}");
    let (pd2, _) = paths::analyze(&c, &info, &env);
    assert!(
        pd2.iter().all(|d| d.severity != Severity::Error),
        "paths: {pd2:#?}"
    );
    let (ld, leaves) = lower(&c, &info, &env, &report);
    assert!(
        ld.iter().all(|d| d.severity != Severity::Error),
        "lower: {ld:#?}"
    );
    (c, info, env, leaves)
}

fn load(name: &str) -> (Contract, ContractInfo, Env, Vec<LoweredLeaf>) {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
    let src = std::fs::read_to_string(dir.join(format!("{name}.sl"))).unwrap();
    let args = std::fs::read_to_string(dir.join(format!("{name}.args.json"))).unwrap();
    pipeline(&src, &args)
}

/// Certify a compiled contract with the marker signature oracle and a standard
/// (non-final-sequence) spend context.
fn reports(c: &Contract, info: &ContractInfo, env: &Env, naive: &[LoweredLeaf]) -> Vec<LeafReport> {
    let opt: Vec<LoweredLeaf> = naive.iter().map(optimize).collect();
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    certify(c, info, env, naive, &opt, &MARKER, &ctx)
}

fn status_of<'a>(rs: &'a [LeafReport], name: &str) -> &'a CertStatus {
    &rs.iter()
        .find(|r| r.name == name)
        .unwrap_or_else(|| panic!("no leaf `{name}`"))
        .status
}

fn assert_no_failures(rs: &[LeafReport], ctx: &str) {
    for r in rs {
        if let CertStatus::Failed { detail } = &r.status {
            panic!("[{ctx}] leaf `{}` FAILED certification: {detail}", r.name);
        }
    }
}

/// quorum: [Bool;8] + Signature = 512 witnesses. Must be exhaustively
/// CERTIFIED (T1 + T2) -- this both proves the CSE-optimized leaf correct for
/// every witness and validates the evaluator on a count/threshold predicate.
#[test]
fn quorum_is_exhaustively_certified() {
    let (c, info, env, naive) = load("quorum");
    let rs = reports(&c, &info, &env, &naive);
    assert_no_failures(&rs, "quorum");
    match status_of(&rs, "act") {
        CertStatus::Certified { checked } => assert_eq!(*checked, 512, "2^8 votes x 2 sig states"),
        other => panic!("quorum.act not certified: {other:?}"),
    }
}

/// multisig: a CHECKSIGADD threshold over a Signature array = a small finite
/// domain. Must be exhaustively certified.
#[test]
fn multisig_is_exhaustively_certified() {
    let (c, info, env, naive) = load("multisig");
    let rs = reports(&c, &info, &env, &naive);
    assert_no_failures(&rs, "multisig");
    // At least one leaf must reach full certification (not merely differential
    // / unbounded), proving the evaluator handles the threshold predicate.
    assert!(
        rs.iter()
            .any(|r| matches!(r.status, CertStatus::Certified { .. })),
        "no multisig leaf was exhaustively certified: {rs:#?}"
    );
}

/// The whole corpus must contain ZERO certification failures: every finite
/// leaf that the evaluator can speak about agrees three ways, and every other
/// leaf at least holds the optimizer differential (T2) or is honestly
/// reported unbounded. Nothing silently ships a divergence.
#[test]
fn corpus_has_no_certification_failures() {
    for name in [
        "vault",
        "htlc",
        "multisig",
        "cat_bounty",
        "mirage",
        "quorum",
    ] {
        let (c, info, env, naive) = load(name);
        let rs = reports(&c, &info, &env, &naive);
        assert_no_failures(&rs, name);
    }
}

/// A `sum` threshold over a bool array is certified, exercising the evaluator's
/// sum aggregate and confirming both bounds are enforced for every witness.
#[test]
fn sum_threshold_is_certified() {
    let src = "contract T { extern const k: PublicKey;
        spend f(relaxed flags: [Bool; 6], s: Signature) {
            require { sum(b in flags where b => 1) >= 2, sum(b in flags where b => 1) <= 4, k.check(s) }
        } keypath None; }";
    let args = format!(r#"{{"k": "{KEY}"}}"#);
    let (c, info, env, naive) = pipeline(src, &args);
    let rs = reports(&c, &info, &env, &naive);
    assert_no_failures(&rs, "sum");
    assert!(matches!(status_of(&rs, "f"), CertStatus::Certified { checked } if *checked == 128));
}

/// `all` and `any` predicates are certified (the evaluator's all/any
/// aggregates), over a 4-bool + sig domain.
#[test]
fn all_any_predicates_are_certified() {
    for agg in ["all", "any"] {
        let src = format!(
            "contract T {{ extern const k: PublicKey;
                spend f(relaxed flags: [Bool; 4], s: Signature) {{
                    require {{ {agg}(b in flags => b), k.check(s) }}
                }} keypath None; }}"
        );
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        let (c, info, env, naive) = pipeline(&src, &args);
        let rs = reports(&c, &info, &env, &naive);
        assert_no_failures(&rs, agg);
        assert!(
            matches!(status_of(&rs, "f"), CertStatus::Certified { .. }),
            "{agg} predicate not certified: {rs:#?}"
        );
    }
}

/// The CSE three-item run (`>= 3, <= 6, != 4`) is exhaustively certified:
/// every one of the 512 witnesses agrees three ways, which proves the shared
/// tally and the kept `!= 4` bound correct for all inputs -- the strongest
/// possible statement of the earlier CSE work.
#[test]
fn cse_three_item_run_is_exhaustively_certified() {
    let src = "contract T { extern const k: PublicKey;
        spend f(relaxed votes: [Bool; 8], s: Signature) {
            require {
                count(v in votes where v => true) >= 3,
                count(v in votes where v => true) <= 6,
                count(v in votes where v => true) != 4,
                k.check(s)
            }
        } keypath None; }";
    let args = format!(r#"{{"k": "{KEY}"}}"#);
    let (c, info, env, naive) = pipeline(src, &args);
    let rs = reports(&c, &info, &env, &naive);
    assert_no_failures(&rs, "cse3");
    assert!(matches!(status_of(&rs, "f"), CertStatus::Certified { checked } if *checked == 512));
}

/// Bounded-Int: a range-constrained Int contract (mirage) is BoundedChecked
/// over a window covering its constants. The three-way check still holds for
/// every bid in the window -- so the dead-constraint-eliminated leaf agrees
/// with the predicate and the naive leaf (including rejecting the out-of-range
/// boundary). Before Phase 3 this leaf was only BoundedChecked (a window); the
/// single-Int symbolic engine (`crate::verify::decide`, Engine A) now PROVES it over
/// every CScriptNum value of `bid`. The full-domain validation of this verdict
/// lives in `tests/decide.rs`.
#[test]
fn mirage_int_is_proven_full_domain() {
    use seal::verify::certify::ProvenKind;
    let (c, info, env, naive) = load("mirage");
    let rs = reports(&c, &info, &env, &naive);
    assert_no_failures(&rs, "mirage");
    match status_of(&rs, "claim") {
        CertStatus::Proven {
            kind: ProvenKind::FullInt { var, .. },
        } => assert_eq!(var, "bid"),
        other => panic!("mirage.claim should be Proven(FullInt), got {other:?}"),
    }
}

/// cat_bounty's weighted-sum leaf is PROVEN over the full symbolic domain
/// (Engine B), and its 37 zero-weight pixels are eliminated -- so the proof is
/// over the REDUCED 748-atom witness, not the declared 784 + sig = 785. A silent
/// drop to T2-only (an `Add` commutativity mismatch) regressed this once; this
/// pins both the full-domain proof AND the dead-witness reduction.
#[test]
fn cat_bounty_is_proven_full_symbolic_over_reduced_witness() {
    use seal::verify::certify::ProvenKind;
    let (c, info, env, naive) = load("cat_bounty");
    let rs = reports(&c, &info, &env, &naive);
    assert_no_failures(&rs, "cat_bounty");
    match status_of(&rs, "claim") {
        CertStatus::Proven {
            kind: ProvenKind::FullSymbolic { atoms },
        } => {
            assert_eq!(*atoms, 748, "784 pixels - 37 dead + 1 signature = 748");
        }
        other => panic!("cat_bounty.claim should be Proven(FullSymbolic over 748), got {other:?}"),
    }
}

/// Teeth: a certifier that never reports Failed is worthless. Pair contract
/// A's predicate (`count >= 3`) and its naive leaf with a DIFFERENT contract's
/// leaf (`count >= 4`) as the "optimized" output -- a planted divergence. The
/// certifier MUST catch it (at exactly count == 3, where the two disagree).
#[test]
fn certifier_detects_a_planted_divergence() {
    let mk = |t: i64| {
        format!(
            "contract T {{ extern const k: PublicKey;
                spend f(relaxed flags: [Bool; 6], s: Signature) {{
                    require {{ count(b in flags where b => true) >= {t}, k.check(s) }}
                }} keypath None; }}"
        )
    };
    let args = format!(r#"{{"k": "{KEY}"}}"#);
    let (ca, ia, ea, na) = pipeline(&mk(3), &args);
    let (_cb, _ib, _eb, nb) = pipeline(&mk(4), &args);
    let optb: Vec<LoweredLeaf> = nb.iter().map(optimize).collect(); // the >= 4 leaf
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    let rs = certify(&ca, &ia, &ea, &na, &optb, &MARKER, &ctx);
    assert!(
        rs.iter()
            .any(|r| matches!(r.status, CertStatus::Failed { .. })),
        "certifier failed to catch a planted >=3 vs >=4 divergence: {rs:#?}"
    );
}

/// Timelock leaves: `after(..)` paths are now proven over BOUNDARY contexts
/// (just-satisfying + just-violating) rather than abstaining, so they reach a
/// fund-safe verdict. htlc.refund (absolute/CLTV) and both vault leaves
/// (relative/CSV) must be exhaustively Certified. `checked` is the WITNESS
/// domain (2 sig states) -- the boundary contexts are a proof mechanism, not
/// extra witnesses.
#[test]
fn timelock_leaves_are_certified() {
    let (c, info, env, naive) = load("htlc");
    let rs = reports(&c, &info, &env, &naive);
    assert_no_failures(&rs, "htlc");
    assert!(
        matches!(status_of(&rs, "refund"), CertStatus::Certified { checked } if *checked == 2),
        "htlc.refund should be Certified over its 2 sig states, got {:?}",
        status_of(&rs, "refund")
    );

    let (c, info, env, naive) = load("vault");
    let rs = reports(&c, &info, &env, &naive);
    assert_no_failures(&rs, "vault");
    for leaf in ["fallback", "recover"] {
        assert!(
            matches!(status_of(&rs, leaf), CertStatus::Certified { checked } if *checked == 2),
            "vault.{leaf} should be Certified over its 2 sig states, got {:?}",
            status_of(&rs, leaf)
        );
    }
}

/// Teeth for the timelock proof: a lowering/optimizer that DROPPED the timelock
/// must be caught. The just-satisfying context alone cannot see it (with the
/// lock met, a present and an absent timelock behave identically); the
/// just-VIOLATING boundary context is what exposes it -- there the real script
/// rejects but the timelock-less one still accepts a valid signature. Pair the
/// real (with-timelock) predicate + naive leaf with a timelock-LESS leaf as the
/// "optimized" output; the certifier MUST report Failed.
#[test]
fn certifier_catches_a_dropped_timelock() {
    let with_tl = "contract T { extern const k: PublicKey;
        spend f(s: Signature) {
            require { after(LockTime.Relative(blocks: 10)), k.check(s) }
        } keypath None; }";
    let without_tl = "contract T { extern const k: PublicKey;
        spend f(s: Signature) {
            require { k.check(s) }
        } keypath None; }";
    let args = format!(r#"{{"k": "{KEY}"}}"#);
    let (ca, ia, ea, na) = pipeline(with_tl, &args); // real contract + naive (has CSV)
    let (_cb, _ib, _eb, nb) = pipeline(without_tl, &args);
    let opt_dropped: Vec<LoweredLeaf> = nb.iter().map(optimize).collect(); // CSV stripped
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    let rs = certify(&ca, &ia, &ea, &na, &opt_dropped, &MARKER, &ctx);
    assert!(
        rs.iter()
            .any(|r| matches!(r.status, CertStatus::Failed { .. })),
        "certifier failed to catch a dropped timelock (the violating context has no teeth): {rs:#?}"
    );
}
