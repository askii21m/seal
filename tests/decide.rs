//! Validation of the Phase 3 symbolic decision procedure (`src/decide.rs`,
//! Engine A: single Int witness variable). A `Proven` verdict claims
//! equivalence over the ENTIRE machine domain, so a wrong one is the single
//! unacceptable outcome. These tests pin both directions against an independent
//! brute force:
//!
//!   - **Proven => actually equivalent (and correct).** For every leaf Engine A
//!     proves, re-execute naive and optimized over a wide range that EXTENDS
//!     past the BoundedChecked window into the tail, and confirm they agree at
//!     every point AND match the contract's intended accept-set.
//!   - **Tail divergence is caught.** A leaf whose optimized script agrees on the
//!     whole enumeration window but diverges only in the TAIL must NOT be Proven
//!     -- exactly the case a window-only (BoundedChecked) check would wave
//!     through. This is Engine A's reason to exist; it is checked head-on.

use seal::analysis::consteval::{Env, bind_args, instantiate};
use seal::analysis::intervals;
use seal::analysis::paths;
use seal::analysis::sema;
use seal::analysis::sema::{ContractInfo, SpendSig};
use seal::codegen::lower::{LoweredLeaf, lower};
use seal::codegen::optimize::optimize;
use seal::diagnostics::Severity;
use seal::json;
use seal::syntax::ast::Contract;
use seal::syntax::parser;
use seal::verify::certify::{CertStatus, LeafReport, ProvenKind, certify};
use seal::verify::interp::{Context, execute};
use seal::verify::satisfy::{SatValue, build_witness};

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

fn run_certify(
    c: &Contract,
    info: &ContractInfo,
    env: &Env,
    naive: &[LoweredLeaf],
    opt: &[LoweredLeaf],
) -> Vec<LeafReport> {
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    certify(c, info, env, naive, opt, &MARKER, &ctx)
}

fn status<'a>(rs: &'a [LeafReport], name: &str) -> &'a CertStatus {
    &rs.iter().find(|r| r.name == name).expect("leaf").status
}

/// Execute one leaf at a concrete (Int, sig-present) witness; true == accepted.
fn accepts(
    leaf: &LoweredLeaf,
    sig: &SpendSig,
    env: &Env,
    intname: &str,
    x: i64,
    present: bool,
) -> bool {
    let plan = vec![
        (intname.to_string(), SatValue::Int(x)),
        ("s".to_string(), SatValue::Sig(present)),
    ];
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    let stack = build_witness(leaf, sig, env, &plan, &MARKER).expect("witness");
    execute(&leaf.script, &stack, &ctx).is_ok()
}

#[test]
fn mirage_claim_is_proven_full_int() {
    let (c, info, env, naive) = load("mirage");
    let opt: Vec<LoweredLeaf> = naive.iter().map(optimize).collect();
    let rs = run_certify(&c, &info, &env, &naive, &opt);
    match status(&rs, "claim") {
        CertStatus::Proven {
            kind: ProvenKind::FullInt { var, breakpoints },
        } => {
            assert_eq!(var, "bid");
            assert!(*breakpoints > 0);
        }
        other => panic!("mirage.claim should be Proven(FullInt), got {other:?}"),
    }
}

/// The teeth: a Proven leaf is equivalent AND semantically correct over a range
/// that extends WELL PAST the BoundedChecked window (which was [-20002, 20002]),
/// so the tail Engine A proved structurally is confirmed by execution.
#[test]
fn proven_mirage_matches_brute_force_including_the_tail() {
    let (c, info, env, naive) = load("mirage");
    let opt: Vec<LoweredLeaf> = naive.iter().map(optimize).collect();
    // sanity: it really is Proven (else this test would be vacuous)
    let rs = run_certify(&c, &info, &env, &naive, &opt);
    assert!(matches!(status(&rs, "claim"), CertStatus::Proven { .. }));

    let nl = naive.iter().find(|l| l.name == "claim").unwrap();
    let ol = opt.iter().find(|l| l.name == "claim").unwrap();
    let sig = info.spends.iter().find(|s| s.name == "claim").unwrap();

    for present in [false, true] {
        for x in -25_000i64..=25_000 {
            let nok = accepts(nl, sig, &env, "bid", x, present);
            let ook = accepts(ol, sig, &env, "bid", x, present);
            assert_eq!(
                nok, ook,
                "T2: naive vs opt diverge at bid={x} present={present}"
            );
            // mirage accepts iff a valid signature AND bid in [0, 1000).
            let expected = present && (0..1000).contains(&x);
            assert_eq!(
                ook, expected,
                "accept-set wrong at bid={x} present={present}"
            );
        }
    }
}

/// Engine A's reason to exist: catch a divergence the window misses. `narrow`
/// accepts x in [0,10); `wide` accepts that OR x==1000 (a sanctioned widened-
/// arithmetic disjunction, no OP_IF). They agree on the whole window [-24,24]
/// but differ at x=1000. Feeding `wide`'s leaf as the (buggy) optimizer output
/// for `narrow`'s source must NOT be Proven.
#[test]
fn tail_only_divergence_is_caught_not_proven() {
    let narrow_src = "contract N { extern const k: PublicKey;
            spend claim(relaxed x: Int, s: Signature) { require { x in 0..10, k.check(s) } }
            keypath None; }";
    let wide_src = "contract N { extern const k: PublicKey;
            spend claim(relaxed x: Int, s: Signature) { require { (x in 0..10) + (x == 1000) >= 1, k.check(s) } }
            keypath None; }";
    let args = format!("{{\"k\":\"{KEY}\"}}");
    let (c, info, env, naive) = pipeline(narrow_src, &args);
    let (_cw, _iw, _ew, wide) = pipeline(wide_src, &args);
    let buggy_opt: Vec<LoweredLeaf> = wide.iter().map(optimize).collect();

    let nl = naive.iter().find(|l| l.name == "claim").unwrap();
    let bl = buggy_opt.iter().find(|l| l.name == "claim").unwrap();
    let sig = info.spends.iter().find(|s| s.name == "claim").unwrap();

    // The window-sized region agrees (so a window-only check would pass)...
    for x in -24i64..=24 {
        assert_eq!(
            accepts(nl, sig, &env, "x", x, true),
            accepts(bl, sig, &env, "x", x, true),
            "narrow and wide should agree on the window at x={x}"
        );
    }
    // ...but they diverge at x=1000, in the tail.
    assert_ne!(
        accepts(nl, sig, &env, "x", 1000, true),
        accepts(bl, sig, &env, "x", 1000, true),
        "narrow and wide must diverge at x=1000"
    );

    // Certifying narrow's source with the buggy (wide) optimizer output must not
    // claim Proven -- Engine A samples the breakpoint at 1000 and refuses.
    let rs = run_certify(&c, &info, &env, &naive, &buggy_opt);
    assert!(
        !matches!(status(&rs, "claim"), CertStatus::Proven { .. }),
        "a tail divergence was wrongly Proven: {:?}",
        status(&rs, "claim")
    );
}

/// The tail-catch at SCALE: divergences near the machine extremes (x == 2e9,
/// just under M; and x == M/2) must also be caught, not just small tails. Engine
/// A collects the breakpoint from the buggy optimizer's own `== <big>` and
/// samples it. (Adapted from an audit probe.)
#[test]
fn tail_divergence_near_machine_max_is_not_proven() {
    let narrow = "contract N { extern const k: PublicKey;
        spend claim(relaxed x: Int, s: Signature) { require { x in 0..10, k.check(s) } }
        keypath None; }";
    let args = format!("{{\"k\":\"{KEY}\"}}");
    // Each buggy source agrees with `narrow` on the window but accepts one extra
    // far-tail point (via the sanctioned widened-arithmetic disjunction).
    let buggy_srcs = [
        ("contract N { extern const k: PublicKey;
            spend claim(relaxed x: Int, s: Signature) { require { (x in 0..10) + (x == 2000000000) >= 1, k.check(s) } }
            keypath None; }", 2_000_000_000i64),
        ("contract N { extern const k: PublicKey;
            spend claim(relaxed x: Int, s: Signature) { require { (x in 0..10) + (x == 1073741823) >= 1, k.check(s) } }
            keypath None; }", 1_073_741_823i64),
    ];
    let (c, info, env, naive) = pipeline(narrow, &args);
    let sig = info.spends.iter().find(|s| s.name == "claim").unwrap();
    let nl = naive.iter().find(|l| l.name == "claim").unwrap();
    for (bsrc, dx) in buggy_srcs {
        let (_cw, _iw, _ew, wide) = pipeline(bsrc, &args);
        let buggy: Vec<LoweredLeaf> = wide.iter().map(optimize).collect();
        let bl = buggy.iter().find(|l| l.name == "claim").unwrap();
        assert_ne!(
            accepts(nl, sig, &env, "x", dx, true),
            accepts(bl, sig, &env, "x", dx, true),
            "narrow and buggy must diverge at x={dx}"
        );
        let rs = run_certify(&c, &info, &env, &naive, &buggy);
        assert!(
            !matches!(status(&rs, "claim"), CertStatus::Proven { .. }),
            "tail divergence at x={dx} wrongly Proven: {:?}",
            status(&rs, "claim")
        );
    }
}

/// `check(s)` appearing in ARITHMETIC (widened to 0/1) is sound: in a slice that
/// DECLINES the signature, check is really 0, shifting a comparison's breakpoint
/// versus the `pred_pwa` model (which treats check as 1). Soundness holds because
/// the SCRIPT breakpoints are collected with the concrete per-slice check value,
/// so the true breakpoint is in the cover. We confirm by brute force that
/// whatever verdict is reached, naive == opt over a wide range in BOTH sig
/// states. (Closes an audit probe's hypothesis.)
#[test]
fn check_in_arithmetic_declined_slice_is_sound() {
    // `x` is bounded so `x + check` stays within M (else the interval engine
    // rejects the contract). With s present, check=1 -> breakpoint x >= 149;
    // with s declined, the trailing `k.check(s)` is false so the leaf rejects
    // everywhere -- a different breakpoint structure per slice.
    let src = "contract A { extern const k: PublicKey;
        spend claim(relaxed x: Int, s: Signature) {
            require { x in 0..200, (x + k.check(s)) >= 150, k.check(s) }
        }
        keypath None; }";
    let args = format!("{{\"k\":\"{KEY}\"}}");
    let (c, info, env, naive) = pipeline(src, &args);
    let opt: Vec<LoweredLeaf> = naive.iter().map(optimize).collect();
    // Whatever the verdict, it must be sound: re-execute over a range that
    // brackets the check=1 breakpoint (149) and the upper bound (200).
    let _ = run_certify(&c, &info, &env, &naive, &opt);
    let nl = naive.iter().find(|l| l.name == "claim").unwrap();
    let ol = opt.iter().find(|l| l.name == "claim").unwrap();
    let sig = info.spends.iter().find(|s| s.name == "claim").unwrap();
    for present in [false, true] {
        for x in -50i64..=300 {
            assert_eq!(
                accepts(nl, sig, &env, "x", x, present),
                accepts(ol, sig, &env, "x", x, present),
                "T2 diverge at x={x} present={present}"
            );
        }
    }
}

/// A second single-Int shape -- min/max/abs in the predicate -- proven, then
/// confirmed correct by brute force over the tail. Exercises the piecewise
/// (non-monotone) parts of the algebra, not just `within`.
#[test]
fn minmax_abs_single_int_proven_and_correct() {
    let src = "contract M { extern const k: PublicKey;
            spend claim(relaxed x: Int, s: Signature) {
                require { x in -100..=100, max(x, -5) <= 50, abs(x) >= 0, k.check(s) }
            }
            keypath None; }";
    let args = format!("{{\"k\":\"{KEY}\"}}");
    let (c, info, env, naive) = pipeline(src, &args);
    let opt: Vec<LoweredLeaf> = naive.iter().map(optimize).collect();
    let rs = run_certify(&c, &info, &env, &naive, &opt);
    assert!(
        matches!(status(&rs, "claim"), CertStatus::Proven { .. }),
        "min/max/abs leaf should be Proven, got {:?}",
        status(&rs, "claim")
    );

    let nl = naive.iter().find(|l| l.name == "claim").unwrap();
    let ol = opt.iter().find(|l| l.name == "claim").unwrap();
    let sig = info.spends.iter().find(|s| s.name == "claim").unwrap();
    for present in [false, true] {
        for x in -1000i64..=1000 {
            let nok = accepts(nl, sig, &env, "x", x, present);
            let ook = accepts(ol, sig, &env, "x", x, present);
            assert_eq!(nok, ook, "T2 at x={x} present={present}");
            // x in [-100,100] (inclusive) AND max(x,-5) <= 50 (i.e. x <= 50) AND
            // abs(x) >= 0 (always). So accept iff present AND -100 <= x <= 50.
            let expected = present && (-100..=50).contains(&x);
            assert_eq!(ook, expected, "accept-set wrong at x={x} present={present}");
        }
    }
}

// --- Engine B (structural symbolic equality; no Int var) ---

const CLASSIFIER_SRC: &str = "contract C {
    extern const weights: [Int; 26]; extern const bias: Int;
    extern const threshold: Int; extern const solver: PublicKey;
    spend claim(relaxed drawing: [Bool; 26], signature: Signature) {
        let score = bias + sum(px in drawing, w in weights where px => w);
        require { score > threshold, solver.check(signature) }
    }
    keypath None; }";

fn classifier_args(weights: &[i64], bias: i64, threshold: i64) -> String {
    let ws: Vec<String> = weights.iter().map(|w| w.to_string()).collect();
    format!(
        "{{\"weights\":[{}],\"bias\":{bias},\"threshold\":{threshold},\"solver\":\"{KEY}\"}}",
        ws.join(",")
    )
}

fn accepts_classifier(
    leaf: &LoweredLeaf,
    sig: &SpendSig,
    env: &Env,
    pixels: &[bool],
    present: bool,
) -> bool {
    let plan = vec![
        (
            "drawing".to_string(),
            SatValue::Array(pixels.iter().map(|&b| SatValue::Bool(b)).collect()),
        ),
        ("signature".to_string(), SatValue::Sig(present)),
    ];
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    let stack = build_witness(leaf, sig, env, &plan, &MARKER).expect("witness");
    execute(&leaf.script, &stack, &ctx).is_ok()
}

/// Deterministic pseudo-random pixel pattern for trial `t` (no `rand`).
fn pixels_for(t: u64, n: usize) -> Vec<bool> {
    let mut x = t.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1);
    (0..n)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x & 1 == 0
        })
        .collect()
}

#[test]
fn cat_bounty_is_proven_full_symbolic() {
    let (c, info, env, naive) = load("cat_bounty");
    let opt: Vec<LoweredLeaf> = naive.iter().map(optimize).collect();
    let rs = run_certify(&c, &info, &env, &naive, &opt);
    match status(&rs, "claim") {
        // Engine B proves BOTH T1 (the lowering implements the predicate) and T2
        // (the optimizer preserved it) over the reduced witness: 784 pixels - 37
        // dead (zero-weight, eliminated) + 1 signature = 748 free atoms.
        CertStatus::Proven {
            kind: ProvenKind::FullSymbolic { atoms },
        } => {
            assert_eq!(*atoms, 748, "784 pixels - 37 dead + 1 signature");
        }
        other => panic!("cat_bounty.claim should be Proven(FullSymbolic), got {other:?}"),
    }
}

/// A 26-pixel classifier (just over the enumeration cap, so it routes to Engine
/// B): proven FULL (T1+T2), then sampled brute-force confirms BOTH naive == opt
/// (T2) AND that the script accepts exactly the predicate's intended set --
/// `present AND (bias + sum of set-pixel weights) > threshold` (T1). A Proven
/// leaf that diverged on either would be caught here.
#[test]
fn classifier_proven_full_and_brute_force_clean() {
    let weights: Vec<i64> = (0..26).map(|i| [-3i64, 0, 2, 5, -1, 0, 4][i % 7]).collect();
    let (bias, threshold) = (1i64, 4i64);
    let args = classifier_args(&weights, bias, threshold);
    let (c, info, env, naive) = pipeline(CLASSIFIER_SRC, &args);
    let opt: Vec<LoweredLeaf> = naive.iter().map(optimize).collect();
    let rs = run_certify(&c, &info, &env, &naive, &opt);
    assert!(
        matches!(
            status(&rs, "claim"),
            CertStatus::Proven {
                kind: ProvenKind::FullSymbolic { .. }
            }
        ),
        "26-pixel classifier should be Proven(FullSymbolic), got {:?}",
        status(&rs, "claim")
    );
    let nl = naive.iter().find(|l| l.name == "claim").unwrap();
    let ol = opt.iter().find(|l| l.name == "claim").unwrap();
    let sig = info.spends.iter().find(|s| s.name == "claim").unwrap();
    for t in 0..3000u64 {
        let px = pixels_for(t, 26);
        for present in [false, true] {
            let nok = accepts_classifier(nl, sig, &env, &px, present);
            let ook = accepts_classifier(ol, sig, &env, &px, present);
            assert_eq!(nok, ook, "T2 diverged at trial {t} present={present}");
            // T1: the script's accept-set IS the predicate's intended set.
            let score: i64 = bias + (0..26).filter(|&i| px[i]).map(|i| weights[i]).sum::<i64>();
            let expected = present && score > threshold;
            assert_eq!(
                nok, expected,
                "T1: accept-set wrong at trial {t} present={present}"
            );
        }
    }
}

/// Teeth: feed the naive lowering of one classifier and the OPTIMIZED lowering
/// of a DIFFERENT one (different threshold) as the "optimizer output". They are
/// not equivalent, so Engine B must NOT prove it -- and a brute-force search
/// confirms a genuine divergence exists (the test is not vacuous).
#[test]
fn divergent_classifier_is_not_proven() {
    let weights: Vec<i64> = (0..26).map(|i| [5i64, 2, 0, 3, 1][i % 5]).collect();
    let (c, info, env, naive) = pipeline(CLASSIFIER_SRC, &classifier_args(&weights, 1, 4));
    let (_cb, _ib, _eb, nb) = pipeline(CLASSIFIER_SRC, &classifier_args(&weights, 1, 40));
    let buggy: Vec<LoweredLeaf> = nb.iter().map(optimize).collect();

    let rs = run_certify(&c, &info, &env, &naive, &buggy);
    assert!(
        !matches!(status(&rs, "claim"), CertStatus::Proven { .. }),
        "non-equivalent classifiers wrongly Proven: {:?}",
        status(&rs, "claim")
    );

    // Confirm a real divergence (threshold 4 vs 40): some assignment accepts
    // under one and rejects under the other.
    let nl = naive.iter().find(|l| l.name == "claim").unwrap();
    let bl = buggy.iter().find(|l| l.name == "claim").unwrap();
    let sig = info.spends.iter().find(|s| s.name == "claim").unwrap();
    let diverged = (0..5000u64).any(|t| {
        let px = pixels_for(t, 26);
        accepts_classifier(nl, sig, &env, &px, true) != accepts_classifier(bl, sig, &env, &px, true)
    });
    assert!(
        diverged,
        "the two classifiers should differ somewhere (test would be vacuous)"
    );
}

/// T1 soundness: the script may be a correct optimization of its OWN lowering
/// (T2 holds) yet NOT implement the stated PREDICATE. We certify a contract
/// whose `body` (predicate) has weights W' but whose naive/optimized leaves were
/// lowered from a DIFFERENT-weight source W. T2 still holds (W's opt == W's
/// naive), but T1 must fail -- so the verdict is T2OnlySymbolic, NOT
/// FullSymbolic. This is the check that the predicate-side proof is real, not a
/// re-statement of the lowering.
#[test]
fn predicate_mismatch_is_not_full_symbolic() {
    let w_script: Vec<i64> = (0..26).map(|i| [3i64, 1, 0, 2, 5][i % 5]).collect();
    let w_pred: Vec<i64> = (0..26).map(|i| [3i64, 1, 0, 2, 6][i % 5]).collect(); // one weight differs
    // body/env from the PREDICATE source (W'); leaves from the SCRIPT source (W).
    let (c, info, env, _np) = pipeline(CLASSIFIER_SRC, &classifier_args(&w_pred, 1, 4));
    let (_cs, _is, _es, ns) = pipeline(CLASSIFIER_SRC, &classifier_args(&w_script, 1, 4));
    let opt: Vec<LoweredLeaf> = ns.iter().map(optimize).collect();
    let rs = run_certify(&c, &info, &env, &ns, &opt);
    match status(&rs, "claim") {
        CertStatus::Proven {
            kind: ProvenKind::FullSymbolic { .. },
        } => {
            panic!(
                "a lowering that does NOT implement the predicate was wrongly Proven FullSymbolic"
            );
        }
        // T2 holds (the W-script's opt == its naive); T1 correctly fails.
        CertStatus::Proven {
            kind: ProvenKind::T2OnlySymbolic { .. },
        } => {}
        other => panic!("expected T2OnlySymbolic, got {other:?}"),
    }
}

// --- Engine B over the hash / size / bytewise-equality fragment ---

#[test]
fn htlc_swap_hashlock_is_proven_full() {
    let (c, info, env, naive) = load("htlc");
    let opt: Vec<LoweredLeaf> = naive.iter().map(optimize).collect();
    let rs = run_certify(&c, &info, &env, &naive, &opt);
    // `require { sha256(preimage) == hashlock, swap_key.check(sig) }` with the
    // Bytes<32> size airlock: T1 (lowering implements it) and T2 both proven.
    assert!(
        matches!(
            status(&rs, "swap"),
            CertStatus::Proven {
                kind: ProvenKind::FullSymbolic { .. }
            }
        ),
        "htlc.swap should be Proven(FullSymbolic), got {:?}",
        status(&rs, "swap")
    );
}

const HASHLOCK_SRC_TMPL: &str = "contract H {
    extern const k: PublicKey; extern const hashlock: Bytes<32>;
    spend claim(preimage: Bytes<1>, signature: Signature) {
        require { HASHFN(preimage) == hashlock, k.check(signature) }
    }
    keypath None; }";

fn hashlock_args(hashlock_hex: &str) -> String {
    format!("{{\"k\":\"{KEY}\",\"hashlock\":\"0x{hashlock_hex}\"}}")
}

/// T1 soundness for the hash fragment: a script that hashes with HASH256 but a
/// predicate stated with SHA256 must NOT be FullSymbolic (the uninterpreted
/// Hash nodes carry the op, so different algorithms do not match). T2 still
/// holds (the HASH256 source's opt == its naive), so the verdict is
/// T2OnlySymbolic.
#[test]
fn hash_algorithm_mismatch_is_not_full() {
    let hl = "ab".repeat(32);
    let sha_src = HASHLOCK_SRC_TMPL.replace("HASHFN", "sha256");
    let h256_src = HASHLOCK_SRC_TMPL.replace("HASHFN", "hash256");
    // body/env from the SHA256 predicate; leaves from the HASH256 script.
    let (c, info, env, _np) = pipeline(&sha_src, &hashlock_args(&hl));
    let (_cs, _is, _es, ns) = pipeline(&h256_src, &hashlock_args(&hl));
    let opt: Vec<LoweredLeaf> = ns.iter().map(optimize).collect();
    let rs = run_certify(&c, &info, &env, &ns, &opt);
    assert!(
        !matches!(
            status(&rs, "claim"),
            CertStatus::Proven {
                kind: ProvenKind::FullSymbolic { .. }
            }
        ),
        "a sha256-vs-hash256 mismatch was wrongly Proven FullSymbolic: {:?}",
        status(&rs, "claim")
    );
}

/// Strong T1 validation: a Bytes<1> hashlock leaf (256-value preimage domain),
/// proven FullSymbolic, then brute-forced against the REAL SHA256 -- the script
/// accepts exactly `present AND sha256(preimage) == hashlock`. The hashlock is
/// the real hash of a chosen byte so the accept-set is non-empty.
#[test]
fn hashlock_full_symbolic_matches_real_sha256() {
    let target: u8 = 0x42;
    let hl = seal::crypto::sha256::sha256(&[target]);
    let hl_hex: String = hl.iter().map(|b| format!("{b:02x}")).collect();
    let src = HASHLOCK_SRC_TMPL.replace("HASHFN", "sha256");
    let (c, info, env, naive) = pipeline(&src, &hashlock_args(&hl_hex));
    let opt: Vec<LoweredLeaf> = naive.iter().map(optimize).collect();
    let rs = run_certify(&c, &info, &env, &naive, &opt);
    assert!(
        matches!(
            status(&rs, "claim"),
            CertStatus::Proven {
                kind: ProvenKind::FullSymbolic { .. }
            }
        ),
        "Bytes<1> hashlock should be Proven(FullSymbolic), got {:?}",
        status(&rs, "claim")
    );
    let nl = naive.iter().find(|l| l.name == "claim").unwrap();
    let sig = info.spends.iter().find(|s| s.name == "claim").unwrap();
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    for pv in 0u16..256 {
        for present in [false, true] {
            let plan = vec![
                ("preimage".to_string(), SatValue::Bytes(vec![pv as u8])),
                ("signature".to_string(), SatValue::Sig(present)),
            ];
            let stack = build_witness(nl, sig, &env, &plan, &MARKER).expect("witness");
            let got = execute(&nl.script, &stack, &ctx).is_ok();
            let expected = present && seal::crypto::sha256::sha256(&[pv as u8]) == hl;
            assert_eq!(
                got, expected,
                "hashlock accept-set wrong at preimage={pv} present={present}"
            );
        }
    }
}
