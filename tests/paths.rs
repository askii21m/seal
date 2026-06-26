//! Path-analysis tests: feasibility timelock checks, authorization
//! (canonical shapes, instantiated thresholds, pinned keys), and parameter
//! classes, plus the corpus, clean, with the expected templates.

use seal::analysis::consteval::{Env, bind_args, instantiate};
use seal::analysis::paths::{Class, PathReport, analyze};
use seal::analysis::sema;
use seal::json;
use seal::syntax::parser::parse_source;

fn run(src: &str, args: &str) -> (Vec<seal::diagnostics::Diagnostic>, PathReport) {
    let (contract, pd) = parse_source(src);
    assert!(pd.is_empty(), "parse: {pd:#?}");
    let c = contract.expect("contract");
    let (sd, info) = sema::analyze(&c);
    assert!(sd.is_empty(), "sema: {sd:#?}");
    let mut env: Env = bind_args(&info, &json::parse(args).expect("json"))
        .unwrap_or_else(|e| panic!("bind: {e:#?}"));
    let id = instantiate(&c, &mut env);
    assert!(id.is_empty(), "instantiate: {id:#?}");
    analyze(&c, &info, &env)
}

fn ok(src: &str, args: &str) -> PathReport {
    let (diags, report) = run(src, args);
    let errors: Vec<_> = diags
        .iter()
        .filter(|d| d.severity == seal::diagnostics::Severity::Error)
        .collect();
    assert!(errors.is_empty(), "expected clean paths, got: {errors:#?}");
    report
}

fn codes(src: &str, args: &str) -> Vec<&'static str> {
    let (diags, _) = run(src, args);
    assert!(!diags.is_empty(), "expected path diagnostics");
    diags.iter().map(|d| d.code).collect()
}

const KEY: &str = "\"0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c\"";

// --- authorization ---

#[test]
fn sigless_spend_is_theft() {
    let cs = codes(
        "contract T {
            extern const h: Hash<Sha256>;
            spend f(p: Bytes<32>) { require sha256(p) == h; }
            keypath None;
        }",
        &format!(r#"{{"h": {}}}"#, KEY.replace("11", "ab")),
    );
    assert!(cs.contains(&"auth/theft"), "{cs:?}");
}

#[test]
fn open_concedes_theft() {
    ok(
        "contract T {
            extern const h: Hash<Sha256>;
            open spend f(p: Bytes<32>) { require sha256(p) == h; }
            keypath None;
        }",
        &format!(r#"{{"h": {}}}"#, KEY.replace("11", "ab")),
    );
}

#[test]
fn array_literal_witness_binder_is_rejected_by_sema() {
    // Audit (whole-codebase pentest): paths::collect_check_sum's threshold
    // family-expansion assumes the signature binder is a plain name, so it
    // pushed exactly one slot to expand. The only way to give it a NON-name
    // sequence (which pushes nothing, so a const key array's `slots > 1` would
    // make the old `out.pop().expect(..)` pop a sibling term or panic on an
    // empty accumulator) is an array literal `s in [s1, s2, s3]`. sema rejects
    // an array literal of WITNESS values ("array literals are const-only"), and
    // the CLI runs path analysis ONLY after sema is clean (seal.rs gates
    // instantiation on sema_clean, with intervals/paths nested under it). So
    // sema is the boundary that keeps the threshold recognizer safe; this test
    // pins it. (paths.rs also bails defensively to the general sum lowering if
    // it ever does see a non-name sig binder -- belt and suspenders.)
    let (contract, pd) = parse_source(
        "contract T {
            extern const keys: [PublicKey; 3];
            spend f(s1: Signature, s2: Signature, s3: Signature) {
                require sum(k in keys, s in [s1, s2, s3] => k.check(s)) >= 2;
            }
            keypath None;
        }",
    );
    assert!(pd.is_empty(), "parse: {pd:#?}");
    let c = contract.expect("contract");
    let (sd, _info) = sema::analyze(&c);
    assert!(
        sd.iter().any(|d| d.code == "sema/array-const"),
        "expected sema to reject the array-literal witness binder, got: {sd:#?}"
    );
}

#[test]
fn unpinned_witness_key_is_not_binding() {
    // The spender chose the key, exactly what a thief has.
    let cs = codes(
        "contract T {
            spend f(relaxed k: PublicKey, s: Signature) { require k.check(s); }
            keypath None;
        }",
        "{}",
    );
    assert!(cs.contains(&"auth/theft"), "{cs:?}");
}

#[test]
fn pinned_witness_key_is_binding_delegation() {
    let report = ok(
        "contract T {
            extern const commitment: Hash<Hash160>;
            spend f(k: PublicKey, s: Signature) {
                require { hash160(k) == commitment, k.check(s) }
            }
            keypath None;
        }",
        &format!(r#"{{"commitment": "0x{}"}}"#, "ab".repeat(20)),
    );
    // The pinned key is Determined; the sig is Signed.
    let p = &report.paths[0];
    let class_of = |n: &str| p.params.iter().find(|x| x.name == n).unwrap().class;
    assert_eq!(class_of("k"), Class::Determined);
    assert_eq!(class_of("s"), Class::Signed);
}

#[test]
fn threshold_bindingness_uses_the_instantiated_k() {
    let src = "contract T {
        extern const M: Int;
        extern const a: PublicKey; extern const b: PublicKey;
        spend f(sa: Signature, sb: Signature) {
            require a.check(sa) + b.check(sb) >= M;
        }
        keypath None;
    }";
    // M = 1: at least one const-key signature required, so binding.
    let report = ok(src, &format!(r#"{{"M": 1, "a": {KEY}, "b": {KEY}}}"#));
    assert_eq!(report.paths[0].threshold, Some((1, 2)));
    // M = 0: the sum can be satisfied with zero signatures, so theft.
    let cs = codes(src, &format!(r#"{{"M": 0, "a": {KEY}, "b": {KEY}}}"#));
    assert!(cs.contains(&"auth/theft"), "{cs:?}");
}

#[test]
fn comprehension_threshold_counts() {
    let report = ok(
        "contract T {
            extern const N: Int;
            extern const keys: [PublicKey; N];
            spend f(sigs: [Signature; N]) {
                require sum(k in keys, s in sigs => k.check(s)) >= 2;
            }
            keypath None;
        }",
        &format!(r#"{{"N": 3, "keys": [{KEY}, {KEY}, {KEY}]}}"#),
    );
    assert_eq!(report.paths[0].threshold, Some((2, 3)));
    assert_eq!(report.paths[0].params[0].class, Class::Signed);
}

// --- timelocks ---

#[test]
fn timelock_domain_mixing_is_unsatisfiable() {
    let cs = codes(
        "contract T {
            extern const k: PublicKey;
            spend f(s: Signature) {
                require {
                    after(LockTime.Absolute(height: 900_000)),
                    after(LockTime.Absolute(time: \"2026-06-10T14:30:00Z\")),
                    k.check(s)
                }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY}}}"#),
    );
    assert!(cs.contains(&"feasibility/timelock-mix"), "{cs:?}");

    let cs = codes(
        "contract T {
            extern const k: PublicKey;
            spend f(s: Signature) {
                require {
                    after(LockTime.Relative(blocks: 100)),
                    after(LockTime.Relative(time: \"P30D\")),
                    k.check(s)
                }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY}}}"#),
    );
    assert!(cs.contains(&"feasibility/timelock-mix"), "{cs:?}");
}

#[test]
fn same_domain_locks_take_the_max_obligation() {
    let report = ok(
        "contract T {
            extern const k: PublicKey;
            spend f(s: Signature) {
                require {
                    after(LockTime.Relative(blocks: 100)),
                    after(LockTime.Relative(blocks: 4320)),
                    k.check(s)
                }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY}}}"#),
    );
    let obligations = &report.paths[0].obligations;
    assert_eq!(obligations.len(), 1, "{obligations:?}");
    assert!(obligations[0].contains("4320"), "{obligations:?}");
}

#[test]
fn body_level_locktime_values_are_validated() {
    // LockTime constructors inside spend bodies.
    let cs = codes(
        "contract T {
            extern const k: PublicKey;
            spend f(s: Signature) {
                require { after(LockTime.Relative(blocks: 70_000)), k.check(s) }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY}}}"#),
    );
    assert!(cs.contains(&"inst/locktime"), "{cs:?}");
}

#[test]
fn constant_false_require_is_unsatisfiable() {
    let cs = codes(
        "contract T {
            extern const k: PublicKey;
            spend f(s: Signature) { require { false, k.check(s) } }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY}}}"#),
    );
    assert!(cs.contains(&"feasibility/unsatisfiable"), "{cs:?}");
}

// --- parameter classes ---

#[test]
fn unused_param_is_an_error() {
    let cs = codes(
        "contract T {
            extern const k: PublicKey;
            spend f(s: Signature, ghost: Int) { require k.check(s); }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY}}}"#),
    );
    assert!(cs.contains(&"malleability/unused"), "{cs:?}");
}

#[test]
fn free_choice_without_relaxed_is_an_error() {
    // A bid is bound by nothing.
    let cs = codes(
        "contract T {
            extern const k: PublicKey;
            spend f(bid: Int, s: Signature) {
                require { bid in 0..=1_000_000, k.check(s) }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY}}}"#),
    );
    assert!(cs.contains(&"malleability/relaxed"), "{cs:?}");
}

#[test]
fn relaxed_redundant_warns() {
    let (diags, _) = run(
        "contract T {
            extern const k: PublicKey;
            spend f(relaxed s: Signature) { require k.check(s); }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY}}}"#),
    );
    assert!(
        diags
            .iter()
            .any(|d| d.code == "malleability/relaxed-redundant"
                && d.severity == seal::diagnostics::Severity::Warning),
        "{diags:#?}"
    );
}

// --- corpus ---

#[test]
fn corpus_paths_are_clean_with_expected_templates() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
    let load = |name: &str| {
        let src = std::fs::read_to_string(dir.join(format!("{name}.sl"))).unwrap();
        let args = std::fs::read_to_string(dir.join(format!("{name}.args.json"))).unwrap();
        ok(&src, &args)
    };

    let vault = load("vault");
    assert_eq!(vault.paths.len(), 3); // fallback, recover, keypath
    let fallback = vault.paths.iter().find(|p| p.name == "fallback").unwrap();
    assert!(
        fallback.obligations[0].contains("4320"),
        "{:?}",
        fallback.obligations
    );
    assert!(vault.paths.iter().any(|p| p.kind == "keypath"));

    let htlc = load("htlc");
    let swap = htlc.paths.iter().find(|p| p.name == "swap").unwrap();
    let preimage = swap.params.iter().find(|p| p.name == "preimage").unwrap();
    assert_eq!(preimage.class, Class::Determined, "preimage is hash-pinned");
    let refund = htlc.paths.iter().find(|p| p.name == "refund").unwrap();
    assert!(
        refund.obligations[0].contains("900000"),
        "{:?}",
        refund.obligations
    );

    let multisig = load("multisig");
    let f = multisig
        .paths
        .iter()
        .find(|p| p.name == "fallback")
        .unwrap();
    assert_eq!(f.threshold, Some((2, 3)), "the instantiated 2-of-3 family");

    let cat = load("cat_bounty");
    let claim = cat.paths.iter().find(|p| p.name == "claim").unwrap();
    let drawing = claim.params.iter().find(|p| p.name == "drawing").unwrap();
    assert_eq!(drawing.class, Class::Relaxed, "the doodle is a free choice");
    let sig = claim.params.iter().find(|p| p.name == "signature").unwrap();
    assert_eq!(sig.class, Class::Signed);
}
