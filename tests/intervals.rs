//! Interval engine (bounds) tests: overflow detection with suggestions,
//! require-narrowing (forward, order-aware), select-arm facts, comprehension
//! folding, and the classifier's score interval computed exactly from the
//! instantiated weights.

use seal::analysis::consteval::{Env, bind_args, instantiate};
use seal::analysis::intervals::{Interval, analyze};
use seal::analysis::sema;
use seal::json;
use seal::syntax::parser::parse_source;

/// Parse + sema + bind + instantiate + intervals. Everything before the
/// engine must be clean.
fn run(
    src: &str,
    args: &str,
) -> (
    Vec<seal::diagnostics::Diagnostic>,
    seal::analysis::intervals::Report,
) {
    let (contract, pd) = parse_source(src);
    assert!(pd.is_empty(), "parse: {pd:#?}");
    let c = contract.expect("contract");
    let (sd, info) = sema::analyze(&c);
    assert!(sd.is_empty(), "sema: {sd:#?}");
    let mut env: Env = bind_args(&info, &json::parse(args).expect("json"))
        .unwrap_or_else(|e| panic!("bind: {e:#?}"));
    let id = instantiate(&c, &mut env);
    assert!(id.is_empty(), "instantiate: {id:#?}");
    analyze(&c, &env)
}

fn ok(src: &str, args: &str) -> seal::analysis::intervals::Report {
    let (diags, report) = run(src, args);
    assert!(diags.is_empty(), "expected G1-clean, got: {diags:#?}");
    report
}

fn codes(src: &str, args: &str) -> Vec<&'static str> {
    let (diags, _) = run(src, args);
    assert!(!diags.is_empty(), "expected G1 diagnostics for {src:?}");
    diags.iter().map(|d| d.code).collect()
}

fn body2(stmts: &str) -> String {
    format!(
        "contract T {{
            extern const c: Int;
            spend f(x: Int, b: Bool, s: Signature) {{
                {stmts}
            }}
            keypath None;
        }}"
    )
}

// --- overflow: the `a + a` case

#[test]
fn unbounded_witness_addition_overflows_with_suggestion() {
    let (diags, _) = run(&body2("let bad = x + x; require bad > 0;"), r#"{"c": 1}"#);
    assert!(!diags.is_empty());
    assert_eq!(diags[0].code, "bounds/overflow");
    assert!(
        diags[0]
            .notes
            .iter()
            .any(|n| n.message.contains("pow(2, 30) - 1")),
        "the backward-solve suggestion, now a help note: {:?}",
        diags[0].notes
    );
}

#[test]
fn one_mistake_one_message_no_cascade() {
    // The overflow on `bad` is the only diagnostic: the later require on
    // the poisoned name must not add "has no fact" noise.
    let (diags, _) = run(&body2("let bad = x + x; require bad > 0;"), r#"{"c": 1}"#);
    assert_eq!(diags.len(), 1, "{diags:#?}");
    assert_eq!(diags[0].code, "bounds/overflow");
}

#[test]
fn narrowing_makes_the_same_code_provable() {
    // The fix the diagnostic suggests, applied, and the let's interval is
    // reported exactly.
    let report = ok(
        &body2("require x in 0..=1_000_000; let fine = x + x; require fine > 0;"),
        r#"{"c": 1}"#,
    );
    assert_eq!(
        report.lets,
        vec![(
            "f".into(),
            "fine".into(),
            Interval {
                lo: 0,
                hi: 2_000_000
            }
        )]
    );
}

#[test]
fn narrowing_is_order_aware() {
    // Use before the require: the value computes on full domain, so error.
    let cs = codes(
        &body2("let bad = x + x; require x in 0..=10; require bad > 0;"),
        r#"{"c": 1}"#,
    );
    assert!(cs.contains(&"bounds/overflow"), "{cs:?}");
}

#[test]
fn chain_and_comparison_narrowing() {
    ok(
        &body2("require 0 <= x <= 1000; let v = x + x; require v < 3000;"),
        r#"{"c": 1}"#,
    );
    // Narrowing from the const side of a comparison: x < c with c exact.
    ok(
        &body2("require x >= 0; require x < c; let v = x + x; require v >= 0;"),
        r#"{"c": 1000}"#,
    );
}

#[test]
fn contradiction_is_infeasibility() {
    let cs = codes(&body2("require x > 100; require x < 50;"), r#"{"c": 1}"#);
    assert!(cs.contains(&"bounds/infeasible"), "{cs:?}");
}

#[test]
fn oversized_literal_operand_is_caught() {
    // 3e9 fits i128 (folds fine) but cannot be pushed as a runtime operand.
    let cs = codes(
        &body2("let v = x + 3_000_000_000; require v > 0;"),
        r#"{"c": 1}"#,
    );
    assert!(cs.contains(&"bounds/operand"), "{cs:?}");
}

#[test]
fn exact_subexpressions_fold_without_false_positives() {
    // pow(2, 40) exceeds M but is exact, so it folds; only the runtime parts
    // are checked. (pow(2,40) - pow(2,40)) + x == x.
    ok(
        &body2("let v = pow(2, 40) - pow(2, 40) + x; require v == x;"),
        r#"{"c": 1}"#,
    );
}

// --- select: condition-sensitive facts

#[test]
fn select_arms_get_condition_facts() {
    // Provable only because the then-arm knows x < 1000 and the else-arm
    // knows x >= 1000 (so min(x, 2000) <= 2000 there; both arms stay small).
    let report = ok(
        &body2("require x >= 0; let v = select(x < 1000, then: x + x, else: 0); require v >= 0;"),
        r#"{"c": 1}"#,
    );
    // then-arm: x in [0, 999] gives x+x in [0, 1998]; else: 0. Hull: [0, 1998].
    assert_eq!(report.lets[0].2, Interval { lo: 0, hi: 1998 });
}

// --- comprehensions

#[test]
fn count_is_bounded_by_n() {
    let report = ok(
        "contract T {
            spend f(bits: [Bool; 7], s: Signature) {
                let n = count(b in bits => b);
                require n >= 3;
            }
            keypath None;
        }",
        "{}",
    );
    assert_eq!(report.lets[0].2, Interval { lo: 0, hi: 7 });
}

#[test]
fn partial_sums_are_checked_not_just_totals() {
    // Each element can be +/-2_000_000_000? No: bind small array but huge
    // count. 2000 elements by +/-2_000_000 stays in M only at the total, so
    // partials overflow midway: elements of 2_000_000 over 2000 steps pass
    // (max 4e9 > M), so expect failure at some partial.
    let weights: Vec<String> = (0..2000).map(|_| "2000000".to_string()).collect();
    let args = format!(r#"{{"ws": [{}]}}"#, weights.join(","));
    let src = "contract T {
        extern const ws: [Int; 2000];
        spend f(bits: [Bool; 2000], s: Signature) {
            let t = sum(w in ws, b in bits where b => w);
            require t >= 0;
        }
        keypath None;
    }";
    let (diags, _) = run(src, &args);
    assert!(
        diags.iter().any(|d| d.code == "bounds/overflow"),
        "{diags:#?}"
    );
}

#[test]
fn fold_iterates_the_transfer() {
    let report = ok(
        "contract T {
            extern const ws: [Int; 4];
            spend f(s: Signature) {
                let m = fold(acc = 0, w in ws => max(acc, w));
                require m >= 0;
            }
            keypath None;
        }",
        r#"{"ws": [3, 1, 4, 1]}"#,
    );
    // Exact per-element folding: max(0,3)=3, max(3,1)=3, max(3,4)=4, max(4,1)=4.
    assert_eq!(report.lets[0].2, Interval { lo: 4, hi: 4 });
}

// --- the corpus, and the score-interval claim

#[test]
fn corpus_is_g1_clean() {
    for name in ["vault", "htlc", "multisig", "cat_bounty"] {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
        let src = std::fs::read_to_string(dir.join(format!("{name}.sl"))).unwrap();
        let args = std::fs::read_to_string(dir.join(format!("{name}.args.json"))).unwrap();
        let (diags, _) = run(&src, &args);
        assert!(diags.is_empty(), "{name}: {diags:#?}");
    }
}

#[test]
fn classifier_score_interval_is_exact_from_the_weights() {
    // The score interval folds exactly from instantiated weights. Compute the
    // expectation from the args file itself, then demand the engine match it
    // to the integer.
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
    let src = std::fs::read_to_string(dir.join("cat_bounty.sl")).unwrap();
    let args_src = std::fs::read_to_string(dir.join("cat_bounty.args.json")).unwrap();

    let json = json::parse(&args_src).unwrap();
    let seal::json::Json::Object(fields) = &json else {
        panic!()
    };
    let weights: Vec<i128> = fields
        .iter()
        .find(|(k, _)| k == "weights")
        .map(|(_, v)| match v {
            seal::json::Json::Array(items) => items
                .iter()
                .map(|i| match i {
                    seal::json::Json::Int(v) => *v,
                    _ => panic!(),
                })
                .collect(),
            _ => panic!(),
        })
        .unwrap();
    let bias = fields
        .iter()
        .find_map(|(k, v)| {
            (k == "bias").then(|| match v {
                seal::json::Json::Int(v) => *v,
                _ => panic!(),
            })
        })
        .unwrap();
    // Each pixel is an unknown Bool guard: contribution is hull(w, 0).
    let lo: i128 = bias + weights.iter().map(|w| (*w).min(0)).sum::<i128>();
    let hi: i128 = bias + weights.iter().map(|w| (*w).max(0)).sum::<i128>();

    let (diags, report) = run(&src, &args_src);
    assert!(diags.is_empty(), "{diags:#?}");
    let score = report
        .lets
        .iter()
        .find(|(s, n, _)| s == "claim" && n == "score")
        .map(|(_, _, iv)| *iv)
        .expect("score interval reported");
    assert_eq!(
        score,
        Interval { lo, hi },
        "exact fold from the real weights"
    );
}
