//! Const evaluation and extern injection tests: every binder rejection, the
//! evaluator's strictness rules, and the corpus instantiating clean with the
//! checked-in args files.

use seal::analysis::consteval::{ConstValue, Env, bind_args, instantiate};
use seal::analysis::sema;
use seal::diagnostics::Severity;
use seal::json;
use seal::syntax::parser::parse_source;

/// Parse + analyze (must be clean) + bind + instantiate.
fn run(src: &str, args: &str) -> Result<(Env, Vec<seal::diagnostics::Diagnostic>), Vec<String>> {
    let (contract, pd) = parse_source(src);
    assert!(pd.is_empty(), "parse: {pd:#?}");
    let c = contract.expect("contract");
    let (sd, info) = sema::analyze(&c);
    assert!(sd.is_empty(), "sema: {sd:#?}");
    let json = json::parse(args).expect("args json");
    let mut env = bind_args(&info, &json)?;
    let diags = instantiate(&c, &mut env);
    Ok((env, diags))
}

fn run_ok(src: &str, args: &str) -> Env {
    let (env, diags) = run(src, args).expect("bind");
    assert!(diags.is_empty(), "instantiate: {diags:#?}");
    env
}

fn inst_codes(src: &str, args: &str) -> Vec<&'static str> {
    let (_, diags) = run(src, args).expect("bind");
    assert!(!diags.is_empty(), "expected instantiation diagnostics");
    diags.iter().map(|d| d.code).collect()
}

fn bind_errs(src: &str, args: &str) -> Vec<String> {
    run(src, args).expect_err("expected binder errors")
}

const KEY: &str = "0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c";

// --- preconditions evaluate with real values

#[test]
fn precondition_passes_and_fails_with_values() {
    let src = "contract T { extern const M: Int; extern const N: Int;
                require 1 <= M <= N; keypath None; }";
    run_ok(src, r#"{"M": 2, "N": 3}"#);

    let (_, diags) = run(src, r#"{"M": 5, "N": 3}"#).unwrap();
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].code, "inst/precondition");
    assert!(
        diags[0].message.contains("M = 5") && diags[0].message.contains("N = 3"),
        "failure must show the values: {}",
        diags[0].message
    );
}

#[test]
fn array_precondition_folds() {
    let src = "contract T { extern const ws: [Int; 3]; require all(w in ws => w > 0);
                keypath None; }";
    run_ok(src, r#"{"ws": [1, 2, 3]}"#);
    let codes = inst_codes(src, r#"{"ws": [1, 0, 3]}"#);
    assert!(codes.contains(&"inst/precondition"), "{codes:?}");
}

// --- const folding semantics

#[test]
fn arithmetic_and_consts_fold() {
    let env = run_ok(
        "contract T { extern const x: Int;
           const a = x + 3;
           const c = a - 3;
           const d = select(c > 1, then: min(c, 7), else: 0);
           const e = fold(acc = 0, i in 0..4 => acc + i);
           const f = sum(w in [1, 2, 3], i in 0..3 where w != 2 => w + i);
           keypath None; }",
        r#"{"x": 2}"#,
    );
    assert_eq!(env["a"], ConstValue::Int(5));
    assert_eq!(env["c"], ConstValue::Int(2));
    assert_eq!(env["d"], ConstValue::Int(2));
    assert_eq!(env["e"], ConstValue::Int(6)); // 0+1+2+3
    assert_eq!(env["f"], ConstValue::Int(1 + 3 + 2)); // skips w==2
}

#[test]
fn select_is_strict_both_arms_evaluate() {
    // The untaken arm's overflow is still an error: preconditions hold per
    // node, branch-independent.
    let src = "contract T {
                const v = select(true, then: 1, else: pow(2, 200));
                keypath None; }";
    let codes = inst_codes(src, "{}");
    assert!(codes.contains(&"inst/overflow"), "{codes:?}");
}

#[test]
fn overflow_is_checked_never_wraps() {
    let src = "contract T { const v = pow(2, 200); keypath None; }";
    let codes = inst_codes(src, "{}");
    assert!(codes.contains(&"inst/overflow"), "{codes:?}");
}

#[test]
fn fold_cap_guards_compile_time() {
    let src = "contract T { const v = sum(i in 0..100000 => i); keypath None; }";
    let codes = inst_codes(src, "{}");
    assert!(codes.contains(&"inst/fold-cap"), "{codes:?}");
}

#[test]
fn index_bounds_checked() {
    let src = "contract T { extern const ws: [Int; 3]; const v = ws[5]; keypath None; }";
    // sema allows (const index, type-correct); the value check is here.
    let (contract, _) = parse_source(src);
    let c = contract.unwrap();
    let (sd, info) = sema::analyze(&c);
    assert!(sd.is_empty(), "{sd:#?}");
    let mut env = bind_args(&info, &json::parse(r#"{"ws": [1,2,3]}"#).unwrap()).unwrap();
    let diags = instantiate(&c, &mut env);
    assert!(diags.iter().any(|d| d.code == "inst/index"), "{diags:#?}");
}

// --- locktime values

#[test]
fn locktime_construction_validates() {
    run_ok(
        "contract T { const t = LockTime.Absolute(height: 900_000); keypath None; }",
        "{}",
    );
    let codes = inst_codes(
        "contract T { const t = LockTime.Absolute(height: 500_000_000); keypath None; }",
        "{}",
    );
    assert!(codes.contains(&"inst/locktime"), "{codes:?}");
    let codes = inst_codes(
        "contract T { const t = LockTime.Relative(blocks: 70_000); keypath None; }",
        "{}",
    );
    assert!(codes.contains(&"inst/locktime"), "{codes:?}");
}

#[test]
fn span_rounding_warns() {
    let src = "contract T { const t = LockTime.Relative(time: \"PT90M\"); keypath None; }";
    let (contract, _) = parse_source(src);
    let c = contract.unwrap();
    let (sd, _) = sema::analyze(&c);
    assert!(sd.is_empty());
    let mut env = Env::new();
    let diags = instantiate(&c, &mut env);
    // PT90M = 5400s = 10.546875 * 512, rounds up to 11 units, with a warning.
    assert_eq!(diags.len(), 1, "{diags:#?}");
    assert_eq!(diags[0].code, "inst/span-rounded");
    assert_eq!(diags[0].severity, Severity::Warning);
    assert!(diags[0].message.contains("11*512s"), "{}", diags[0].message);
}

#[test]
fn iso_durations_strict_subset() {
    use seal::analysis::consteval::iso_duration_to_units;
    // Exact forms: every documented spelling, exact unit math.
    assert_eq!(
        iso_duration_to_units("P4W"),
        Ok((4725, false)),
        "2419200s exact"
    );
    assert_eq!(
        iso_duration_to_units("P90D"),
        Ok((15188, true)),
        "7776000s = 15187.5 rounds up"
    );
    assert_eq!(
        iso_duration_to_units("PT1H30M"),
        Ok((11, true)),
        "5400s rounds up"
    );
    assert_eq!(
        iso_duration_to_units("P1DT12H"),
        Ok((254, true)),
        "129600s = 253.125 units"
    );
    assert_eq!(iso_duration_to_units("PT512S"), Ok((1, false)));
    assert_eq!(
        iso_duration_to_units("P0D"),
        Ok((0, false)),
        "zero span is legal"
    );
    // Strict rejections.
    for bad in [
        "90D", "P", "PT", "P90", "P1W2D", "P1Y", "P2M", "PT1H1H", "P1DT", "PT1.5H",
    ] {
        assert!(
            iso_duration_to_units(bad).is_err(),
            "{bad} must be rejected"
        );
    }
    // Calendar units get the dedicated message.
    let err = iso_duration_to_units("P1Y").unwrap_err();
    assert!(err.contains("calendar-dependent"), "{err}");
    // The 388-day cap.
    assert!(iso_duration_to_units("P389D").is_err());
    assert!(iso_duration_to_units("P388D").is_ok());
}

#[test]
fn iso8601_strictness() {
    use seal::analysis::consteval::parse_iso8601;
    assert_eq!(
        parse_iso8601("2026-06-10T14:30:00Z").unwrap(),
        1_781_101_800
    );
    assert_eq!(parse_iso8601("1985-11-05T00:53:20Z").unwrap(), 500_000_000);
    for bad in [
        "2026-06-10 14:30:00Z", // no T
        "2026-06-10T14:30:00",  // no Z (UTC only)
        "2026-13-10T14:30:00Z", // month 13
        "2026-02-30T14:30:00Z", // Feb 30
        "2026-06-10T24:00:00Z", // hour 24
        "1985-01-01T00:00:00Z", // before the CLTV time threshold
        "2200-01-01T00:00:00Z", // beyond u32
    ] {
        assert!(parse_iso8601(bad).is_err(), "{bad} should be rejected");
    }
    // Leap year: Feb 29 valid in 2028, not 2027.
    assert!(parse_iso8601("2028-02-29T00:00:00Z").is_ok());
    assert!(parse_iso8601("2027-02-29T00:00:00Z").is_err());
}

// --- binder rejections

#[test]
fn binder_rejections_teach() {
    let src = "contract T { extern const k: PublicKey; extern const n: Int;
                keypath k; }";
    let errs = bind_errs(src, r#"{"k": "0xabcd", "n": 1}"#);
    assert!(errs[0].contains("64 hex digits"), "{errs:?}");

    let errs = bind_errs(src, &format!(r#"{{"k": "{KEY}"}}"#));
    assert!(
        errs.iter().any(|e| e.contains("missing extern `n`")),
        "{errs:?}"
    );

    let errs = bind_errs(src, &format!(r#"{{"k": "{KEY}", "n": 1, "typo": 2}}"#));
    assert!(
        errs.iter().any(|e| e.contains("`typo` is not an extern")),
        "{errs:?}"
    );

    let errs = bind_errs(src, &format!(r#"{{"k": "{KEY}", "n": 4000000000}}"#));
    assert!(errs.iter().any(|e| e.contains("CScriptNum")), "{errs:?}");
}

#[test]
fn named_length_arrays_cross_check() {
    let src = "contract T { extern const N: Int; extern const keys: [PublicKey; N];
                keypath None; }";
    run_ok(src, &format!(r#"{{"N": 2, "keys": ["{KEY}", "{KEY}"]}}"#));
    let errs = bind_errs(src, &format!(r#"{{"N": 3, "keys": ["{KEY}", "{KEY}"]}}"#));
    assert!(
        errs.iter().any(|e| e.contains("expected 3 elements")),
        "the spec's len(keys)==N cross-check: {errs:?}"
    );
}

// --- corpus gate

#[test]
fn corpus_instantiates_clean() {
    for name in ["vault", "htlc", "multisig", "cat_bounty"] {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
        let src = std::fs::read_to_string(dir.join(format!("{name}.sl"))).unwrap();
        let args = std::fs::read_to_string(dir.join(format!("{name}.args.json"))).unwrap();
        let (env, diags) =
            run(&src, &args).unwrap_or_else(|e| panic!("{name}: binder errors: {e:#?}"));
        assert!(diags.is_empty(), "{name}: {diags:#?}");
        assert!(!env.is_empty(), "{name}: no externs bound");
    }
}

#[test]
fn hash_intrinsics_const_evaluate() {
    // Commitments fold at compile time: the htlc author can write the
    // preimage and let the compiler derive the digest.
    let src = r#"contract T {
        const preimage = Bytes<32>("0x6262626262626262626262626262626262626262626262626262626262626262");
        const digest = sha256(preimage);
        const double = hash256(preimage);
        const short = hash160(preimage);
        keypath None;
    }"#;
    let (contract, pd) = parse_source(src);
    assert!(pd.is_empty(), "{pd:#?}");
    let c = contract.unwrap();
    let (sd, _) = sema::analyze(&c);
    assert!(sd.is_empty(), "{sd:#?}");
    let mut env = Env::new();
    let diags = instantiate(&c, &mut env);
    assert!(diags.is_empty(), "{diags:#?}");
    // sha256(0x62 * 32), golden from python hashlib.
    let ConstValue::Bytes(d) = &env["digest"] else {
        panic!("digest")
    };
    let hex: String = d.iter().map(|b| format!("{b:02x}")).collect();
    assert_eq!(
        hex,
        "bdb339768bc5e4fecbe55a442056919b2b325907d49bcbf3bf8de13781996a83"
    );
    let ConstValue::Bytes(h) = &env["short"] else {
        panic!("short")
    };
    assert_eq!(h.len(), 20, "hash160 is 20 bytes");
    let ConstValue::Bytes(dd) = &env["double"] else {
        panic!("double")
    };
    assert_eq!(dd.len(), 32);
}
