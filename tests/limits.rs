//! Resource-limit pass (`src/limits.rs`): a contract that could never produce a
//! standard, spendable transaction (and would only burn memory) is rejected
//! BEFORE lowering allocates. Consensus/standardness-derived bounds.

use seal::analysis::consteval::{Env, bind_args, instantiate};
use seal::analysis::limits;
use seal::analysis::sema;
use seal::analysis::sema::ContractInfo;
use seal::diagnostics::Severity;
use seal::json;
use seal::syntax::parser;

const KEY: &str = "0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c";

/// Parse -> sema -> bind -> instantiate (NOT lower: the whole point is that
/// limits reject before lowering would allocate). Returns the codes limits
/// produces, or a marker if an earlier stage rejected.
fn limit_codes(src: &str, args: &str) -> Vec<String> {
    let (contract, pd) = parser::parse_source(src);
    assert!(
        pd.iter().all(|d| d.severity != Severity::Error),
        "parse: {pd:#?}"
    );
    let c = contract.expect("contract");
    let (sd, info): (_, ContractInfo) = sema::analyze(&c);
    if sd.iter().any(|d| d.severity == Severity::Error) {
        return sd.iter().map(|d| d.code.to_string()).collect();
    }
    let mut env: Env = bind_args(&info, &json::parse(args).expect("json")).expect("bind");
    let id = instantiate(&c, &mut env);
    assert!(
        id.iter().all(|d| d.severity != Severity::Error),
        "instantiate: {id:#?}"
    );
    limits::analyze(&c, &info, &env)
        .iter()
        .map(|d| d.code.to_string())
        .collect()
}

#[test]
fn corpus_is_within_limits() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
    for name in [
        "cat_bounty",
        "multisig",
        "mirage",
        "quorum",
        "vault",
        "htlc",
    ] {
        let src = std::fs::read_to_string(dir.join(format!("{name}.sl"))).unwrap();
        let args = std::fs::read_to_string(dir.join(format!("{name}.args.json"))).unwrap();
        let codes = limit_codes(&src, &args);
        assert!(codes.is_empty(), "{name} hit resource limits: {codes:?}");
    }
}

#[test]
fn huge_witness_array_is_rejected() {
    // 2000 Bool pixels + sig = 2001 witness elements > 1000-element stack limit.
    let src = "contract C { extern const k: PublicKey;
        spend s(relaxed drawing: [Bool; 2000], sig: Signature) {
            require { count(b in drawing where b => true) >= 0, k.check(sig) }
        } keypath None; }";
    let codes = limit_codes(src, &format!("{{\"k\":\"{KEY}\"}}"));
    assert!(
        codes.iter().any(|c| c == "limits/witness-stack"),
        "got {codes:?}"
    );
}

#[test]
fn witness_arity_boundary() {
    // 999 Bool + sig = 1000 == the cap -> ok; 1000 Bool + sig = 1001 -> rejected.
    let ok = "contract C { extern const k: PublicKey;
        spend s(relaxed d: [Bool; 999], sig: Signature) {
            require { count(b in d where b => true) >= 0, k.check(sig) }
        } keypath None; }";
    assert!(limit_codes(ok, &format!("{{\"k\":\"{KEY}\"}}")).is_empty());
    let over = ok.replace("[Bool; 999]", "[Bool; 1000]");
    assert!(
        limit_codes(&over, &format!("{{\"k\":\"{KEY}\"}}"))
            .iter()
            .any(|c| c == "limits/witness-stack")
    );
}

#[test]
fn huge_comprehension_range_is_rejected() {
    let src = "contract R { extern const k: PublicKey;
        spend s(sig: Signature) {
            let z = sum(i in 0..500000 => 1);
            require { z >= 0, k.check(sig) }
        } keypath None; }";
    let codes = limit_codes(src, &format!("{{\"k\":\"{KEY}\"}}"));
    assert!(codes.iter().any(|c| c == "limits/unroll"), "got {codes:?}");
}

#[test]
fn json_input_size_is_capped() {
    // Over 8 MiB of input is rejected before parsing (memory totality).
    let big = format!("[{}]", "1,".repeat(5_000_000)); // ~10 MB
    assert!(big.len() > 8 << 20);
    assert!(
        seal::json::parse(&big).is_err(),
        "oversized JSON must be rejected"
    );
    // A small valid input still parses.
    assert!(seal::json::parse("[1, 2, 3]").is_ok());
}
