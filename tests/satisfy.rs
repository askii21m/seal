//! The satisfier differential: "compiles, therefore spendable", automatic.
//!
//! The satisfier builds the witness from a high-level spend plan; the
//! interpreter executes it. An honest plan must spend; a declining plan
//! must not. No hand-built witness stacks, so this is the form that can be
//! fuzzed over random contracts.

use seal::analysis::consteval::{Env, bind_args, instantiate};
use seal::analysis::intervals;
use seal::analysis::paths;
use seal::analysis::sema;
use seal::analysis::sema::{ContractInfo, SpendSig};
use seal::codegen::lower::{LoweredLeaf, lower};
use seal::diagnostics::Severity;
use seal::json;
use seal::syntax::parser;
use seal::verify::interp::{Context, execute};
use seal::verify::satisfy::{SatValue, build_witness};

const KEY_A: &str = "\"0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c\"";
const KEY_B: &str = "\"0x5cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc\"";
const MARKER: [u8; 64] = [0xAA; 64];

fn setup(src: &str, args: &str) -> (ContractInfo, Env, Vec<LoweredLeaf>) {
    let (contract, pd) = parser::parse_source(src);
    assert!(pd.is_empty(), "parse: {pd:#?}");
    let c = contract.expect("contract");
    let (sd, info) = sema::analyze(&c);
    assert!(sd.is_empty(), "sema: {sd:#?}");
    let mut env: Env = bind_args(&info, &json::parse(args).expect("json")).expect("bind");
    let id = instantiate(&c, &mut env);
    assert!(
        id.iter().all(|d| d.severity != Severity::Error),
        "inst: {id:#?}"
    );
    let (g1, report) = intervals::analyze(&c, &env);
    assert!(g1.is_empty(), "G1: {g1:#?}");
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
    (info, env, leaves)
}

fn sig_of<'a>(info: &'a ContractInfo, name: &str) -> &'a SpendSig {
    info.spends
        .iter()
        .find(|s| s.name == name)
        .expect("spendable sig")
}

/// Satisfy a leaf with a plan and execute (marker-sig oracle accepts any
/// present signature; the lowering logic is the subject. Key-binding is
/// proven separately by the real-Schnorr test).
fn spend(
    info: &ContractInfo,
    env: &Env,
    leaf: &LoweredLeaf,
    plan: &[(&str, SatValue)],
    ctx_seq: u32,
    ctx_lt: u32,
) -> Result<(), String> {
    let sig = sig_of(info, &leaf.name);
    let owned: Vec<(String, SatValue)> = plan
        .iter()
        .map(|(n, v)| (n.to_string(), v.clone()))
        .collect();
    let stack = build_witness(leaf, sig, env, &owned, &MARKER).expect("build witness");
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: ctx_lt,
        sequence: ctx_seq,
        tx_version: 2,
        verify_sig: &oracle,
    };
    execute(&leaf.script, &stack, &ctx)
}

fn leaf<'a>(leaves: &'a [LoweredLeaf], name: &str) -> &'a LoweredLeaf {
    leaves.iter().find(|l| l.name == name).expect("leaf")
}

#[test]
fn single_sig_is_spendable() {
    let (info, env, leaves) = setup(
        "contract T { extern const k: PublicKey;
            spend f(s: Signature) { require k.check(s); } keypath None; }",
        &format!(r#"{{"k": {KEY_A}}}"#),
    );
    let f = leaf(&leaves, "f");
    assert!(
        spend(
            &info,
            &env,
            f,
            &[("s", SatValue::Sig(true))],
            0xffff_fffe,
            0
        )
        .is_ok()
    );
    // Declining the only signature means not spendable.
    assert!(
        spend(
            &info,
            &env,
            f,
            &[("s", SatValue::Sig(false))],
            0xffff_fffe,
            0
        )
        .is_err()
    );
}

#[test]
fn hashlock_is_spendable_with_the_preimage() {
    let preimage = vec![0x42u8; 32];
    let digest = seal::crypto::sha256::sha256(&preimage);
    let hex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
    let (info, env, leaves) = setup(
        "contract T { extern const k: PublicKey; extern const h: Bytes<32>;
            spend f(p: Bytes<32>, s: Signature) {
                require { sha256(p) == h, k.check(s) }
            } keypath None; }",
        &format!(r#"{{"k": {KEY_A}, "h": "0x{hex}"}}"#),
    );
    let f = leaf(&leaves, "f");
    assert!(
        spend(
            &info,
            &env,
            f,
            &[("p", SatValue::Bytes(preimage)), ("s", SatValue::Sig(true))],
            0xffff_fffe,
            0
        )
        .is_ok()
    );
    // Wrong preimage means not spendable.
    assert!(
        spend(
            &info,
            &env,
            f,
            &[
                ("p", SatValue::Bytes(vec![0x99u8; 32])),
                ("s", SatValue::Sig(true))
            ],
            0xffff_fffe,
            0
        )
        .is_err()
    );
}

#[test]
fn threshold_family_is_spendable_at_k() {
    let (info, env, leaves) = setup(
        "contract T { extern const a: PublicKey; extern const b: PublicKey;
            spend f(sa: Signature, sb: Signature) {
                require a.check(sa) + b.check(sb) >= 2;
            } keypath None; }",
        &format!(r#"{{"a": {KEY_A}, "b": {KEY_B}}}"#),
    );
    let f = leaf(&leaves, "f");
    // Both sign, so 2 >= 2, so spendable.
    assert!(
        spend(
            &info,
            &env,
            f,
            &[("sa", SatValue::Sig(true)), ("sb", SatValue::Sig(true))],
            0xffff_fffe,
            0
        )
        .is_ok()
    );
    // Only one signs, so 1 < 2, so not spendable.
    assert!(
        spend(
            &info,
            &env,
            f,
            &[("sa", SatValue::Sig(true)), ("sb", SatValue::Sig(false))],
            0xffff_fffe,
            0
        )
        .is_err()
    );
}

#[test]
fn range_param_is_spendable_in_domain() {
    let (info, env, leaves) = setup(
        "contract T { extern const k: PublicKey;
            spend f(relaxed x: Int, s: Signature) {
                require { x in 0..100, k.check(s) }
            } keypath None; }",
        &format!(r#"{{"k": {KEY_A}}}"#),
    );
    let f = leaf(&leaves, "f");
    let go = |x: i64| {
        spend(
            &info,
            &env,
            f,
            &[("x", SatValue::Int(x)), ("s", SatValue::Sig(true))],
            0xffff_fffe,
            0,
        )
    };
    assert!(go(50).is_ok());
    assert!(go(0).is_ok());
    assert!(go(100).is_err());
    assert!(go(-1).is_err());
}

#[test]
fn the_whole_corpus_is_spendable() {
    // Every spendable path of every corpus contract is satisfiable: the
    // "compiles, therefore spendable" guarantee on the real golden contracts.
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
    let load = |name: &str| -> (ContractInfo, Env, Vec<LoweredLeaf>) {
        let src = std::fs::read_to_string(dir.join(format!("{name}.sl"))).unwrap();
        let args = std::fs::read_to_string(dir.join(format!("{name}.args.json"))).unwrap();
        setup(&src, &args)
    };

    // vault: each leaf is a single sig behind a relative timelock (>= its
    // CSV value). Sign, supply enough sequence age.
    let (vi, ve, vl) = load("vault");
    for (name, age) in [("fallback", 4320u32), ("recover", 12960)] {
        let l = leaf(&vl, name);
        assert!(
            spend(&vi, &ve, l, &[("signature", SatValue::Sig(true))], age, 0).is_ok(),
            "vault.{name}"
        );
        // Too-young sequence means CSV blocks the spend.
        assert!(
            spend(
                &vi,
                &ve,
                l,
                &[("signature", SatValue::Sig(true))],
                age - 1,
                0
            )
            .is_err()
        );
    }

    // multisig (instantiated 2-of-3): any 2 of the 3 signature slots.
    let (mi, me, ml) = load("multisig");
    let f = leaf(&ml, "fallback");
    let two_of_three = |signs: [bool; 3]| {
        let sigs = SatValue::Array(signs.iter().map(|&b| SatValue::Sig(b)).collect());
        spend(&mi, &me, f, &[("sigs", sigs)], 0xffff_fffe, 0)
    };
    assert!(two_of_three([true, true, false]).is_ok(), "2-of-3 spends");
    assert!(
        two_of_three([true, false, false]).is_err(),
        "1-of-3 does not"
    );

    // cat_bounty: a maximal drawing + the solver signature.
    let (ci, ce, cl) = load("cat_bounty");
    let claim = leaf(&cl, "claim");
    let weights = match &ce["weights"] {
        seal::analysis::consteval::ConstValue::Array(items) => items
            .iter()
            .map(|v| match v {
                seal::analysis::consteval::ConstValue::Int(n) => *n,
                _ => panic!(),
            })
            .collect::<Vec<_>>(),
        _ => panic!(),
    };
    let drawing = SatValue::Array((0..784).map(|i| SatValue::Bool(weights[i] > 0)).collect());
    assert!(
        spend(
            &ci,
            &ce,
            claim,
            &[("drawing", drawing), ("signature", SatValue::Sig(true))],
            0xffff_fffe,
            0
        )
        .is_ok(),
        "cat_bounty winning drawing spends"
    );
}
