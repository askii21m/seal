//! Optimizer differential: the optimized leaf must accept and reject exactly
//! the witnesses the naive leaf does, and must be no larger. Lowering stays
//! the oracle; this checks the optimizer against it on the golden corpus.

use seal::analysis::consteval::{ConstValue, Env, bind_args, instantiate};
use seal::analysis::intervals;
use seal::analysis::paths;
use seal::analysis::sema;
use seal::analysis::sema::{ContractInfo, SpendSig};
use seal::codegen::lower::{LoweredLeaf, lower};
use seal::codegen::optimize::optimize;
use seal::diagnostics::Severity;
use seal::json;
use seal::syntax::parser;
use seal::verify::interp::{Context, execute};
use seal::verify::satisfy::{SatValue, build_witness};

const MARKER: [u8; 64] = [0xAA; 64];

fn load(name: &str) -> (ContractInfo, Env, Vec<LoweredLeaf>) {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
    let src = std::fs::read_to_string(dir.join(format!("{name}.sl"))).unwrap();
    let args = std::fs::read_to_string(dir.join(format!("{name}.args.json"))).unwrap();
    let (contract, pd) = parser::parse_source(&src);
    assert!(pd.is_empty(), "parse {name}: {pd:#?}");
    let c = contract.unwrap();
    let (sd, info) = sema::analyze(&c);
    assert!(sd.is_empty(), "sema {name}: {sd:#?}");
    let mut env = bind_args(&info, &json::parse(&args).unwrap()).unwrap();
    let id = instantiate(&c, &mut env);
    assert!(id.iter().all(|d| d.severity != Severity::Error));
    let (b, report) = intervals::analyze(&c, &env);
    assert!(b.is_empty());
    let (pd2, _) = paths::analyze(&c, &info, &env);
    assert!(pd2.iter().all(|d| d.severity != Severity::Error));
    let (ld, leaves) = lower(&c, &info, &env, &report);
    assert!(ld.iter().all(|d| d.severity != Severity::Error));
    (info, env, leaves)
}

fn sig_of<'a>(info: &'a ContractInfo, name: &str) -> &'a SpendSig {
    info.spends.iter().find(|s| s.name == name).unwrap()
}

fn exec(leaf: &LoweredLeaf, stack: &[Vec<u8>], seq: u32, lt: u32) -> bool {
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: lt,
        sequence: seq,
        tx_version: 2,
        verify_sig: &oracle,
    };
    execute(&leaf.script, stack, &ctx).is_ok()
}

/// Run a plan through both the naive and optimized leaf; require identical
/// accept/reject, matching the expectation. The optimizer keeps witness
/// order, so one witness stack drives both.
fn agree(
    info: &ContractInfo,
    env: &Env,
    leaf: &LoweredLeaf,
    plan: &[(&str, SatValue)],
    seq: u32,
    lt: u32,
    expect: bool,
) {
    let opt = optimize(leaf);
    let sig = sig_of(info, &leaf.name);
    let owned: Vec<(String, SatValue)> = plan
        .iter()
        .map(|(n, v)| (n.to_string(), v.clone()))
        .collect();
    let naive_stack = build_witness(leaf, sig, env, &owned, &MARKER).expect("naive witness");
    let opt_stack = build_witness(&opt, sig, env, &owned, &MARKER).expect("opt witness");
    assert_eq!(
        naive_stack, opt_stack,
        "witness order changed for {}",
        leaf.name
    );
    let n = exec(leaf, &naive_stack, seq, lt);
    let o = exec(&opt, &opt_stack, seq, lt);
    assert_eq!(n, o, "naive/opt disagree on {}", leaf.name);
    assert_eq!(n, expect, "{} expected {expect}", leaf.name);
}

fn leaf<'a>(leaves: &'a [LoweredLeaf], name: &str) -> &'a LoweredLeaf {
    leaves.iter().find(|l| l.name == name).unwrap()
}

fn opt_len(leaf: &LoweredLeaf) -> usize {
    optimize(leaf).script.len()
}

#[test]
fn vault_bare_checks_shrink_and_agree() {
    let (info, env, leaves) = load("vault");
    for (name, age) in [("fallback", 4320u32), ("recover", 12960)] {
        let l = leaf(&leaves, name);
        assert_eq!(l.script.len(), 43, "naive {name}");
        assert_eq!(opt_len(l), 39, "optimized {name} (consume + tail-result)");
        agree(
            &info,
            &env,
            l,
            &[("signature", SatValue::Sig(true))],
            age,
            0,
            true,
        );
        agree(
            &info,
            &env,
            l,
            &[("signature", SatValue::Sig(true))],
            age - 1,
            0,
            false,
        );
        agree(
            &info,
            &env,
            l,
            &[("signature", SatValue::Sig(false))],
            age,
            0,
            false,
        );
    }
}

#[test]
fn htlc_leaves_shrink_and_agree() {
    let (info, env, leaves) = load("htlc");

    let refund = leaf(&leaves, "refund");
    assert_eq!(refund.script.len(), 44);
    assert_eq!(opt_len(refund), 40);
    agree(
        &info,
        &env,
        refund,
        &[("signature", SatValue::Sig(true))],
        0xffff_fffe,
        900_000,
        true,
    );
    agree(
        &info,
        &env,
        refund,
        &[("signature", SatValue::Sig(false))],
        0xffff_fffe,
        900_000,
        false,
    );

    // swap: preimage (used twice) + signature. The corpus hash is a
    // placeholder, so no preimage spends it; check the optimizer shrinks it
    // and still rejects, exactly as the naive form does.
    let swap = leaf(&leaves, "swap");
    assert!(opt_len(swap) < swap.script.len(), "swap should shrink");
    let plan = [
        ("preimage", SatValue::Bytes(vec![0xabu8; 32])),
        ("signature", SatValue::Sig(true)),
    ];
    agree(&info, &env, swap, &plan, 0xffff_fffe, 0, false);
}

/// A real hashlock + signature (controllable hash) exercises the
/// multi-witness consume + tail-result accept path that the corpus swap
/// cannot, because its hash has a known preimage.
#[test]
fn synthetic_hashlock_multiwitness_agrees() {
    let preimage = vec![0x42u8; 32];
    let digest = seal::crypto::sha256::sha256(&preimage);
    let hex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
    let key = "0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c";
    let src = "contract T { extern const k: PublicKey; extern const h: Bytes<32>;
            spend f(p: Bytes<32>, s: Signature) {
                require { sha256(p) == h, k.check(s) }
            } keypath None; }";
    let args = format!(r#"{{"k": "{key}", "h": "0x{hex}"}}"#);
    let (contract, pd) = parser::parse_source(src);
    assert!(pd.is_empty());
    let c = contract.unwrap();
    let (sd, info) = sema::analyze(&c);
    assert!(sd.is_empty());
    let mut env = bind_args(&info, &json::parse(&args).unwrap()).unwrap();
    instantiate(&c, &mut env);
    let (_b, report) = intervals::analyze(&c, &env);
    paths::analyze(&c, &info, &env);
    let (_ld, leaves) = lower(&c, &info, &env, &report);
    let f = leaf(&leaves, "f");
    assert!(opt_len(f) < f.script.len(), "hashlock+sig should shrink");

    let ok = [("p", SatValue::Bytes(preimage)), ("s", SatValue::Sig(true))];
    agree(&info, &env, f, &ok, 0xffff_fffe, 0, true);
    let bad_preimage = [
        ("p", SatValue::Bytes(vec![0x99u8; 32])),
        ("s", SatValue::Sig(true)),
    ];
    agree(&info, &env, f, &bad_preimage, 0xffff_fffe, 0, false);
    let declined = [
        ("p", SatValue::Bytes(vec![0x42u8; 32])),
        ("s", SatValue::Sig(false)),
    ];
    agree(&info, &env, f, &declined, 0xffff_fffe, 0, false);
}

/// Compile an inline contract through the full pipeline (naive leaves).
fn compile_src(src: &str, args: &str) -> (ContractInfo, Env, Vec<LoweredLeaf>) {
    let (contract, pd) = parser::parse_source(src);
    assert!(pd.is_empty(), "parse: {pd:#?}");
    let c = contract.unwrap();
    let (sd, info) = sema::analyze(&c);
    assert!(sd.is_empty(), "sema: {sd:#?}");
    let mut env = bind_args(&info, &json::parse(args).unwrap()).unwrap();
    let id = instantiate(&c, &mut env);
    assert!(
        id.iter().all(|d| d.severity != Severity::Error),
        "inst: {id:#?}"
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
    (info, env, leaves)
}

const KEY: &str = "0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c";

/// Like `compile_src` but tolerates non-error sema diagnostics (e.g. the
/// `sema/sha1` collision-broken warning), asserting only that nothing is an
/// error through the whole pipeline.
fn compile_src_lenient(src: &str, args: &str) -> (ContractInfo, Env, Vec<LoweredLeaf>) {
    let (contract, pd) = parser::parse_source(src);
    assert!(pd.is_empty(), "parse: {pd:#?}");
    let c = contract.unwrap();
    let (sd, info) = sema::analyze(&c);
    assert!(
        sd.iter().all(|d| d.severity != Severity::Error),
        "sema: {sd:#?}"
    );
    let mut env = bind_args(&info, &json::parse(args).unwrap()).unwrap();
    let id = instantiate(&c, &mut env);
    assert!(
        id.iter().all(|d| d.severity != Severity::Error),
        "inst: {id:#?}"
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
    (info, env, leaves)
}

fn sha256_hex(b: &[u8]) -> String {
    seal::crypto::sha256::sha256(b)
        .iter()
        .map(|x| format!("{x:02x}"))
        .collect()
}

/// Two byte parameters in one leaf: two SIZE airlocks plus two reveals, a
/// shape the random fuzzer does not reliably produce.
#[test]
fn two_byte_params_two_airlocks_agree() {
    let p1 = vec![0x11u8; 32];
    let p2 = vec![0x22u8; 32];
    let src = "contract T { extern const k: PublicKey; extern const h1: Bytes<32>; extern const h2: Bytes<32>;
        spend f(a: Bytes<32>, b: Bytes<32>, s: Signature) {
            require { sha256(a) == h1, sha256(b) == h2, k.check(s) }
        } keypath None; }";
    let args = format!(
        r#"{{"k": "{KEY}", "h1": "0x{}", "h2": "0x{}"}}"#,
        sha256_hex(&p1),
        sha256_hex(&p2)
    );
    let (info, env, leaves) = compile_src(src, &args);
    let f = leaf(&leaves, "f");
    assert!(
        opt_len(f) < f.script.len(),
        "two-airlock leaf should shrink"
    );
    agree(
        &info,
        &env,
        f,
        &[
            ("a", SatValue::Bytes(p1.clone())),
            ("b", SatValue::Bytes(p2)),
            ("s", SatValue::Sig(true)),
        ],
        0xffff_fffe,
        0,
        true,
    );
    agree(
        &info,
        &env,
        f,
        &[
            ("a", SatValue::Bytes(p1)),
            ("b", SatValue::Bytes(vec![0x00u8; 32])),
            ("s", SatValue::Sig(true)),
        ],
        0xffff_fffe,
        0,
        false,
    );
}

/// End-to-end OP_SHA1: a `sha1()` hashlock now compiles, executes through the
/// interpreter (which matches Bitcoin Core), and is spendable with the
/// preimage. Previously the interpreter refused OP_SHA1 though the compiler
/// emitted it; this locks the full lower -> satisfy -> interp path for sha1.
#[test]
fn sha1_hashlock_executes_and_is_spendable() {
    let preimage = b"hello".to_vec();
    let digest = seal::crypto::sha1::sha1(&preimage);
    let hex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
    let src = "contract T { extern const k: PublicKey; extern const h: Hash<Sha1>;
        spend f(p: Bytes<5>, s: Signature) {
            require { sha1(p) == h, k.check(s) }
        } keypath None; }";
    let args = format!(r#"{{"k": "{KEY}", "h": "0x{hex}"}}"#);
    // sha1() compiles with the collision-broken warning (not an error), so use
    // the warning-tolerant pipeline.
    let (info, env, leaves) = compile_src_lenient(src, &args);
    let f = leaf(&leaves, "f");
    // Correct preimage + signature spends; a wrong preimage does not.
    agree(
        &info,
        &env,
        f,
        &[("p", SatValue::Bytes(preimage)), ("s", SatValue::Sig(true))],
        0xffff_fffe,
        0,
        true,
    );
    agree(
        &info,
        &env,
        f,
        &[
            ("p", SatValue::Bytes(b"world".to_vec())),
            ("s", SatValue::Sig(true)),
        ],
        0xffff_fffe,
        0,
        false,
    );
}

/// A comparison as the final require item exercises the tail path on a
/// non-CHECKSIG verify; whatever lowering emits, optimized must match naive.
#[test]
fn comparison_last_item_agrees() {
    let src = "contract T { extern const k: PublicKey;
        spend f(relaxed x: Int, s: Signature) {
            require { k.check(s), x in 10..100 }
        } keypath None; }";
    let args = format!(r#"{{"k": "{KEY}"}}"#);
    let (info, env, leaves) = compile_src(src, &args);
    let f = leaf(&leaves, "f");
    let go = |x: i64, expect: bool| {
        agree(
            &info,
            &env,
            f,
            &[("x", SatValue::Int(x)), ("s", SatValue::Sig(true))],
            0xffff_fffe,
            0,
            expect,
        )
    };
    go(50, true);
    go(10, true);
    go(100, false);
    go(9, false);
    agree(
        &info,
        &env,
        f,
        &[("x", SatValue::Int(50)), ("s", SatValue::Sig(false))],
        0xffff_fffe,
        0,
        false,
    );
}

/// A comprehension leaf (balanced IF blocks, no pick inside a branch): the
/// flags and the running count are consumed at last use; naive must agree.
#[test]
fn comprehension_if_leaf_agrees() {
    let src = "contract T { extern const k: PublicKey;
        spend f(relaxed flags: [Bool; 6], s: Signature) {
            require { sum(b in flags where b => 1) >= 3, k.check(s) }
        } keypath None; }";
    let args = format!(r#"{{"k": "{KEY}"}}"#);
    let (info, env, leaves) = compile_src(src, &args);
    let f = leaf(&leaves, "f");
    assert!(
        opt_len(f) < f.script.len(),
        "comprehension leaf should shrink"
    );
    let flags = |n: usize| SatValue::Array((0..6).map(|i| SatValue::Bool(i < n)).collect());
    agree(
        &info,
        &env,
        f,
        &[("flags", flags(3)), ("s", SatValue::Sig(true))],
        0xffff_fffe,
        0,
        true,
    );
    agree(
        &info,
        &env,
        f,
        &[("flags", flags(5)), ("s", SatValue::Sig(true))],
        0xffff_fffe,
        0,
        true,
    );
    agree(
        &info,
        &env,
        f,
        &[("flags", flags(2)), ("s", SatValue::Sig(true))],
        0xffff_fffe,
        0,
        false,
    );
    agree(
        &info,
        &env,
        f,
        &[("flags", flags(3)), ("s", SatValue::Sig(false))],
        0xffff_fffe,
        0,
        false,
    );
}

/// `count(... where ...)` lowers to NESTED IF blocks (where-guard then the
/// count increment). The optimizer must handle the nesting and agree.
#[test]
fn count_nested_if_leaf_agrees() {
    let src = "contract T { extern const k: PublicKey;
        spend f(relaxed flags: [Bool; 6], s: Signature) {
            require { count(b in flags where b => true) >= 3, k.check(s) }
        } keypath None; }";
    let args = format!(r#"{{"k": "{KEY}"}}"#);
    let (info, env, leaves) = compile_src(src, &args);
    let f = leaf(&leaves, "f");
    assert!(opt_len(f) < f.script.len(), "count leaf should shrink");
    let flags = |n: usize| SatValue::Array((0..6).map(|i| SatValue::Bool(i < n)).collect());
    agree(
        &info,
        &env,
        f,
        &[("flags", flags(3)), ("s", SatValue::Sig(true))],
        0xffff_fffe,
        0,
        true,
    );
    agree(
        &info,
        &env,
        f,
        &[("flags", flags(2)), ("s", SatValue::Sig(true))],
        0xffff_fffe,
        0,
        false,
    );
}

/// `all`/`any` put their bools in value position, which get a DUP airlock. The
/// optimizer now MODELS DUP, so it schedules these leaves instead of bailing;
/// the rewrite must never grow the leaf and must preserve behavior (checked
/// here by agree(), and exhaustively by the certifier's all/any Certified test).
#[test]
fn all_and_any_leaves_optimize_and_agree() {
    let args = format!(r#"{{"k": "{KEY}"}}"#);
    let flags4 = |n: usize| SatValue::Array((0..4).map(|i| SatValue::Bool(i < n)).collect());

    let s_all = "contract T { extern const k: PublicKey;
        spend f(relaxed flags: [Bool; 4], s: Signature) {
            require { all(b in flags => b), k.check(s) }
        } keypath None; }";
    let (info, env, leaves) = compile_src(s_all, &args);
    let f = leaf(&leaves, "f");
    assert!(opt_len(f) <= f.script.len(), "all must never grow");
    agree(
        &info,
        &env,
        f,
        &[("flags", flags4(4)), ("s", SatValue::Sig(true))],
        0xffff_fffe,
        0,
        true,
    );
    agree(
        &info,
        &env,
        f,
        &[("flags", flags4(3)), ("s", SatValue::Sig(true))],
        0xffff_fffe,
        0,
        false,
    );

    let s_any = "contract T { extern const k: PublicKey;
        spend f(relaxed flags: [Bool; 4], s: Signature) {
            require { any(b in flags => b), k.check(s) }
        } keypath None; }";
    let (info2, env2, leaves2) = compile_src(s_any, &args);
    let g = leaf(&leaves2, "f");
    assert!(opt_len(g) <= g.script.len(), "any must never grow");
    agree(
        &info2,
        &env2,
        g,
        &[("flags", flags4(1)), ("s", SatValue::Sig(true))],
        0xffff_fffe,
        0,
        true,
    );
    agree(
        &info2,
        &env2,
        g,
        &[("flags", flags4(0)), ("s", SatValue::Sig(true))],
        0xffff_fffe,
        0,
        false,
    );
}

/// `select` lowers to IF/ELSE; the optimizer bails on ELSE (left naive). The
/// witness used inside the branches stays a copy, so behavior is preserved.
#[test]
fn select_else_leaf_bails_to_naive() {
    let src = "contract T { extern const k: PublicKey;
        spend f(relaxed flag: Bool, relaxed x: Int, s: Signature) {
            require { x in 0..100, select(flag, then: x, else: 0) >= 10, k.check(s) }
        } keypath None; }";
    let args = format!(r#"{{"k": "{KEY}"}}"#);
    let (info, env, leaves) = compile_src(src, &args);
    let f = leaf(&leaves, "f");
    assert_eq!(
        opt_len(f),
        f.script.len(),
        "select (ELSE) should stay naive"
    );
    let go = |flag: bool, x: i64, expect: bool| {
        agree(
            &info,
            &env,
            f,
            &[
                ("flag", SatValue::Bool(flag)),
                ("x", SatValue::Int(x)),
                ("s", SatValue::Sig(true)),
            ],
            0xffff_fffe,
            0,
            expect,
        )
    };
    go(true, 50, true);
    go(true, 5, false);
    go(false, 50, false);
}

/// Dead-constraint elimination: mirage stacks four always-true checks the
/// interval engine proves under `bid in 0..1000`. They vanish, leaving the one
/// real range and the signature. The real range must still be enforced.
#[test]
fn mirage_dead_constraints_are_eliminated() {
    let (info, env, leaves) = load("mirage");
    let claim = leaf(&leaves, "claim");
    assert_eq!(
        opt_len(claim),
        40,
        "dead checks dropped + reverse-consumption layout drops the stray ROLL: 75 -> 40"
    );
    let go = |bid: i64, sig: bool, expect: bool| {
        agree(
            &info,
            &env,
            claim,
            &[("bid", SatValue::Int(bid)), ("s", SatValue::Sig(sig))],
            0xffff_fffe,
            0,
            expect,
        )
    };
    go(500, true, true); // in range and signed: spends
    go(0, true, true); // lower boundary
    go(1000, true, false); // out of range: the surviving real range rejects
    go(500, false, false); // declined signature
}

#[test]
fn multisig_chain_is_already_optimal() {
    let (info, env, leaves) = load("multisig");
    let f = leaf(&leaves, "fallback");
    // The CHECKSIGADD chain has no PICK and ends in a comparison, so the
    // optimizer must leave it byte-identical.
    assert_eq!(opt_len(f), f.script.len(), "multisig must not change");
    let sigs = |b: [bool; 3]| SatValue::Array(b.iter().map(|&x| SatValue::Sig(x)).collect());
    agree(
        &info,
        &env,
        f,
        &[("sigs", sigs([true, true, false]))],
        0xffff_fffe,
        0,
        true,
    );
    agree(
        &info,
        &env,
        f,
        &[("sigs", sigs([true, false, false]))],
        0xffff_fffe,
        0,
        false,
    );
}

#[test]
fn cat_bounty_if_leaf_optimizes_and_agrees() {
    let (info, env, leaves) = load("cat_bounty");
    let claim = leaf(&leaves, "claim");
    // The classifier is a balanced-IF leaf with no pick inside a branch, so it
    // optimizes: the drawing bits and the score are consumed at last use and
    // the trailing cleanup goes.
    assert!(opt_len(claim) < claim.script.len(), "IF leaf should shrink");
    let weights = match &env["weights"] {
        ConstValue::Array(items) => items
            .iter()
            .map(|v| match v {
                ConstValue::Int(n) => *n,
                _ => panic!(),
            })
            .collect::<Vec<_>>(),
        _ => panic!(),
    };
    let winning = SatValue::Array((0..784).map(|i| SatValue::Bool(weights[i] > 0)).collect());
    agree(
        &info,
        &env,
        claim,
        &[("drawing", winning), ("signature", SatValue::Sig(true))],
        0xffff_fffe,
        0,
        true,
    );
    // A blank drawing scores below threshold: rejected by both forms.
    let blank = SatValue::Array((0..784).map(|_| SatValue::Bool(false)).collect());
    agree(
        &info,
        &env,
        claim,
        &[("drawing", blank), ("signature", SatValue::Sig(true))],
        0xffff_fffe,
        0,
        false,
    );
}

/// quorum tests one eight-vote tally against two bounds (`>= 3`, `<= 6`). The
/// optimizer: drops the const-body count's inner IF, lifts each vote with a SWAP
/// (consume-at-last-use, no DROP cleanup tail), and FUSES the two bounds on the
/// shared tally into a single `3 7 WITHIN VERIFY` (so the CSE DUP is gone too).
/// 170 -> 71. Both bounds must still be enforced (the fused WITHIN must not drop
/// a check), checked exhaustively over all 512 witnesses by the certifier.
#[test]
fn quorum_cse_shares_the_tally_and_enforces_both_bounds() {
    let (info, env, leaves) = load("quorum");
    let act = leaf(&leaves, "act");
    assert!(
        opt_len(act) < act.script.len(),
        "the optimizer must shrink the leaf"
    );
    assert_eq!(
        opt_len(act),
        71,
        "SWAP-scheduled tally + WITHIN-fused bounds, no inner IF, no DUP, no tail"
    );
    let votes = |n: usize| SatValue::Array((0..8).map(|i| SatValue::Bool(i < n)).collect());
    let go = |n: usize, sig: bool, expect: bool| {
        agree(
            &info,
            &env,
            act,
            &[("votes", votes(n)), ("s", SatValue::Sig(sig))],
            0xffff_fffe,
            0,
            expect,
        );
    };
    go(3, true, true); // lower bound
    go(4, true, true);
    go(6, true, true); // upper bound
    go(2, true, false); // below the lower bound: the kept `>= 3` still rejects
    go(7, true, false); // above the upper bound: the kept `<= 6` still rejects
    go(8, true, false);
    go(5, false, false); // declined signature
}

/// CSE is not count-specific: a `sum` subject shared by two adjacent bounds
/// is computed once too. Exercises the mechanism on a different aggregate.
#[test]
fn cse_generalizes_to_a_shared_sum_subject() {
    let src = "contract T { extern const k: PublicKey;
        spend f(relaxed flags: [Bool; 5], s: Signature) {
            require {
                sum(b in flags where b => 1) >= 2,
                sum(b in flags where b => 1) <= 4,
                k.check(s)
            }
        } keypath None; }";
    let args = format!(r#"{{"k": "{KEY}"}}"#);
    let (info, env, leaves) = compile_src(src, &args);
    let f = leaf(&leaves, "f");
    assert!(
        opt_len(f) < f.script.len(),
        "shared sum subject should shrink"
    );
    let flags = |n: usize| SatValue::Array((0..5).map(|i| SatValue::Bool(i < n)).collect());
    let go = |n: usize, expect: bool| {
        agree(
            &info,
            &env,
            f,
            &[("flags", flags(n)), ("s", SatValue::Sig(true))],
            0xffff_fffe,
            0,
            expect,
        );
    };
    go(2, true);
    go(3, true);
    go(4, true);
    go(1, false); // below 2
    go(5, false); // above 4
    agree(
        &info,
        &env,
        f,
        &[("flags", flags(3)), ("s", SatValue::Sig(false))],
        0xffff_fffe,
        0,
        false,
    );
}

/// A run of three adjacent same-subject items (mixed `>=`, `<=`, `!=`) shares
/// one tally with two DUPs; every bound, including the final `!=`, stays
/// enforced. Exercises k>=3 runs and the Ne operator, which the two-bound
/// tests and fuzz stage7 do not reach. The `count == 4` probe is the headline:
/// if the third predicate were dropped, it would wrongly accept.
#[test]
fn cse_three_item_run_with_ne_enforces_every_bound() {
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
    let (info, env, leaves) = compile_src(src, &args);
    let f = leaf(&leaves, "f");
    assert!(opt_len(f) < f.script.len(), "3-item run should shrink");
    let votes = |n: usize| SatValue::Array((0..8).map(|i| SatValue::Bool(i < n)).collect());
    let go = |n: usize, expect: bool| {
        agree(
            &info,
            &env,
            f,
            &[("votes", votes(n)), ("s", SatValue::Sig(true))],
            0xffff_fffe,
            0,
            expect,
        );
    };
    // accept iff 3 <= count <= 6 AND count != 4  ->  {3, 5, 6}
    go(3, true);
    go(5, true);
    go(6, true);
    go(4, false); // the `!= 4` bound (the third predicate) must still reject
    go(2, false); // below `>= 3`
    go(7, false); // above `<= 6`
    agree(
        &info,
        &env,
        f,
        &[("votes", votes(5)), ("s", SatValue::Sig(false))],
        0xffff_fffe,
        0,
        false,
    );
}

/// The pick-in-predicate guard: a witness-dependent bound makes the
/// comparison read the stack by depth, so a kept copy of the subject would
/// shift that read onto the wrong slot. CSE must decline; the leaf computes
/// the tally twice, and correctness here is what guards the guard (were CSE
/// to fire, the bound would read the wrong value and `agree` would fail).
#[test]
fn cse_skips_a_subject_when_the_bound_is_witness_dependent() {
    let src = "contract T { extern const k: PublicKey;
        spend f(relaxed votes: [Bool; 4], relaxed lo: Int, relaxed hi: Int, s: Signature) {
            require {
                count(v in votes where v => true) >= lo,
                count(v in votes where v => true) <= hi,
                k.check(s)
            }
        } keypath None; }";
    let args = format!(r#"{{"k": "{KEY}"}}"#);
    let (info, env, leaves) = compile_src(src, &args);
    let f = leaf(&leaves, "f");
    let votes = |n: usize| SatValue::Array((0..4).map(|i| SatValue::Bool(i < n)).collect());
    let go = |n: usize, lo: i64, hi: i64, expect: bool| {
        agree(
            &info,
            &env,
            f,
            &[
                ("votes", votes(n)),
                ("lo", SatValue::Int(lo)),
                ("hi", SatValue::Int(hi)),
                ("s", SatValue::Sig(true)),
            ],
            0xffff_fffe,
            0,
            expect,
        );
    };
    go(2, 1, 3, true); // 1 <= 2 <= 3
    go(2, 3, 4, false); // count below lo
    go(2, 0, 1, false); // count above hi
    go(4, 0, 4, true); // upper boundary
}

/// A single comparison in tail position lowers (naively) to `... cmp VERIFY`
/// like any item: VERIFY aborts on a false comparison, so the bound IS
/// enforced -- the spend does not "always succeed". The optimizer's
/// tail-result step later turns the final VERIFY into the leaf's own bool (a
/// byte win, not a correctness change). Guards against reading VERIFY as a
/// bare pop.
#[test]
fn tail_single_comparison_enforces_its_bound() {
    let src = "contract T { extern const k: PublicKey;
        spend f(relaxed x: Int, s: Signature) {
            require { k.check(s), x >= 50 }
        } keypath None; }";
    let args = format!(r#"{{"k": "{KEY}"}}"#);
    let (info, env, leaves) = compile_src(src, &args);
    let f = leaf(&leaves, "f");
    let go = |x: i64, expect: bool| {
        agree(
            &info,
            &env,
            f,
            &[("x", SatValue::Int(x)), ("s", SatValue::Sig(true))],
            0xffff_fffe,
            0,
            expect,
        );
    };
    go(50, true); // boundary 50 >= 50
    go(100, true);
    go(49, false); // below the bound: VERIFY aborts, not an automatic success
    agree(
        &info,
        &env,
        f,
        &[("x", SatValue::Int(50)), ("s", SatValue::Sig(false))],
        0xffff_fffe,
        0,
        false,
    );
}

/// Totality: a malformed `cse_subjects` annotation (out of bounds, inverted,
/// descending, overlapping) must make CSE fall back, never panic. Lowering
/// never produces such a set, but the optimizer must be total regardless.
#[test]
fn cse_falls_back_on_malformed_subjects_without_panicking() {
    use seal::codegen::lower::CseSubject;
    let (_info, _env, leaves) = load("quorum");
    let base = leaf(&leaves, "act").clone();
    let n = base.ops.len();
    let bogus_sets = vec![
        vec![CseSubject {
            subject: (n + 5, n + 10),
            item_end: n + 20,
        }], // out of bounds
        vec![
            CseSubject {
                subject: (10, 5),
                item_end: 20,
            }, // subject.0 > subject.1
            CseSubject {
                subject: (30, 40),
                item_end: 25,
            }, // item_end < subject.1
        ],
        vec![
            CseSubject {
                subject: (40, 50),
                item_end: 60,
            }, // descending / overlapping
            CseSubject {
                subject: (0, 5),
                item_end: 10,
            },
        ],
        vec![CseSubject {
            subject: (0, n),
            item_end: n + 1,
        }], // item_end past end
    ];
    for set in bogus_sets {
        let mut l = base.clone();
        l.cse_subjects = set;
        let opt = optimize(&l); // must not panic
        assert!(!opt.script.is_empty(), "optimize produced an empty leaf");
    }
}
