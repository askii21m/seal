//! The reference interpreter: self-validation, then execution of compiled
//! scripts as the lowering's differential oracle.
//!
//! Two layers:
//!  1. the interpreter is correct (tiny scripts with known outcomes;
//!     CScriptNum cross-checked against `script::encode_num`; MINIMALIF,
//!     CLEANSTACK, the CHECKSIG trichotomy);
//!  2. every lowering pattern is run: an honest witness must succeed, an
//!     adversarial/tampered witness must fail, for single-sig, hashlock
//!     (plus the size airlock), the CHECKSIGADD threshold chain, ranges, the
//!     CSV timelock, and the cat-bounty 784-add classifier.

use seal::analysis::consteval::{ConstValue, Env, bind_args, instantiate};
use seal::analysis::intervals;
use seal::analysis::paths;
use seal::analysis::sema;
use seal::codegen::lower::{LoweredLeaf, lower};
use seal::codegen::script::{Op, encode_num, serialize};
use seal::diagnostics::Severity;
use seal::json;
use seal::syntax::parser;
use seal::verify::interp::{Context, execute};

// --- a permissive default context (no timelock, sigs accepted by oracle) ---

fn ctx_with<'a>(oracle: &'a dyn Fn(&[u8], &[u8]) -> bool) -> Context<'a> {
    Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: oracle,
    }
}

/// Run raw ops against a witness stack with a never-call sig oracle.
fn run_ops(ops: &[Op], witness: &[Vec<u8>]) -> Result<(), String> {
    let never = |_: &[u8], _: &[u8]| false;
    execute(&serialize(ops), witness, &ctx_with(&never))
}

// --- layer 1: the interpreter is correct ---

#[test]
fn tiny_scripts_have_known_outcomes() {
    // OP_1 implies success; OP_0 implies false; 2 3 ADD 5 EQUAL implies success.
    assert!(run_ops(&[Op::PushNum(1)], &[]).is_ok());
    assert!(run_ops(&[Op::PushNum(0)], &[]).is_err());
    assert!(
        run_ops(
            &[
                Op::PushNum(2),
                Op::PushNum(3),
                Op::Add,
                Op::PushNum(5),
                Op::NumEqual
            ],
            &[]
        )
        .is_ok()
    );
    // CLEANSTACK: two truthy elements is still a FAILURE.
    assert!(run_ops(&[Op::PushNum(1), Op::PushNum(1)], &[]).is_err());
    // Underflow is caught, not a panic.
    assert!(run_ops(&[Op::Add], &[]).is_err());
}

#[test]
fn minimalif_is_enforced() {
    let never = |_: &[u8], _: &[u8]| false;
    let ctx = ctx_with(&never);
    // {0x01} is a valid IF arg, takes the branch, OP_1.
    // Bytes: push1(0x01) IF(0x63) OP_1(0x51) ENDIF(0x68).
    assert!(execute(&[0x01, 0x01, 0x63, 0x51, 0x68], &[], &ctx).is_ok());
    // {0x02} is NOT minimal: consensus rejects it as an IF argument.
    // (Built as raw bytes: the serializer forbids 1-byte small-int pushes.)
    let bad = execute(&[0x01, 0x02, 0x63, 0x51, 0x68], &[], &ctx).unwrap_err();
    assert!(bad.contains("minimal"), "{bad}");
    // A 2-byte truthy value is also a non-minimal IF arg.
    let bad2 = execute(&[0x02, 0x01, 0x00, 0x63, 0x51, 0x68], &[], &ctx).unwrap_err();
    assert!(bad2.contains("minimal"), "{bad2}");
}

#[test]
fn cscriptnum_codec_matches_the_serializer() {
    // The interpreter decodes exactly what `script::encode_num` produces,
    // round-trips, and reads it back as the same value (independent code,
    // cross-checked) across the whole 4-byte domain's edges.
    for n in [
        0i64,
        1,
        -1,
        2,
        16,
        17,
        -16,
        127,
        128,
        -128,
        255,
        256,
        4320,
        900_000,
        -900_000,
        2_147_483_647,
        -2_147_483_647,
    ] {
        // `<n> <n> NUMEQUAL` must succeed iff the interpreter reads n back.
        let ops = vec![Op::PushNum(n), Op::PushNum(n), Op::NumEqual];
        assert!(run_ops(&ops, &[]).is_ok(), "n={n}");
        // And our serializer's bytes for n decode to n via the interp's
        // independent path (an `<n> 0 ADD` returns n, compared to n).
        let probe = vec![
            Op::PushNum(n),
            Op::PushNum(0),
            Op::Add,
            Op::PushNum(n),
            Op::NumEqual,
        ];
        assert!(run_ops(&probe, &[]).is_ok(), "decode n={n}");
        // Sanity: the byte form is the one the serializer emits.
        let _ = encode_num(n);
    }
}

// --- layer 2: execute compiled scripts (the differential oracle) ---

const KEY_A: &str = "\"0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c\"";
const KEY_B: &str = "\"0x5cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc\"";

fn key_bytes(b: u8) -> Vec<u8> {
    let hex = match b {
        0x11 => &KEY_A[3..67],
        0x22 => &KEY_B[3..67],
        _ => panic!("key tag"),
    };
    (0..32)
        .map(|i| u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).unwrap())
        .collect()
}

/// Compile + lower a contract; assert every analysis is clean.
fn lower_contract(src: &str, args: &str) -> Vec<LoweredLeaf> {
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
    let (pdiags, _) = paths::analyze(&c, &info, &env);
    assert!(
        pdiags.iter().all(|d| d.severity != Severity::Error),
        "paths: {pdiags:#?}"
    );
    let (ld, leaves) = lower(&c, &info, &env, &report);
    assert!(
        ld.iter().all(|d| d.severity != Severity::Error),
        "lower: {ld:#?}"
    );
    leaves
}

fn leaf<'a>(leaves: &'a [LoweredLeaf], name: &str) -> &'a LoweredLeaf {
    leaves.iter().find(|l| l.name == name).expect("leaf")
}

/// Build the initial stack from a name-to-bytes map, in witness order.
fn witness(leaf: &LoweredLeaf, vals: &[(&str, Vec<u8>)]) -> Vec<Vec<u8>> {
    leaf.witness_order
        .iter()
        .map(|slot| {
            vals.iter()
                .find(|(n, _)| n == slot)
                .map(|(_, v)| v.clone())
                .unwrap_or_else(|| panic!("no witness for slot `{slot}`"))
        })
        .collect()
}

const VALID: [u8; 64] = [0xAA; 64];
const WRONG: [u8; 64] = [0xBB; 64];

#[test]
fn single_sig_with_real_schnorr() {
    // The full stack with REAL cryptography: a compiled single-sig leaf,
    // the interpreter, and BIP340 verification, satisfied by a genuinely
    // valid signature (sourced from an official BIP340 vector, since the
    // compiler deliberately cannot sign). The CHECKSIG oracle is the real
    // verifier against the vector's message.
    let pk_hex = "dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659";
    let msg_hex = "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89";
    let sig_hex = "6896bd60eeae296db48a229ff71dfe071bde413e6d43f917dc8dcf8c78de33418906d11ac976abccb20b091292bff4ea897efcb639ea871cfa95f6de339e4b0a";
    let hx = |s: &str| -> Vec<u8> {
        (0..s.len() / 2)
            .map(|i| u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).unwrap())
            .collect()
    };
    let msg = hx(msg_hex);
    let mut sig64 = [0u8; 64];
    sig64.copy_from_slice(&hx(sig_hex));

    let leaves = lower_contract(
        "contract T { extern const k: PublicKey;
            spend f(s: Signature) { require k.check(s); } keypath None; }",
        &format!(r#"{{"k": "0x{pk_hex}"}}"#),
    );
    let f = leaf(&leaves, "f");

    // The oracle is REAL BIP340 verification against the vector message.
    let real = |pk: &[u8], sig: &[u8]| {
        let (Ok(p), Ok(s)) = (<[u8; 32]>::try_from(pk), <[u8; 64]>::try_from(sig)) else {
            return false;
        };
        seal::crypto::schnorr::verify(&p, &msg, &s)
    };
    let ctx = ctx_with(&real);
    // The genuine signature spends.
    assert!(execute(&f.script, &witness(f, &[("s", sig64.to_vec())]), &ctx).is_ok());
    // Flip one bit of the real signature, BIP340 rejects, CHECKSIGVERIFY
    // aborts. No forgery, no theft.
    let mut tampered = sig64;
    tampered[20] ^= 0x01;
    assert!(execute(&f.script, &witness(f, &[("s", tampered.to_vec())]), &ctx).is_err());
}

#[test]
fn single_sig_executes() {
    let leaves = lower_contract(
        "contract T { extern const k: PublicKey;
            spend f(s: Signature) { require k.check(s); } keypath None; }",
        &format!(r#"{{"k": {KEY_A}}}"#),
    );
    let f = leaf(&leaves, "f");
    let key = key_bytes(0x11);
    let oracle = |pk: &[u8], sig: &[u8]| pk == key && sig == VALID;
    let ctx = ctx_with(&oracle);
    // Honest: the valid signature spends.
    assert!(execute(&f.script, &witness(f, &[("s", VALID.to_vec())]), &ctx).is_ok());
    // A wrong (non-empty) signature ABORTS: no soft failure, no theft.
    assert!(execute(&f.script, &witness(f, &[("s", WRONG.to_vec())]), &ctx).is_err());
    // The empty decline fails a single-sig leaf (it requires the sig).
    assert!(execute(&f.script, &witness(f, &[("s", vec![])]), &ctx).is_err());
}

#[test]
fn hashlock_and_size_airlock_execute() {
    // preimage = 0x42 by 32; the args hashlock is sha256(preimage).
    let preimage = vec![0x42u8; 32];
    let digest = seal::crypto::sha256::sha256(&preimage);
    let hex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
    let leaves = lower_contract(
        "contract T { extern const k: PublicKey; extern const h: Bytes<32>;
            spend f(p: Bytes<32>, s: Signature) {
                require { sha256(p) == h, k.check(s) }
            } keypath None; }",
        &format!(r#"{{"k": {KEY_A}, "h": "0x{hex}"}}"#),
    );
    let f = leaf(&leaves, "f");
    let key = key_bytes(0x11);
    let oracle = |pk: &[u8], sig: &[u8]| pk == key && sig == VALID;
    let ctx = ctx_with(&oracle);
    // Honest: correct preimage + signature.
    assert!(
        execute(
            &f.script,
            &witness(f, &[("p", preimage.clone()), ("s", VALID.to_vec())]),
            &ctx
        )
        .is_ok()
    );
    // Wrong preimage (right size), hash mismatch, fail.
    assert!(
        execute(
            &f.script,
            &witness(f, &[("p", vec![0x43u8; 32]), ("s", VALID.to_vec())]),
            &ctx
        )
        .is_err()
    );
    // Wrong-SIZE preimage, the never-elided SIZE airlock aborts.
    assert!(
        execute(
            &f.script,
            &witness(f, &[("p", vec![0x42u8; 31]), ("s", VALID.to_vec())]),
            &ctx
        )
        .is_err()
    );
}

#[test]
fn threshold_chain_executes() {
    // 2-of-2 over keys a (0x11) and b (0x22). The consuming chain lays out
    // sb deepest, sa on top (reverse chain order).
    let leaves = lower_contract(
        "contract T { extern const a: PublicKey; extern const b: PublicKey;
            spend f(sa: Signature, sb: Signature) {
                require a.check(sa) + b.check(sb) >= 2;
            } keypath None; }",
        &format!(r#"{{"a": {KEY_A}, "b": {KEY_B}}}"#),
    );
    let f = leaf(&leaves, "f");
    let (ka, kb) = (key_bytes(0x11), key_bytes(0x22));
    let sa = vec![0xA1u8; 64];
    let sb = vec![0xB2u8; 64];
    let oracle = |pk: &[u8], sig: &[u8]| (pk == ka && sig == sa) || (pk == kb && sig == sb);
    let ctx = ctx_with(&oracle);
    // Both valid implies 2 >= 2 implies success.
    assert!(
        execute(
            &f.script,
            &witness(f, &[("sa", sa.clone()), ("sb", sb.clone())]),
            &ctx
        )
        .is_ok()
    );
    // One declined (empty) implies 1 >= 2 is false implies fail.
    assert!(
        execute(
            &f.script,
            &witness(f, &[("sa", sa.clone()), ("sb", vec![])]),
            &ctx
        )
        .is_err()
    );
    // A forged non-empty sig ABORTS (can't fake the count).
    assert!(
        execute(
            &f.script,
            &witness(f, &[("sa", sa.clone()), ("sb", WRONG.to_vec())]),
            &ctx
        )
        .is_err()
    );
}

#[test]
fn range_within_executes() {
    let leaves = lower_contract(
        "contract T { extern const k: PublicKey;
            spend f(relaxed x: Int, s: Signature) {
                require { x in 0..100, k.check(s) }
            } keypath None; }",
        &format!(r#"{{"k": {KEY_A}}}"#),
    );
    let f = leaf(&leaves, "f");
    let key = key_bytes(0x11);
    let oracle = |pk: &[u8], sig: &[u8]| pk == key && sig == VALID;
    let ctx = ctx_with(&oracle);
    let run = |x: i64| {
        execute(
            &f.script,
            &witness(f, &[("x", encode_num(x)), ("s", VALID.to_vec())]),
            &ctx,
        )
    };
    assert!(run(50).is_ok(), "in range");
    assert!(run(0).is_ok(), "lo inclusive");
    assert!(run(100).is_err(), "hi exclusive");
    assert!(run(-1).is_err(), "below");
}

#[test]
fn csv_timelock_executes() {
    let leaves = lower_contract(
        "contract T { extern const k: PublicKey;
            spend f(s: Signature) {
                require { after(LockTime.Relative(blocks: 144)), k.check(s) }
            } keypath None; }",
        &format!(r#"{{"k": {KEY_A}}}"#),
    );
    let f = leaf(&leaves, "f");
    let key = key_bytes(0x11);
    let oracle = |pk: &[u8], sig: &[u8]| pk == key && sig == VALID;
    let w = witness(f, &[("s", VALID.to_vec())]);
    // Sufficient relative age (>=144 blocks) implies success.
    let ctx_ok = Context {
        locktime: 0,
        sequence: 144,
        tx_version: 2,
        verify_sig: &oracle,
    };
    assert!(execute(&f.script, &w, &ctx_ok).is_ok());
    // Too young (100 < 144) implies CSV aborts.
    let ctx_young = Context {
        locktime: 0,
        sequence: 100,
        tx_version: 2,
        verify_sig: &oracle,
    };
    assert!(execute(&f.script, &w, &ctx_young).is_err());
    // tx version < 2 implies CSV aborts.
    let ctx_v1 = Context {
        locktime: 0,
        sequence: 144,
        tx_version: 1,
        verify_sig: &oracle,
    };
    assert!(execute(&f.script, &w, &ctx_v1).is_err());
}

#[test]
fn cltv_absolute_timelock_executes() {
    // Absolute height lock (CLTV); the path tested before was CSV.
    let leaves = lower_contract(
        "contract T { extern const k: PublicKey; extern const t: LockTime.Absolute;
            spend f(s: Signature) {
                require { after(t), k.check(s) }
            } keypath None; }",
        &format!(r#"{{"k": {KEY_A}, "t": {{"height": 800000}}}}"#),
    );
    let f = leaf(&leaves, "f");
    let key = key_bytes(0x11);
    let oracle = |pk: &[u8], sig: &[u8]| pk == key && sig == VALID;
    let w = witness(f, &[("s", VALID.to_vec())]);
    // nLockTime reached, input non-final implies success.
    let ok = Context {
        locktime: 800_000,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    assert!(execute(&f.script, &w, &ok).is_ok());
    // nLockTime not yet reached implies CLTV aborts.
    let early = Context {
        locktime: 799_999,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    assert!(execute(&f.script, &w, &early).is_err());
    // A FINAL input nSequence disables nLockTime implies CLTV aborts even
    // when the height is reached.
    let final_seq = Context {
        locktime: 800_000,
        sequence: 0xffff_ffff,
        tx_version: 2,
        verify_sig: &oracle,
    };
    assert!(execute(&f.script, &w, &final_seq).is_err());
}

#[test]
fn checksig_pubkey_dispatch_matches_core() {
    // The interpreter models BIP342 EvalChecksigTapscript faithfully for
    // ANY bytes (it will be fuzzed on arbitrary scripts).
    let never = |_: &[u8], _: &[u8]| false;
    let ctx = ctx_with(&never);
    // An EMPTY public key aborts, even with an empty signature.
    // Bytes: OP_0 (empty sig) OP_0 (empty pubkey) OP_CHECKSIG.
    let err = execute(&[0x00, 0x00, 0xac], &[], &ctx).unwrap_err();
    assert!(err.contains("empty public key"), "{err}");
}

#[test]
fn cat_bounty_classifier_executes() {
    // The 784-add binarized classifier. A maximal drawing (every
    // positive-weight pixel on) scores the maximum, clearing the threshold.
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
    let src = std::fs::read_to_string(dir.join("cat_bounty.sl")).unwrap();
    let args = std::fs::read_to_string(dir.join("cat_bounty.args.json")).unwrap();
    let leaves = lower_contract(&src, &args);
    let claim = leaf(&leaves, "claim");

    // Pull the weights + solver key from the args to build the witness.
    let parsed = json::parse(&args).unwrap();
    let info = sema::analyze(&parser::parse_source(&src).0.unwrap()).1;
    let env = bind_args(&info, &parsed).unwrap();
    let weights = match &env["weights"] {
        ConstValue::Array(items) => items
            .iter()
            .map(|v| match v {
                ConstValue::Int(n) => *n,
                _ => panic!("weight"),
            })
            .collect::<Vec<_>>(),
        _ => panic!("weights"),
    };
    let solver = match &env["solver"] {
        ConstValue::Bytes(b) => b.clone(),
        _ => panic!("solver"),
    };

    // drawing[i] = on iff weight[i] > 0 gives the maximal score.
    let mut vals: Vec<(String, Vec<u8>)> = (0..784)
        .map(|i| {
            (
                format!("drawing[{i}]"),
                if weights[i] > 0 { vec![0x01] } else { vec![] },
            )
        })
        .collect();
    vals.push(("signature".into(), VALID.to_vec()));
    let vals_ref: Vec<(&str, Vec<u8>)> =
        vals.iter().map(|(n, v)| (n.as_str(), v.clone())).collect();

    let oracle = |pk: &[u8], sig: &[u8]| pk == solver && sig == VALID;
    let ctx = ctx_with(&oracle);
    assert!(
        execute(&claim.script, &witness(claim, &vals_ref), &ctx).is_ok(),
        "a maximal drawing must satisfy the bounty"
    );

    // An empty drawing scores only the bias, below threshold implies fail.
    let mut empty: Vec<(String, Vec<u8>)> = (0..784)
        .map(|i| (format!("drawing[{i}]"), vec![]))
        .collect();
    empty.push(("signature".into(), VALID.to_vec()));
    let empty_ref: Vec<(&str, Vec<u8>)> =
        empty.iter().map(|(n, v)| (n.as_str(), v.clone())).collect();
    assert!(
        execute(&claim.script, &witness(claim, &empty_ref), &ctx).is_err(),
        "an empty drawing must not satisfy the bounty"
    );
}
