//! Lowering tests: golden op sequences for every require shape, the airlock
//! rules, comprehension unrolling, witness layout, and the corpus, lowered
//! and structurally verified.
//!
//! Goldens assert on `Op` vectors (exact, readable); bigger leaves assert
//! key properties plus the poison gate. Lowering runs only on code that
//! passed every analysis (mirroring the driver), so each fixture is fully
//! legal.

use seal::analysis::consteval::{Env, bind_args, instantiate};
use seal::analysis::intervals;
use seal::analysis::paths;
use seal::analysis::sema;
use seal::codegen::lower::{LoweredLeaf, lower};
use seal::codegen::optimize::optimize;
use seal::codegen::script::{Op, asm, verify_script};
use seal::diagnostics::{Diagnostic, Severity};
use seal::json;
use seal::syntax::parser::parse_source;

/// Full pipeline through the analyses (all asserted clean), then lowering.
fn run(src: &str, args: &str) -> (Vec<Diagnostic>, Vec<LoweredLeaf>) {
    let (contract, pd) = parse_source(src);
    assert!(pd.is_empty(), "parse: {pd:#?}");
    let c = contract.expect("contract");
    let (sd, info) = sema::analyze(&c);
    assert!(sd.is_empty(), "sema: {sd:#?}");
    let mut env: Env = bind_args(&info, &json::parse(args).expect("json"))
        .unwrap_or_else(|e| panic!("bind: {e:#?}"));
    let id = instantiate(&c, &mut env);
    assert!(id.is_empty(), "instantiate: {id:#?}");
    let (g1, report) = intervals::analyze(&c, &env);
    assert!(g1.is_empty(), "G1: {g1:#?}");
    let (pdiags, _) = paths::analyze(&c, &info, &env);
    let perr: Vec<_> = pdiags
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(perr.is_empty(), "paths: {perr:#?}");
    lower(&c, &info, &env, &report)
}

fn leaves(src: &str, args: &str) -> Vec<LoweredLeaf> {
    let (diags, leaves) = run(src, args);
    let errors: Vec<_> = diags
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        errors.is_empty(),
        "expected clean lowering, got: {errors:#?}"
    );
    leaves
}

fn one_leaf(src: &str, args: &str) -> LoweredLeaf {
    let mut ls = leaves(src, args);
    assert_eq!(ls.len(), 1, "expected one leaf");
    ls.remove(0)
}

// Real curve points (k*G for small k), lexicographically A < B < G.
// PublicKey externs are on-curve-validated at bind time, so the fixtures
// use genuine keys. The 0x11/0x22/0x33 byte tags below map to A/B/G
// respectively (the tags preserve the goldens' readable ordering).
const KEY_A: &str = "\"0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c\"";
const KEY_B: &str = "\"0x5cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc\"";
const KEY_G: &str = "\"0xf28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8\"";

fn key_bytes(tag: u8) -> Vec<u8> {
    let hex = match tag {
        0x11 => &KEY_A[3..67],
        0x22 => &KEY_B[3..67],
        0x33 => &KEY_G[3..67],
        _ => panic!("unknown key tag"),
    };
    (0..32)
        .map(|i| u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).expect("hex"))
        .collect()
}

/// `needle` ops appear in `haystack` in order (not necessarily adjacent).
fn contains_subseq(haystack: &[Op], needle: &[Op]) -> bool {
    let mut it = haystack.iter();
    needle.iter().all(|n| it.any(|h| h == n))
}

// --- single-sig: the minimal leaf ---

#[test]
fn single_sig_golden() {
    let leaf = one_leaf(
        "contract T {
            extern const k: PublicKey;
            spend f(s: Signature) { require k.check(s); }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY_A}}}"#),
    );
    assert_eq!(
        leaf.ops,
        vec![
            Op::PushNum(0),
            Op::Pick,
            Op::Push(key_bytes(0x11)),
            Op::CheckSigVerify,
            Op::Drop,
            Op::PushNum(1),
        ],
        "asm: {}",
        asm(&leaf.ops)
    );
    assert_eq!(leaf.witness_order, vec!["s"]);
    assert!(verify_script(&leaf.script).is_ok());
}

// --- hashlock: SIZE airlock + fused EQUALVERIFY ---

#[test]
fn hashlock_golden() {
    let leaf = one_leaf(
        "contract T {
            extern const k: PublicKey;
            extern const h: Bytes<32>;
            spend f(p: Bytes<32>, s: Signature) {
                require {
                    sha256(p) == h,
                    k.check(s)
                }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY_A}, "h": {KEY_B}}}"#),
    );
    assert_eq!(
        leaf.ops,
        vec![
            // reverse-consumption layout: p (consumed first) is on top, s
            // (consumed last by CHECKSIG) is deepest.
            // airlock: p is Bytes<32>, SIZE check IN PLACE (p is on top, SIZE
            // is non-consuming), never elided -- no PICK-copy, no DROP.
            // EQUALVERIFY (SIZE and a minimal push share an encoding; matches
            // rust-miniscript and the certifier decodes it as a length check).
            Op::Size,
            Op::PushNum(32),
            Op::EqualVerify,
            // sha256(p) == h: byte equality fuses to EQUALVERIFY
            Op::PushNum(0),
            Op::Pick,
            Op::Sha256,
            Op::Push(key_bytes(0x22)),
            Op::EqualVerify,
            // k.check(s)
            Op::PushNum(1),
            Op::Pick,
            Op::Push(key_bytes(0x11)),
            Op::CheckSigVerify,
            // CLEANSTACK
            Op::Drop2,
            Op::PushNum(1),
        ],
        "asm: {}",
        asm(&leaf.ops)
    );
    assert_eq!(leaf.witness_order, vec!["s", "p"]);
}

// --- two independent single-sig checks: reverse-consumption sig layout ---
//
// `hot.check(h)` then `warm.check(w)` is a conjunction of two separate checks.
// The signature witness slots lay out in reverse consumption order (the
// first-checked sig on top), so the optimizer consumes each off the stack top
// with no SWAP/ROLL/PICK, and the result no longer depends on the source order
// of the two conjuncts. (The naive leaf copies via PICK; the optimizer turns
// that into the consuming form -- which is where the layout decides whether a
// SWAP is needed -- so this asserts on the optimized leaf.)
#[test]
fn two_independent_sig_checks_no_juggle_and_order_independent() {
    let src = |a: &str, b: &str| {
        format!(
            "contract T {{
                extern const hot:  PublicKey;
                extern const warm: PublicKey;
                spend f(h: Signature, w: Signature) {{
                    require {{
                        {a},
                        {b}
                    }}
                }}
                keypath None;
            }}"
        )
    };
    let args = format!(r#"{{"hot": {KEY_A}, "warm": {KEY_B}}}"#);

    // Source order: hot/h first. h (consumed first) lays out on top, w deepest.
    let hw = optimize(&one_leaf(&src("hot.check(h)", "warm.check(w)"), &args));
    assert_eq!(
        hw.ops,
        vec![
            Op::Push(key_bytes(0x11)), // hot
            Op::CheckSigVerify,        // consumes h off the top, no juggle
            Op::Push(key_bytes(0x22)), // warm
            Op::CheckSig,              // tail: consumes w, its bool is the result
        ],
        "asm: {}",
        asm(&hw.ops)
    );
    assert_eq!(hw.witness_order, vec!["w", "h"]);

    // Reversed source order: warm/w first. Same optimal shape (no SWAP), just
    // the mirror -- byte count is identical, so output is order-independent.
    let wh = optimize(&one_leaf(&src("warm.check(w)", "hot.check(h)"), &args));
    assert_eq!(
        wh.ops,
        vec![
            Op::Push(key_bytes(0x22)), // warm
            Op::CheckSigVerify,
            Op::Push(key_bytes(0x11)), // hot
            Op::CheckSig,
        ],
        "asm: {}",
        asm(&wh.ops)
    );
    assert_eq!(wh.witness_order, vec!["h", "w"]);

    // Neither juggles: no SWAP, ROLL, or PICK in either ordering, and the two
    // scripts are the same length (the wart was a 1-byte SWAP in one order).
    for leaf in [&hw, &wh] {
        assert!(
            !leaf.ops.contains(&Op::Swap)
                && !leaf.ops.contains(&Op::Roll)
                && !leaf.ops.contains(&Op::Pick),
            "unexpected stack juggle: {}",
            asm(&leaf.ops)
        );
    }
    assert_eq!(
        hw.script.len(),
        wh.script.len(),
        "order changed the byte count"
    );
}

// --- thresholds: the CHECKSIGADD counting chain (k < n) ---
//
// A cost contract: keys lexicographic, signatures consumed off the stack
// top (witness slots in reverse chain order, named in the template), zero
// stack manipulation, and in tail position the comparison is the leaf
// result: `34n + ~2` script bytes. n-of-n (k == n) is a pure conjunction, so
// it collapses to the AND-chain `<k0> CHECKSIGVERIFY .. <kn-1> CHECKSIG`
// (34n bytes, no `<n> NUMEQUAL/GTE` tail) -- matching rust-miniscript.

#[test]
fn explicit_two_of_two_collapses_to_and_chain() {
    let leaf = one_leaf(
        "contract T {
            extern const a: PublicKey;
            extern const b: PublicKey;
            spend f(sa: Signature, sb: Signature) {
                require a.check(sa) + b.check(sb) >= 2;
            }
            keypath None;
        }",
        &format!(r#"{{"a": {KEY_A}, "b": {KEY_B}}}"#),
    );
    // 2-of-2 is n-of-n: every signature must verify, so this is the AND-chain,
    // not the CHECKSIGADD tally plus `<2> GREATERTHANOREQUAL`.
    assert_eq!(
        leaf.ops,
        vec![
            Op::Push(key_bytes(0x11)),
            Op::CheckSigVerify,
            Op::Push(key_bytes(0x22)),
            Op::CheckSig,
        ],
        "asm: {}",
        asm(&leaf.ops)
    );
    // Consumption order mirrors the chain: sa (key 0x11) goes on top, so it
    // is listed last (first = deepest).
    assert_eq!(leaf.witness_order, vec!["sb", "sa"]);
    assert_eq!(leaf.script.len(), 2 * 34, "n-of-n AND-chain: 34n bytes");
}

#[test]
fn comprehension_threshold_lowers_to_the_same_chain() {
    // The comprehension spelling and the explicit Add-tree produce the
    // identical CHECKSIGADD chain.
    let leaf = one_leaf(
        "contract T {
            extern const keys: [PublicKey; 2];
            spend f(sigs: [Signature; 2]) {
                require sum(k in keys, s in sigs => k.check(s)) >= 1;
            }
            keypath None;
        }",
        &format!(r#"{{"keys": [{KEY_A}, {KEY_B}]}}"#),
    );
    assert_eq!(
        leaf.ops,
        vec![
            Op::Push(key_bytes(0x11)),
            Op::CheckSig,
            Op::Push(key_bytes(0x22)),
            Op::CheckSigAdd,
            Op::PushNum(1),
            Op::GreaterThanOrEqual,
        ],
        "asm: {}",
        asm(&leaf.ops)
    );
    assert_eq!(leaf.witness_order, vec!["sigs[1]", "sigs[0]"]);
}

#[test]
fn chain_keys_sort_lexicographically() {
    // Keys injected unsorted (a=0x33.., b=0x11.., c=0x22..): the chain
    // emits 0x11, 0x22, 0x33 with each signature following its key.
    // Pairing is by key identity, never source position.
    let leaf = one_leaf(
        "contract T {
            extern const a: PublicKey;
            extern const b: PublicKey;
            extern const c: PublicKey;
            spend f(sa: Signature, sb: Signature, sc: Signature) {
                require a.check(sa) + b.check(sb) + c.check(sc) >= 2;
            }
            keypath None;
        }",
        &format!(r#"{{"a": {}, "b": {KEY_A}, "c": {KEY_B}}}"#, KEY_G),
    );
    assert_eq!(
        leaf.ops,
        vec![
            Op::Push(key_bytes(0x11)), // b, lexicographically first
            Op::CheckSig,
            Op::Push(key_bytes(0x22)), // c
            Op::CheckSigAdd,
            Op::Push(key_bytes(0x33)), // a
            Op::CheckSigAdd,
            Op::PushNum(2),
            Op::GreaterThanOrEqual,
        ],
        "asm: {}",
        asm(&leaf.ops)
    );
    // Chain consumes sb (0x11) first, so sb is on top and listed last.
    assert_eq!(leaf.witness_order, vec!["sa", "sc", "sb"]);
}

#[test]
fn permuted_key_injection_yields_identical_script() {
    // The script, and therefore the address, depends on the key set:
    // cosmetic injection reorders change only the witness template.
    let src = "contract T {
        extern const keys: [PublicKey; 3];
        spend f(sigs: [Signature; 3]) {
            require sum(k in keys, s in sigs => k.check(s)) >= 2;
        }
        keypath None;
    }";
    let key_c = KEY_G;
    let a = one_leaf(src, &format!(r#"{{"keys": [{KEY_A}, {KEY_B}, {key_c}]}}"#));
    let b = one_leaf(src, &format!(r#"{{"keys": [{key_c}, {KEY_A}, {KEY_B}]}}"#));
    assert_eq!(a.script, b.script, "same key set gives same script bytes");
    // The template maps slots by key identity: sigs[i] pairs keys[i] as
    // injected, so the physical order differs between the two injections.
    assert_eq!(a.witness_order, vec!["sigs[2]", "sigs[1]", "sigs[0]"]);
    assert_eq!(b.witness_order, vec!["sigs[0]", "sigs[2]", "sigs[1]"]);
}

#[test]
fn reused_sig_slot_falls_back_to_copy_chain() {
    // One signature checked against two keys: the slot is not single-use,
    // so the consuming layout is rejected and the copy-based chain (PICK +
    // SWAP, key-sorted, VERIFY form) takes over. Correctness never depends
    // on the fast path.
    let leaf = one_leaf(
        "contract T {
            extern const a: PublicKey;
            extern const b: PublicKey;
            spend f(s: Signature) {
                require a.check(s) + b.check(s) >= 1;
            }
            keypath None;
        }",
        &format!(r#"{{"a": {KEY_A}, "b": {KEY_B}}}"#),
    );
    assert_eq!(leaf.witness_order, vec!["s"]);
    assert!(leaf.ops.contains(&Op::Pick), "asm: {}", asm(&leaf.ops));
    assert!(leaf.ops.contains(&Op::Swap), "asm: {}", asm(&leaf.ops));
    assert!(
        contains_subseq(
            &leaf.ops,
            &[Op::GreaterThanOrEqual, Op::Verify, Op::PushNum(1)]
        ),
        "asm: {}",
        asm(&leaf.ops)
    );
}

// --- timelocks ---

#[test]
fn csv_relative_blocks() {
    let leaf = one_leaf(
        "contract T {
            extern const k: PublicKey;
            spend f(s: Signature) {
                require {
                    after(LockTime.Relative(blocks: 4320)),
                    k.check(s)
                }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY_A}}}"#),
    );
    assert!(
        leaf.ops
            .starts_with(&[Op::PushNum(4320), Op::Csv, Op::Drop]),
        "asm: {}",
        asm(&leaf.ops)
    );
}

#[test]
fn csv_relative_time_sets_bip68_type_flag() {
    // 90d = 7_776_000 s, ceil/512 = 15_188 units, OR'd with bit 22.
    let leaf = one_leaf(
        "contract T {
            extern const k: PublicKey;
            spend f(s: Signature) {
                require {
                    after(LockTime.Relative(time: \"P90D\")),
                    k.check(s)
                }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY_A}}}"#),
    );
    let expect = 15_188 | (1 << 22);
    assert!(
        leaf.ops
            .starts_with(&[Op::PushNum(expect), Op::Csv, Op::Drop]),
        "asm: {}",
        asm(&leaf.ops)
    );
}

#[test]
fn cltv_absolute_height() {
    let leaf = one_leaf(
        "contract T {
            extern const k: PublicKey;
            extern const t: LockTime.Absolute;
            spend f(s: Signature) {
                require {
                    after(t),
                    k.check(s)
                }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY_A}, "t": {{"height": 900000}}}}"#),
    );
    assert!(
        leaf.ops
            .starts_with(&[Op::PushNum(900_000), Op::Cltv, Op::Drop]),
        "asm: {}",
        asm(&leaf.ops)
    );
}

// --- ranges: native WITHIN, const-folded `..=`, the +max fallback ---

#[test]
fn half_open_range_is_native_within() {
    let leaf = one_leaf(
        "contract T {
            extern const k: PublicKey;
            spend f(relaxed x: Int, s: Signature) {
                require {
                    x in 0..1000,
                    k.check(s)
                }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY_A}}}"#),
    );
    assert!(
        contains_subseq(
            &leaf.ops,
            &[Op::PushNum(0), Op::PushNum(1000), Op::Within, Op::Verify]
        ),
        "asm: {}",
        asm(&leaf.ops)
    );
}

#[test]
fn inclusive_range_const_folds_hi_plus_one() {
    let leaf = one_leaf(
        "contract T {
            extern const k: PublicKey;
            spend f(relaxed x: Int, s: Signature) {
                require {
                    x in 1..=10,
                    k.check(s)
                }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY_A}}}"#),
    );
    // hi+1 folds at compile time: WITHIN(x, 1, 11), no runtime 1ADD.
    assert!(
        contains_subseq(&leaf.ops, &[Op::PushNum(1), Op::PushNum(11), Op::Within]),
        "asm: {}",
        asm(&leaf.ops)
    );
    assert!(
        !leaf.ops.contains(&Op::Add1),
        "no runtime 1ADD: {}",
        asm(&leaf.ops)
    );
}

#[test]
fn inclusive_range_at_max_falls_back_to_two_comparisons() {
    // hi = +max: hi+1 exceeds the 4-byte WITHIN operand domain, so the
    // lowering is two conjoined comparisons (totality).
    let leaf = one_leaf(
        "contract T {
            extern const k: PublicKey;
            spend f(relaxed x: Int, s: Signature) {
                require {
                    x in 0..=2_147_483_647,
                    k.check(s)
                }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY_A}}}"#),
    );
    assert!(
        contains_subseq(
            &leaf.ops,
            &[
                Op::GreaterThanOrEqual,
                Op::LessThanOrEqual,
                Op::BoolAnd,
                Op::Verify
            ]
        ),
        "asm: {}",
        asm(&leaf.ops)
    );
    assert!(
        !leaf.ops.contains(&Op::Within),
        "WITHIN impossible at +max: {}",
        asm(&leaf.ops)
    );
}

// --- comprehensions: the where-guard IF/ADD/ENDIF pattern ---

#[test]
fn where_sum_unrolls_to_guarded_adds() {
    let leaf = one_leaf(
        "contract T {
            extern const k: PublicKey;
            spend f(relaxed px: [Bool; 3], s: Signature) {
                let score = sum(b in px, w in [5, 7, 9] where b => w);
                require {
                    score >= 1,
                    k.check(s)
                }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY_A}}}"#),
    );
    // Reverse-consumption layout: s deepest, and the array laid index-0 on top
    // so the fold lifts each element from depth 1. Stack at the let is
    // [s, px2, px1, px0, acc]; the naive picks are at depths 1, 2, 3 (the
    // optimizer turns the depth-1 lift into a SWAP). px0 has weight 5, etc.
    let expect_prefix = vec![
        Op::PushNum(0), // acc = 0
        Op::PushNum(1),
        Op::Pick,
        Op::If,
        Op::PushNum(5),
        Op::Add,
        Op::EndIf,
        Op::PushNum(2),
        Op::Pick,
        Op::If,
        Op::PushNum(7),
        Op::Add,
        Op::EndIf,
        Op::PushNum(3),
        Op::Pick,
        Op::If,
        Op::PushNum(9),
        Op::Add,
        Op::EndIf,
    ];
    assert!(
        leaf.ops.starts_with(&expect_prefix),
        "asm: {}",
        asm(&leaf.ops)
    );
    // Bare single-clause guards are MINIMALIF-protected: no Bool airlock.
    assert!(
        !leaf.ops.contains(&Op::ZeroNotEqual),
        "asm: {}",
        asm(&leaf.ops)
    );
    assert_eq!(leaf.witness_order, vec!["s", "px[2]", "px[1]", "px[0]"]);
}

#[test]
fn count_uses_if_1add() {
    let leaf = one_leaf(
        "contract T {
            extern const k: PublicKey;
            spend f(relaxed bs: [Bool; 2], s: Signature) {
                let n = count(b in bs => b);
                require {
                    n >= 1,
                    k.check(s)
                }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY_A}}}"#),
    );
    assert!(
        contains_subseq(
            &leaf.ops,
            &[Op::If, Op::Add1, Op::EndIf, Op::If, Op::Add1, Op::EndIf]
        ),
        "asm: {}",
        asm(&leaf.ops)
    );
}

// --- select: IF/ELSE/ENDIF, MINIMALIF covers the bare guard ---

#[test]
fn select_lowers_to_if_else_no_airlock() {
    let leaf = one_leaf(
        "contract T {
            extern const k: PublicKey;
            spend f(relaxed c: Bool, s: Signature) {
                let v = select(c, then: 2, else: 3);
                require {
                    v >= 2,
                    k.check(s)
                }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY_A}}}"#),
    );
    assert!(
        contains_subseq(
            &leaf.ops,
            &[Op::If, Op::PushNum(2), Op::Else, Op::PushNum(3), Op::EndIf]
        ),
        "asm: {}",
        asm(&leaf.ops)
    );
    // c's only use is the select condition: MINIMALIF, no airlock.
    assert!(
        !leaf.ops.contains(&Op::ZeroNotEqual),
        "asm: {}",
        asm(&leaf.ops)
    );
}

// --- Bool airlocks: emitted exactly when a use escapes IF-position ---

#[test]
fn bool_in_arithmetic_gets_the_canonicality_airlock() {
    let leaf = one_leaf(
        "contract T {
            extern const k: PublicKey;
            spend f(relaxed b: Bool, s: Signature) {
                require {
                    b + 1 >= 1,
                    k.check(s)
                }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY_A}}}"#),
    );
    assert!(
        // b is on top (reverse-consumption layout), so the canonicality check
        // is in place: DUP a copy to consume, leaving b for the `b + 1`.
        leaf.ops
            .starts_with(&[Op::Dup, Op::Dup, Op::ZeroNotEqual, Op::EqualVerify]),
        "asm: {}",
        asm(&leaf.ops)
    );
}

#[test]
fn multi_clause_guard_forces_the_airlock() {
    // Two where clauses conjoin via BOOLAND, which accepts non-canonical
    // truthy values, so the bare binder no longer counts as IF-position.
    let leaf = one_leaf(
        "contract T {
            extern const k: PublicKey;
            spend f(relaxed px: [Bool; 2], s: Signature) {
                let n = sum(b in px, i in 0..2 where b, i < 5 => 1);
                require {
                    n >= 1,
                    k.check(s)
                }
            }
            keypath None;
        }",
        &format!(r#"{{"k": {KEY_A}}}"#),
    );
    assert!(
        contains_subseq(&leaf.ops, &[Op::ZeroNotEqual, Op::EqualVerify]),
        "multi-clause guard needs the airlock: {}",
        asm(&leaf.ops)
    );
    assert!(
        contains_subseq(&leaf.ops, &[Op::BoolAnd, Op::If]),
        "asm: {}",
        asm(&leaf.ops)
    );
}

// --- the corpus, lowered ---

#[test]
fn corpus_lowers_clean_and_passes_the_poison_gate() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
    let load = |name: &str| -> Vec<LoweredLeaf> {
        let src = std::fs::read_to_string(dir.join(format!("{name}.sl"))).unwrap();
        let args = std::fs::read_to_string(dir.join(format!("{name}.args.json"))).unwrap();
        leaves(&src, &args)
    };

    let vault = load("vault");
    assert_eq!(vault.len(), 2, "fallback + recover");
    for leaf in &vault {
        assert_eq!(leaf.witness_order, vec!["signature"]);
        assert!(leaf.ops.contains(&Op::Csv));
        assert!(leaf.ops.contains(&Op::CheckSigVerify));
    }

    let htlc = load("htlc");
    assert_eq!(htlc.len(), 2, "swap + refund");
    let swap = htlc.iter().find(|l| l.name == "swap").unwrap();
    assert_eq!(swap.witness_order, vec!["signature", "preimage"]);
    assert!(contains_subseq(
        &swap.ops,
        &[Op::Size, Op::PushNum(32), Op::EqualVerify] // the preimage airlock
    ));
    assert!(contains_subseq(&swap.ops, &[Op::Sha256, Op::EqualVerify]));
    let refund = htlc.iter().find(|l| l.name == "refund").unwrap();
    assert!(
        refund
            .ops
            .starts_with(&[Op::PushNum(900_000), Op::Cltv, Op::Drop])
    );

    let multisig = load("multisig");
    assert_eq!(multisig.len(), 1);
    let f = &multisig[0];
    // The consuming chain: slots in reverse chain order (keys injected
    // pre-sorted, so the identity permutation reversed), no stack ops, the
    // comparison as the leaf result: exactly 34n + 2 bytes.
    assert_eq!(f.witness_order, vec!["sigs[2]", "sigs[1]", "sigs[0]"]);
    let adds = f.ops.iter().filter(|o| **o == Op::CheckSigAdd).count();
    assert_eq!(
        (f.ops.iter().filter(|o| **o == Op::CheckSig).count(), adds),
        (1, 2)
    );
    assert!(!f.ops.contains(&Op::Pick) && !f.ops.contains(&Op::Swap));
    assert!(f.ops.ends_with(&[Op::PushNum(2), Op::GreaterThanOrEqual]));
    assert_eq!(f.script.len(), 3 * 34 + 2, "the spec's 34n + ~2 contract");

    let cat = load("cat_bounty");
    assert_eq!(cat.len(), 1);
    let claim = &cat[0];
    // 37 zero-weight pixels are dead and dropped from the witness: 784 - 37 + 1
    // signature = 748. Reverse-consumption layout: signature (consumed last)
    // deepest, the surviving pixels index-descending below it (index 0 on top).
    assert_eq!(
        claim.witness_order.len(),
        748,
        "784 - 37 dead pixels + signature"
    );
    assert_eq!(claim.witness_order[0], "signature");
    assert_eq!(claim.witness_order[1], "drawing[783]"); // weight -4, kept
    assert_eq!(claim.witness_order[747], "drawing[0]"); // weight -10, kept (topmost)
    // One guarded add per SURVIVING pixel; the 37 dead ones emit nothing.
    assert_eq!(claim.ops.iter().filter(|o| **o == Op::If).count(), 747);
    // The free MINIMALIF airlock: no canonicality sequence for the pixels.
    assert!(!claim.ops.contains(&Op::ZeroNotEqual));
    assert!(claim.ops.contains(&Op::CheckSigVerify));
}

// --- the model is honest: every emitted script passes the poison gate ---

#[test]
fn lowering_is_deterministic() {
    let src = "contract T {
        extern const k: PublicKey;
        spend f(relaxed x: Int, s: Signature) {
            require x in 0..1000;
            require k.check(s);
        }
        keypath None;
    }";
    let args = format!(r#"{{"k": {KEY_A}}}"#);
    let a = leaves(src, &args);
    let b = leaves(src, &args);
    assert_eq!(a.len(), b.len());
    for (x, y) in a.iter().zip(&b) {
        assert_eq!(x.ops, y.ops);
        assert_eq!(x.script, y.script);
        assert_eq!(x.witness_order, y.witness_order);
    }
}

/// A fully-const comparison must fold to a literal in the naive leaf. The CSE
/// recording path splits a comparison into `push subject, push bound, cmp`,
/// which would diverge from the whole-expression const fold the general path
/// performs; it must therefore fire only for a witness-dependent subject. A
/// const `a >= 3` (a = 5) must leave no comparison opcode behind.
#[test]
fn const_comparison_folds_to_a_literal_not_a_split_compare() {
    let src = "contract T { extern const k: PublicKey; extern const a: Int;
        spend f(s: Signature) { require { a >= 3, k.check(s) } } keypath None; }";
    let args = format!(r#"{{"k": {KEY_A}, "a": 5}}"#);
    let leaf = one_leaf(src, &args);
    assert!(
        !leaf.ops.iter().any(|o| matches!(o, Op::GreaterThanOrEqual)),
        "const `a >= 3` must fold, not emit a split comparison: {:?}",
        leaf.ops
    );
}
