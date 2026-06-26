//! Rule-by-rule semantic checker tests: every rule in sema.rs's header doc
//! has a positive and a negative case.

use seal::analysis::sema;
use seal::syntax::parser::parse_source;

/// Parse (must be syntactically clean) then check; return diagnostic codes.
fn check(src: &str) -> Vec<&'static str> {
    let (contract, parse_diags) = parse_source(src);
    assert!(
        parse_diags.is_empty(),
        "parse must be clean for {src:?}: {parse_diags:#?}"
    );
    sema::check(&contract.expect("contract"))
        .iter()
        .map(|d| d.code)
        .collect()
}

fn ok(src: &str) {
    let codes = check(src);
    assert!(
        codes.is_empty(),
        "expected clean check of {src:?}, got: {codes:?}"
    );
}

fn has(src: &str, code: &str) {
    let codes = check(src);
    assert!(
        codes.contains(&code),
        "expected {code} for {src:?}, got: {codes:?}"
    );
}

/// Wrap statements into a standard spend with useful params in scope.
fn body(stmts: &str) -> String {
    format!(
        "contract T {{
            extern const k: PublicKey;
            extern const h: Hash<Sha256>;
            extern const t: LockTime.Relative;
            extern const ws: [Int; 4];
            spend f(x: Int, b: Bool, s: Signature, p: Bytes<32>, bits: [Bool; 4]) {{
                {stmts}
            }}
            keypath None;
        }}"
    )
}

// --- resolution & scoping

#[test]
fn unresolved_and_use_before_decl() {
    has(&body("require y > 0;"), "sema/unresolved");
    // consts resolve in declaration order
    has(
        "contract T { const a = b + 1; const b = 2; keypath None; }",
        "sema/unresolved",
    );
}

#[test]
fn no_shadowing_no_dups() {
    has(&body("let x = 1;"), "sema/shadow"); // param x already in scope
    has(&body("let q = 1; let q = 2;"), "sema/shadow");
    has(
        "contract T { const a = 1; const a = 2; keypath None; }",
        "sema/dup",
    );
    // a const may not take a spend's name
    has(
        "contract T { spend f(s: Signature) { require true; }
                      const f = 1; keypath None; }",
        "sema/dup",
    );
}

#[test]
fn stdlib_and_type_names_protected() {
    has(
        "contract T { const sum = 1; keypath None; }",
        "sema/shadow-stdlib",
    );
    has(
        "contract T { const Int = 1; keypath None; }",
        "sema/shadow-stdlib",
    );
    has(&body("let abs = 1;"), "sema/shadow-stdlib");
}

#[test]
fn type_and_fn_names_are_not_values() {
    has(&body("let v = Int;"), "sema/type-as-value");
    has(&body("let v = abs;"), "sema/fn-as-value");
    has(&body("let v = f;"), "sema/spend-as-value");
}

// --- types of declarations

#[test]
fn signature_is_witness_only() {
    has(
        "contract T { extern const s: Signature; keypath None; }",
        "sema/extern-signature",
    );
    has(
        "contract T { extern const s: [Signature; 3]; keypath None; }",
        "sema/extern-signature",
    );
}

#[test]
fn witness_pubkey_params_allowed() {
    // Allowed: the airlock enforces SIZE==32; authorization counts only const
    // or commitment-pinned keys. At the type level this is clean.
    ok("contract T { spend f(k: PublicKey, s: Signature) { require k.check(s); } keypath None; }");
    // The legitimate idiom: hash-committed delegation. Keys are hashable.
    ok("contract T {
            extern const commitment: Hash<Hash160>;
            spend f(k: PublicKey, s: Signature) {
                require { hash160(k) == commitment, k.check(s) }
            }
            keypath None;
        }");
}

#[test]
fn locktime_is_const_only() {
    has(
        "contract T { spend f(t: LockTime.Absolute, s: Signature) { require true; } keypath None; }",
        "sema/witness-locktime",
    );
}

#[test]
fn typed_byte_constructors() {
    // Form Bytes<32>("0x..."): closed-type-name disambiguation makes it parse
    // as a constructor, never comparisons.
    let h64 = "ab".repeat(32);
    ok(&format!(
        "contract T {{ const h = Bytes<32>(\"0x{h64}\"); extern const p: Bytes<32>;
           spend f(s: Signature) {{ require p == h; }} keypath None; }}"
    ));
    ok(&format!(
        "contract T {{ const h = Hash<Sha256>(\"0x{h64}\"); keypath None; }}"
    ));
    // Wrong hex length for the declared type.
    has(
        "contract T { const h = Bytes<32>(\"0xabcd\"); keypath None; }",
        "sema/ctor-hex",
    );
    // Not a string argument.
    has(
        "contract T { const h = Bytes<4>(5); keypath None; }",
        "sema/ctor-arg",
    );
    // Named lengths have no value at template level.
    has(
        "contract T { extern const n: Int; const h = Bytes<n>(\"0xab\"); keypath None; }",
        "sema/ctor-len",
    );
}

#[test]
fn bytes_caps() {
    has(
        "contract T { spend f(p: Bytes<81>, s: Signature) { require true; } keypath None; }",
        "sema/bytes-cap",
    );
    ok("contract T { spend f(p: Bytes<80>, s: Signature) { require true; } keypath None; }");
    has(
        "contract T { extern const c: Bytes<521>; keypath None; }",
        "sema/bytes-cap",
    );
    ok("contract T { extern const c: Bytes<520>; keypath None; }");
}

#[test]
fn const_type_annotation_checked() {
    has(
        "contract T { const c: Bool = 5; keypath None; }",
        "sema/type-mismatch",
    );
    ok("contract T { const c: Int = 5; keypath None; }");
}

// --- equality classes

#[test]
fn hash_equality_rules() {
    // Hash<A> == Hash<B> is an error.
    has(&body("require sha256(p) == hash256(p);"), "sema/hash-mix");
    // Hash vs same-length Bytes is fine (32 == 32).
    ok(&body("require sha256(p) == h;"));
    // Hash160 (20B) vs Bytes<32> is always-false, so error.
    has(&body("require hash160(p) == p;"), "sema/type-mismatch");
    // Bytes lengths must match.
    has(
        "contract T { spend f(a: Bytes<4>, b: Bytes<8>, s: Signature) { require a == b; } keypath None; }",
        "sema/type-mismatch",
    );
}

#[test]
fn no_ordering_on_bytes() {
    has(&body("require p < p;"), "sema/type-mismatch");
}

#[test]
fn widening_is_one_way() {
    ok(&body("require b + b >= 1;")); // Bool widens in arithmetic
    ok(&body("require x == b;")); // and in equality with Int
    has(&body("require x;"), "sema/require-bool"); // Int is not a condition
    has(&body("let v = !x;"), "sema/type-mismatch"); // ! takes Bool
    has(&body("let v = -b;"), "sema/type-mismatch"); // unary - takes Int
}

// --- check-kind: after() composes via commas only

#[test]
fn after_is_a_require_item_only() {
    ok(&body("require { after(t), k.check(s) }"));
    has(&body("let v = after(t);"), "sema/check-position");
    has(&body("require !after(t);"), "sema/check-position");
    has(&body("require after(t) + 1 > 0;"), "sema/check-position");
    has(
        "contract T { extern const t: LockTime.Relative; require after(t); keypath None; }",
        "sema/check-position",
    );
}

#[test]
fn locktime_constructor_rules() {
    ok(&body("require after(LockTime.Relative(blocks: 4320));"));
    ok(&body("require after(LockTime.Relative(time: \"P90D\"));"));
    // The retired span literal is rejected in favor of ISO-8601 durations.
    has(
        &body("require after(LockTime.Relative(time: 90d));"),
        "sema/type-mismatch",
    );
    ok(&body("require after(LockTime.Absolute(height: 900_000));"));
    has(
        &body("require after(LockTime.Relative(height: 10));"),
        "sema/args",
    );
    has(
        &body("require after(LockTime.Absolute(time: 90d));"),
        "sema/type-mismatch",
    );
    has(
        &body("require after(LockTime.Relative(blocks: x));"),
        "sema/locktime-const",
    );
    has(&body("require after(x);"), "sema/type-mismatch");
}

// --- provenance: const-required positions

#[test]
fn pow_is_const_only() {
    ok(&body("require x < pow(2, 30) - 1;"));
    has(&body("let v = pow(x, 2);"), "sema/pow-const");
}

#[test]
fn keypath_must_be_const_pubkey() {
    has(
        "contract T { extern const n: Int; keypath n; }",
        "sema/type-mismatch",
    );
    ok(
        "contract T { extern const a: PublicKey; extern const b: PublicKey;
           keypath PublicKey.MuSig2([a, b]); }",
    );
}

#[test]
fn precondition_rules() {
    ok("contract T { extern const m: Int; require 1 <= m; keypath None; }");
    ok("contract T { require 1 < 2 + 0; keypath None; }");
    // Comprehensions over const data are const: array-based preconditions are
    // legal and evaluated at instantiation.
    ok("contract T { extern const ws: [Int; 4]; require all(w in ws => w > 0); keypath None; }");
}

#[test]
fn array_indices_are_const() {
    ok(&body("require bits[0];"));
    ok(&body("require ws[3] > 0;"));
    has(&body("require ws[x] > 0;"), "sema/index-const");
    has(&body("require x[0] > 0;"), "sema/type-mismatch");
}

#[test]
fn comprehension_range_bounds_are_const() {
    ok(&body("let v = sum(i in 0..4 => i);"));
    has(&body("let v = sum(i in 0..x => i);"), "sema/range-const");
}

#[test]
fn array_literals_are_const() {
    has(&body("let v = [x, x];"), "sema/array-const");
}

// --- stdlib shapes

#[test]
fn select_shape_and_arms() {
    ok(&body("let v = select(b, then: 1, else: 2);"));
    has(&body("let v = select(b, 1, 2);"), "sema/select-shape");
    has(
        &body("let v = select(x, then: 1, else: 2);"),
        "sema/type-mismatch",
    );
    has(
        &body("let v = select(b, then: 1, else: b);"),
        "sema/type-mismatch",
    );
}

#[test]
fn hash_inputs_are_bytes_only() {
    has(&body("let v = sha256(x);"), "sema/type-mismatch");
    ok(&body("let v = sha256(p);"));
    ok(&body("let v = sha256(sha256(p));")); // Hash input is Bytes-compatible
}

#[test]
fn check_method_rules() {
    ok(&body("require k.check(s);"));
    has(&body("require x.check(s);"), "sema/type-mismatch");
    has(&body("require k.check(x);"), "sema/type-mismatch");
    has(&body("require k.verify(s);"), "sema/member");
    has(&body("let v = PublicKey.MuSig2(ws);"), "sema/type-mismatch");
}

#[test]
fn pubkey_literal_shape() {
    ok(&format!(
        "contract T {{ const k = PublicKey(\"0x{}\"); keypath k; }}",
        "ab".repeat(32)
    ));
    has(
        "contract T { const k = PublicKey(\"0xabcd\"); keypath k; }",
        "sema/key-literal",
    );
}

#[test]
fn strings_and_durations_are_positional() {
    has(&body("let v = \"abc\";"), "sema/str-position");
    has(&body("let v = 90d;"), "sema/duration-position");
}

// --- comprehensions

#[test]
fn comprehension_rules() {
    ok(&body("let v = sum(w in ws, bit in bits where bit => w);"));
    ok(&body("let v = count(bit in bits => bit);"));
    ok(&body("let v = all(w in ws => w > 0);"));
    ok(&body("let v = fold(acc = 0, w in ws => acc + w);"));
    // zip length mismatch (4 vs literal 2-array)
    has(
        &body("let arr = [1, 2]; let v = sum(w in ws, a in arr => w + a);"),
        "sema/zip-len",
    );
    // count body must be Bool
    has(&body("let v = count(w in ws => w);"), "sema/type-mismatch");
    // sum body Bool widens
    ok(&body("let v = sum(bit in bits => bit);"));
    // fold body must match accumulator type
    has(
        &body("let v = fold(acc = b, w in ws => w);"),
        "sema/type-mismatch",
    );
    // unknown aggregator
    has(&body("let v = product(w in ws => w);"), "sema/comp-callee");
    // binder over non-array
    has(&body("let v = sum(i in x => i);"), "sema/type-mismatch");
    // where guard must be Bool
    has(
        &body("let v = sum(w in ws where w => w);"),
        "sema/type-mismatch",
    );
}

#[test]
fn binders_do_not_leak() {
    // `w` is out of scope after the comprehension, even after an error inside.
    has(
        &body("let v = sum(w in ws => w); require w > 0;"),
        "sema/unresolved",
    );
    has(
        &body("let v = sum(w in ws => unknown); require w > 0;"),
        "sema/unresolved",
    );
}

// The tree placement checks (sema/tree-missing, /tree-unknown, /tree-dup) were
// removed with the `layout` block: every spend is its own leaf by guarantee,
// and the tree is planned from `@depth`/`@weight` at assembly time, validated
// there against Kraft.
