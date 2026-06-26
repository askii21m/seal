//! Construct-by-construct parser tests: every decision in the parser's header
//! doc has a positive and a negative case here.

use seal::syntax::ast::*;
use seal::syntax::parser::parse_source;

/// Parse a full contract expecting zero diagnostics.
fn ok(src: &str) -> Contract {
    let (c, diags) = parse_source(src);
    assert!(
        diags.is_empty(),
        "expected clean parse of {src:?}, got: {diags:#?}"
    );
    c.expect("contract")
}

/// Wrap a statement into a minimal contract and parse it clean.
fn ok_stmt(stmt: &str) -> Contract {
    ok(&format!(
        "contract T {{ spend f(x: Int, s: Signature) {{ {stmt} }} keypath None; }}"
    ))
}

/// Parse expecting at least one diagnostic; return all codes.
fn err(src: &str) -> Vec<&'static str> {
    let (_, diags) = parse_source(src);
    assert!(!diags.is_empty(), "expected diagnostics for {src:?}");
    diags.iter().map(|d| d.code).collect()
}

fn err_stmt(stmt: &str) -> Vec<&'static str> {
    err(&format!(
        "contract T {{ spend f(x: Int, s: Signature) {{ {stmt} }} keypath None; }}"
    ))
}

/// Dig the first spend's first statement out of a contract.
fn first_stmt(c: &Contract) -> &Stmt {
    c.items
        .iter()
        .find_map(|i| match i {
            Item::Spend(s) => s.body.first(),
            _ => None,
        })
        .expect("statement")
}

// --- items ---

#[test]
fn extern_const_requires_annotation() {
    let codes = err("contract T { extern const x = 5; keypath None; }");
    assert!(codes.contains(&"parse/extern-needs-type"), "{codes:?}");
}

#[test]
fn const_with_and_without_annotation() {
    ok("contract T { const x = 5; const y: Int = 6; keypath None; }");
}

#[test]
fn one_contract_per_file() {
    let codes = err("contract A { keypath None; } contract B { keypath None; }");
    assert!(codes.contains(&"parse/trailing"), "{codes:?}");
}

#[test]
fn open_spend_parses() {
    let c = ok("contract T { open spend faucet() { require true; } keypath None; }");
    match &c.items[0] {
        Item::Spend(s) => assert!(s.open),
        i => panic!("{i:?}"),
    }
}

#[test]
fn require_block_forbids_trailing_semi() {
    // A brace block self-terminates; a one-liner needs `;`.
    ok("contract T {
        spend f(s: Signature) {
            require { s == s }
        }
        keypath None;
    }");
    // The same with a stray `;` after the block is a teaching diagnostic.
    let codes = err("contract T {
        spend f(s: Signature) {
            require { s == s };
        }
        keypath None;
    }");
    assert!(codes.contains(&"parse/block-semi"), "{codes:?}");
    // A one-liner require keeps its `;`.
    ok_stmt("require s == s;");
    let codes = err_stmt("require s == s");
    assert!(codes.contains(&"parse/expected"), "{codes:?}");
}

#[test]
fn trailing_commas_everywhere() {
    ok("contract T {
        const ks = [1, 2, 3,];
        spend f(a: Int, b: Signature,) {
            require { a > 0, }
        }
        keypath None;
    }");
}

// --- keypath + decorators ---

#[test]
fn keypath_is_required() {
    let codes = err("contract T { spend f(s: Signature) { require s == s; } }");
    assert!(codes.contains(&"parse/keypath-missing"), "{codes:?}");
}

#[test]
fn keypath_one_liner_and_block_forms() {
    // One-liner needs `;`; block form holds exactly one thing, no `;`.
    let c = ok("contract T { keypath None; }");
    assert!(matches!(
        c.items.iter().find_map(|i| match i {
            Item::Keypath(kp) => Some(kp),
            _ => None,
        }),
        Some(Keypath::None(_))
    ));
    ok("contract T { keypath { None } }");
    // A block with more than one thing is rejected.
    let codes = err("contract T { keypath { None None } }");
    assert!(codes.contains(&"parse/keypath-block"), "{codes:?}");
    // The `layout { }` block was removed.
    let codes = err("contract T { layout { keypath: None } }");
    assert!(codes.contains(&"parse/layout-removed"), "{codes:?}");
}

#[test]
fn keypath_declared_once() {
    let codes = err("contract T { keypath None; keypath None; }");
    assert!(codes.contains(&"parse/keypath-dup"), "{codes:?}");
}

#[test]
fn decorators_parse_and_validate() {
    // `@depth`/`@weight` attach to a spend; weights are decimals, parsed
    // exactly to fixed-point micro-weights (times 1_000_000).
    let c = ok("contract T {
        keypath None;
        @depth(1) spend a(s: Signature) { require s == s; }
        @weight(4) spend b(s: Signature) { require s == s; }
        @weight(0.4) spend c(s: Signature) { require s == s; }
        @weight(2.5) spend d(s: Signature) { require s == s; }
    }");
    let spends: Vec<_> = c
        .items
        .iter()
        .filter_map(|i| match i {
            Item::Spend(s) => Some(s),
            _ => None,
        })
        .collect();
    assert_eq!(spends[0].depth, Some(1));
    assert_eq!(spends[1].weight, Some(4_000_000)); // 4.0
    assert_eq!(spends[2].weight, Some(400_000)); // 0.4, exact fixed point
    assert_eq!(spends[3].weight, Some(2_500_000)); // 2.5
    // A zero weight is meaningless; too many fractional digits is rejected.
    let codes =
        err("contract T { keypath None; @weight(0) spend a(s: Signature) { require s == s; } }");
    assert!(codes.contains(&"parse/weight-range"), "{codes:?}");
    let codes = err(
        "contract T { keypath None; @weight(0.1234567) spend a(s: Signature) { require s == s; } }",
    );
    assert!(codes.contains(&"parse/weight-precision"), "{codes:?}");
    // A decimal `@depth` is a type error (depth is whole levels).
    let codes =
        err("contract T { keypath None; @depth(1.5) spend a(s: Signature) { require s == s; } }");
    assert!(codes.contains(&"parse/decorator-arg"), "{codes:?}");
    // Decimals exist only in `@weight`, nowhere else.
    let codes = err("contract T { const x = 0.4; keypath None; }");
    assert!(codes.contains(&"parse/decimal-position"), "{codes:?}");
    // Unknown decorator.
    let codes =
        err("contract T { keypath None; @inline spend a(s: Signature) { require s == s; } }");
    assert!(codes.contains(&"parse/decorator-unknown"), "{codes:?}");
}

// --- statements ---

#[test]
fn let_annotation_teaches() {
    let codes = err_stmt("let y: Int = 5;");
    assert!(codes.contains(&"parse/let-annotation"), "{codes:?}");
}

#[test]
fn require_forms() {
    ok_stmt("require x > 0;");
    ok_stmt("require { x > 0 }");
    ok_stmt("require { x > 0, x < 10, }");
}

#[test]
fn require_empty_block_rejected() {
    let codes = err_stmt("require { };");
    assert!(codes.contains(&"parse/require-empty"), "{codes:?}");
}

// --- expressions ---

#[test]
fn chain_same_direction_ok() {
    ok_stmt("require 1 <= x <= 10;");
    ok_stmt("require 10 >= x > 0;");
}

#[test]
fn chain_mixed_rejected() {
    let codes = err_stmt("require 1 <= x >= 0;");
    assert!(codes.contains(&"parse/chain-mixed"), "{codes:?}");
}

#[test]
fn chain_eq_rejected() {
    let codes = err_stmt("require x == x == x;");
    assert!(codes.contains(&"parse/chain-eq"), "{codes:?}");
}

#[test]
fn membership_needs_range() {
    ok_stmt("require x in 0..10;");
    ok_stmt("require x in 0..=1_000_000;");
    let codes = err_stmt("require x in y;");
    assert!(codes.contains(&"parse/in-needs-range"), "{codes:?}");
}

#[test]
fn standalone_range_is_not_a_value() {
    let codes = err_stmt("let r = 0..10;");
    assert!(codes.contains(&"parse/range-not-value"), "{codes:?}");
}

#[test]
fn in_does_not_chain() {
    let codes = err_stmt("require x in 0..10 < 5;");
    assert!(codes.contains(&"parse/chain-in"), "{codes:?}");
}

#[test]
fn select_labels_may_be_keywords() {
    let c = ok_stmt("let v = select(x > 0, then: 1, else: 2);");
    match first_stmt(&c) {
        Stmt::Let {
            value: Expr::Call { args, .. },
            ..
        } => {
            let labels: Vec<_> = args
                .iter()
                .map(|a| a.label.as_ref().map(|l| l.text.as_str()))
                .collect();
            assert_eq!(labels, vec![None, Some("then"), Some("else")]);
        }
        s => panic!("{s:?}"),
    }
}

#[test]
fn precedence_shape() {
    // -a + b - c < d  parses as  (((-a) + b) - c) < d
    let c = ok_stmt("require -x + 1 - 2 < 3;");
    match first_stmt(&c) {
        Stmt::Require(r) => match &r.items[0] {
            Expr::Compare { first, rest, .. } => {
                assert_eq!(rest.len(), 1);
                assert!(matches!(rest[0].0, CmpOp::Lt));
                match first.as_ref() {
                    Expr::Binary {
                        op: BinaryOp::Sub,
                        lhs,
                        ..
                    } => match lhs.as_ref() {
                        Expr::Binary {
                            op: BinaryOp::Add,
                            lhs,
                            ..
                        } => {
                            assert!(matches!(
                                lhs.as_ref(),
                                Expr::Unary {
                                    op: UnaryOp::Neg,
                                    ..
                                }
                            ));
                        }
                        e => panic!("{e:?}"),
                    },
                    e => panic!("{e:?}"),
                }
            }
            e => panic!("{e:?}"),
        },
        s => panic!("{s:?}"),
    }
}

#[test]
fn member_call_and_index() {
    ok_stmt("require keys[0].check(s);");
    ok_stmt("require PublicKey.MuSig2([a, b]).check(s);");
}

#[test]
fn typed_constructors_parse_not_comparisons() {
    // `Bytes<32>("0x...")` is a constructor: the closed generic-type-name set
    // makes `Bytes <` unambiguous in expression position.
    let c = ok_stmt("let h = Bytes<32>(\"0xab\");");
    match first_stmt(&c) {
        Stmt::Let {
            value: Expr::TypedCtor { args, .. },
            ..
        } => {
            assert_eq!(args.len(), 1);
        }
        s => panic!("expected TypedCtor, got {s:?}"),
    }
    ok_stmt("let h = Hash<Sha256>(\"0xab\");");
    // Ordinary identifiers still compare normally.
    ok_stmt("require x < 32;");
}

#[test]
fn empty_array_literal_rejected() {
    let codes = err_stmt("let a = [];");
    assert!(codes.contains(&"parse/array-empty"), "{codes:?}");
}

#[test]
fn none_outside_keypath_rejected() {
    let codes = err_stmt("let a = None;");
    assert!(codes.contains(&"parse/none-position"), "{codes:?}");
}

// --- comprehensions ---

#[test]
fn comprehension_forms() {
    ok_stmt("let s = sum(x in xs => x);");
    ok_stmt("let s = sum(i in 0..784 => i);");
    ok_stmt("let s = sum(px in drawing, w in weights where px => w);");
    ok_stmt("let s = sum(k in keys, s2 in sigs => k.check(s2));");
    ok_stmt("let s = fold(acc = 0, x in xs => acc + x);");
    ok_stmt("let s = all(x in xs where x > 0, x < 9 => x != 5);");
}

#[test]
fn comprehension_nested() {
    // Inner `=>` sits at depth 2 for the outer call and depth 1 for the inner.
    ok_stmt("let s = sum(x in xs => count(y in ys => y > x));");
    // A plain call whose argument is a comprehension stays a plain call.
    let c = ok_stmt("let s = abs(sum(x in xs => x));");
    match first_stmt(&c) {
        Stmt::Let {
            value: Expr::Call { callee, args, .. },
            ..
        } => {
            assert!(matches!(callee.as_ref(), Expr::Name(n) if n.text == "abs"));
            assert!(matches!(args[0].value, Expr::Comprehension { .. }));
        }
        s => panic!("{s:?}"),
    }
}

#[test]
fn comprehension_acc_rules() {
    let codes = err_stmt("let s = fold(x in xs, acc = 0 => acc);");
    assert!(codes.contains(&"parse/comp-acc-order"), "{codes:?}");
    let codes = err_stmt("let s = fold(a = 0, b = 1, x in xs => x);");
    assert!(codes.contains(&"parse/comp-acc-dup"), "{codes:?}");
    let codes = err_stmt("let s = fold(acc = 0 => acc);");
    assert!(codes.contains(&"parse/comp-no-binder"), "{codes:?}");
}

#[test]
fn comprehension_callee_must_be_name() {
    let codes = err_stmt("let s = a.b(x in xs => x);");
    assert!(codes.contains(&"parse/comp-callee"), "{codes:?}");
}

// --- reserved tokens teach, in context ---

#[test]
fn reserved_tokens_teach() {
    // The headline names what is unavailable; the supported alternative is a
    // help note (so each reserved token must carry one).
    for (src, needle) in [
        ("require a && b;", "boolean operators are not available"),
        ("require a || b;", "boolean operators are not available"),
        ("let x = a * b;", "multiplication"),
        ("let x = a / b;", "division"),
        ("require x in 0...10;", "is not a range operator"),
    ] {
        let full =
            format!("contract T {{ spend f(a: Int, b: Int, x: Int) {{ {src} }} keypath None; }}");
        let (_, diags) = parse_source(&full);
        assert!(
            diags.iter().any(|d| d.code == "parse/reserved"
                && d.message.contains(needle)
                && !d.notes.is_empty()),
            "for {src:?}: {diags:#?}"
        );
    }
}

#[test]
fn if_keyword_teaches() {
    let codes = err_stmt("let x = if c { 1 } else { 0 };");
    assert!(codes.contains(&"parse/reserved"), "{codes:?}");
}

#[test]
fn recovery_is_brace_aware_no_cascade() {
    // One bad statement (containing braces) + one bad require = exactly two
    // teaching diagnostics and nothing else. No cascade from the `{ 1 }`.
    let (_, diags) = parse_source(
        "contract Bad {
            spend f(a: Bool, b: Bool, c: Bool, s: Signature) {
                let x = if c { 1 } else { 0 };
                require a && b;
            }
            keypath None;
        }",
    );
    let codes: Vec<_> = diags.iter().map(|d| d.code).collect();
    assert_eq!(
        codes,
        vec!["parse/reserved", "parse/reserved"],
        "expected exactly two teaching diagnostics, got: {diags:#?}"
    );
    assert!(
        diags[0].message.contains("`if` is not available"),
        "{:?}",
        diags[0].message
    );
    assert!(
        diags[1]
            .message
            .contains("boolean operators are not available"),
        "{:?}",
        diags[1].message
    );
}

// --- totality: the item/stmt loops must ALWAYS make forward progress ---

#[test]
fn recovery_loops_terminate_no_unbounded_diagnostics() {
    // A parse arm that errors WITHOUT consuming a token, while a recovery
    // anchor sits on the same token, spun the item loop forever: append-only
    // diagnostics turned that into an out-of-memory crash, not a hang. The
    // forward-progress guard makes it structurally impossible.
    // Every input here must return promptly with a BOUNDED diagnostic count.
    let adversarial = [
        "contract T { layout { keypath: None } }", // the exact crash input
        "contract T { layout layout layout keypath None; }",
        "contract T { @ @ @ keypath None; }",
        "contract T { keypath keypath keypath }",
        "contract T { spend f() { } } } } keypath None;",
        "contract T { = = = ; ; ; }",
        "contract T { @depth @weight spend }",
    ];
    for src in adversarial {
        let (_, diags) = parse_source(src);
        // Terminates (no hang/OOM) AND stays bounded by input size.
        assert!(
            diags.len() <= 4 * src.len(),
            "diagnostic count {} unbounded for {src:?}",
            diags.len()
        );
    }
    // The canonical migration input gives exactly the teaching diagnostic.
    let codes = err("contract T { layout { keypath: None } }");
    assert!(codes.contains(&"parse/layout-removed"), "{codes:?}");
}

// --- totality under adversarial nesting (the stack is part of totality) ---

#[test]
fn deep_nesting_is_a_diagnostic_not_a_crash() {
    // 10,000 levels of each recursive construct: must produce `parse/depth`,
    // never a stack overflow.
    let parens = format!("require {}x{};", "(".repeat(10_000), ")".repeat(10_000));
    let codes = err_stmt(&parens);
    assert!(codes.contains(&"parse/depth"), "{codes:?}");

    let ty = format!(
        "contract T {{ extern const k: {}Int{}; keypath None; }}",
        "[".repeat(10_000),
        "; 1]".repeat(10_000)
    );
    let codes = err(&ty);
    assert!(codes.contains(&"parse/depth"), "{codes:?}");
}

#[test]
fn long_chains_are_bounded_like_nesting() {
    // Chains build AST height too (drop glue recurses over them), so they
    // draw on the same budget: long runs are diagnostics, never overflows,
    // at parse time or at drop time.
    let unary = format!("require {}x;", "!".repeat(100_000));
    let codes = err_stmt(&unary);
    assert!(codes.contains(&"parse/depth"), "{codes:?}");

    let additive = format!("let s = x{};", " + x".repeat(100_000));
    let codes = err_stmt(&additive);
    assert!(codes.contains(&"parse/depth"), "{codes:?}");

    let members = format!("require x{};", ".m".repeat(100_000));
    let codes = err_stmt(&members);
    assert!(codes.contains(&"parse/depth"), "{codes:?}");

    // Realistic sizes sit far under the bound (corpus nesting maxes at ~4).
    let fine = format!("require {}x;", "!".repeat(40));
    ok_stmt(&fine);
    let fine = format!("let s = x{};", " + x".repeat(40));
    ok_stmt(&fine);
    let fine = format!("require {}x{};", "(".repeat(40), ")".repeat(40));
    ok_stmt(&fine);
}

// --- recovery: multiple independent errors in one run ---

#[test]
fn recovery_reports_multiple_errors() {
    let (_, diags) = parse_source(
        "contract T {
            spend f(x: Int) {
                let a = ;
                require x > 0;
                let b = [];
            }
            keypath None;
        }",
    );
    let errors: Vec<_> = diags.iter().map(|d| d.code).collect();
    assert!(
        errors.len() >= 2,
        "expected two independent errors, got {errors:?}"
    );
    assert!(errors.contains(&"parse/array-empty"), "{errors:?}");
}
