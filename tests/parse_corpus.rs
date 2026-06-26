//! Corpus gate for the parser: every corpus contract must parse clean, forever,
//! plus prefix totality: the parser must never panic on ANY truncation of any
//! corpus file (every byte boundary that is a char boundary).

use seal::syntax::ast::{Item, Keypath, Stmt};
use seal::syntax::parser::parse_source;

const CORPUS: [&str; 4] = ["vault.sl", "htlc.sl", "multisig.sl", "cat_bounty.sl"];

fn read(name: &str) -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/corpus")
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("reading {name}: {e}"))
}

#[test]
fn corpus_parses_clean() {
    for name in CORPUS {
        let src = read(name);
        let (contract, diags) = parse_source(&src);
        assert!(
            diags.is_empty(),
            "{name}: expected clean parse, got: {diags:#?}"
        );
        let c = contract.unwrap_or_else(|| panic!("{name}: no contract produced"));

        // Every corpus contract has at least one spend and exactly one layout.
        let spends: Vec<_> = c
            .items
            .iter()
            .filter_map(|i| match i {
                Item::Spend(s) => Some(s),
                _ => None,
            })
            .collect();
        let keypaths: Vec<_> = c
            .items
            .iter()
            .filter_map(|i| match i {
                Item::Keypath(kp) => Some(kp),
                _ => None,
            })
            .collect();
        assert!(!spends.is_empty(), "{name}: no spends");
        assert_eq!(keypaths.len(), 1, "{name}: expected exactly one keypath");
    }
}

#[test]
fn corpus_structural_spot_checks() {
    // vault: two spends; keypath is a key expression (MuSig2 aggregate).
    let (c, _) = parse_source(&read("vault.sl"));
    let c = c.unwrap();
    assert_eq!(c.name.text, "Vault");
    let keypath = c
        .items
        .iter()
        .find_map(|i| match i {
            Item::Keypath(kp) => Some(kp),
            _ => None,
        })
        .unwrap();
    assert!(
        matches!(keypath, Keypath::Key(_)),
        "vault keypath should be MuSig2"
    );

    // cat_bounty: NUMS key path (`keypath None`).
    let (c, _) = parse_source(&read("cat_bounty.sl"));
    let c = c.unwrap();
    let keypath = c
        .items
        .iter()
        .find_map(|i| match i {
            Item::Keypath(kp) => Some(kp),
            _ => None,
        })
        .unwrap();
    assert!(
        matches!(keypath, Keypath::None(_)),
        "cat_bounty keypath should be None (NUMS)"
    );

    // multisig: a contract-scope precondition and a comprehension threshold.
    let (c, _) = parse_source(&read("multisig.sl"));
    let c = c.unwrap();
    assert!(
        c.items.iter().any(|i| matches!(i, Item::Precondition(_))),
        "multisig: template precondition expected"
    );

    // cat_bounty: claim has a relaxed param; body is let + require (in order).
    let (c, _) = parse_source(&read("cat_bounty.sl"));
    let c = c.unwrap();
    let claim = c
        .items
        .iter()
        .find_map(|i| match i {
            Item::Spend(s) if s.name.text == "claim" => Some(s),
            _ => None,
        })
        .unwrap();
    assert!(claim.params[0].relaxed, "drawing must be `relaxed`");
    assert!(matches!(claim.body[0], Stmt::Let { .. }));
    assert!(matches!(claim.body[1], Stmt::Require(_)));
    match &claim.body[0] {
        Stmt::Let { value, .. } => {
            // bias + sum(px in drawing, w in weights where px => w)
            let s = format!("{value:?}");
            assert!(
                s.contains("Comprehension"),
                "score should contain the comprehension"
            );
        }
        _ => unreachable!(),
    }
}

/// Prefix totality: parsing any truncation of any corpus file must not panic
/// (and must uphold the lexer's invariants on the way). This is the cheap,
/// deterministic stand-in for a fuzzer, run on every `cargo test`.
#[test]
fn corpus_prefix_totality() {
    for name in CORPUS {
        let src = read(name);
        for end in 0..=src.len() {
            if !src.is_char_boundary(end) {
                continue;
            }
            let prefix = &src[..end];
            let _ = parse_source(prefix); // must not panic
        }
    }
}
