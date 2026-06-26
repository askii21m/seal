//! Corpus gate: every example must lex cleanly, forever.
//!
//! The golden corpus (`tests/corpus/*.sl`) is the permanent acceptance suite:
//! these four contracts exercise the full settled surface.

use seal::syntax::lexer::{lex, verify_token_stream_invariants};
use seal::syntax::token::TokenKind;

const CORPUS: [&str; 4] = ["vault.sl", "htlc.sl", "multisig.sl", "cat_bounty.sl"];

fn corpus_path(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/corpus")
        .join(name)
}

#[test]
fn corpus_lexes_clean() {
    for name in CORPUS {
        let src = std::fs::read_to_string(corpus_path(name))
            .unwrap_or_else(|e| panic!("reading {name}: {e}"));
        let (tokens, diags) = lex(&src);

        verify_token_stream_invariants(&src, &tokens)
            .unwrap_or_else(|e| panic!("{name}: token invariants violated: {e}"));

        assert!(
            diags.is_empty(),
            "{name}: expected clean lex, got diagnostics: {:#?}",
            diags
        );

        // The corpus must never contain a reserved token: the examples are
        // the language's showcase of what is allowed, not what is refused.
        for t in &tokens {
            if let TokenKind::Reserved(r) = &t.kind {
                panic!(
                    "{name}: reserved token {r:?} at {:?}; corpus must be idiomatic",
                    t.span
                );
            }
        }

        // Substance check: a contract is not three tokens long.
        assert!(
            tokens.len() > 40,
            "{name}: suspiciously few tokens ({})",
            tokens.len()
        );
    }
}

#[test]
fn corpus_spot_checks() {
    // cat_bounty: the zip comprehension with a `where` filter is the central
    // line: `sum(px in drawing, w in weights where px => w)`.
    let src = std::fs::read_to_string(corpus_path("cat_bounty.sl")).unwrap();
    let (tokens, _) = lex(&src);
    let has = |k: &TokenKind| tokens.iter().any(|t| t.kind == *k);
    assert!(
        has(&TokenKind::Where),
        "cat_bounty: `where` filter expected"
    );
    assert!(
        has(&TokenKind::FatArrow),
        "cat_bounty: comprehension `=>` expected"
    );
    assert!(has(&TokenKind::In), "cat_bounty: binder `in` expected");
    assert!(
        has(&TokenKind::Relaxed),
        "cat_bounty: `relaxed` modifier expected"
    );

    // multisig: chained comparison `1 <= M <= N` yields two Le tokens.
    let src = std::fs::read_to_string(corpus_path("multisig.sl")).unwrap();
    let (tokens, _) = lex(&src);
    let le_count = tokens.iter().filter(|t| t.kind == TokenKind::Le).count();
    assert!(
        le_count >= 2,
        "multisig should contain the chained comparison"
    );

    // htlc: the pinned tree is now plain `script:`. The `@` token left the
    // corpus when `@override` was retired (its lexer arm stays for the
    // migration diagnostic; see every_punctuation_token_is_producible).
    let src = std::fs::read_to_string(corpus_path("htlc.sl")).unwrap();
    let (tokens, _) = lex(&src);
    assert!(
        !tokens.iter().any(|t| t.kind == TokenKind::At),
        "htlc: no `@` expected after the @override retirement"
    );
}
