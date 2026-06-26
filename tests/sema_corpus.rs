//! Corpus gate for the semantic checker: every corpus contract must check clean
//! at template level: zero errors, zero warnings.

use seal::analysis::sema;
use seal::syntax::parser::parse_source;

const CORPUS: [&str; 4] = ["vault.sl", "htlc.sl", "multisig.sl", "cat_bounty.sl"];

#[test]
fn corpus_checks_clean() {
    for name in CORPUS {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/corpus")
            .join(name);
        let src = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("reading {name}: {e}"));
        let (contract, parse_diags) = parse_source(&src);
        assert!(
            parse_diags.is_empty(),
            "{name}: parse diagnostics: {parse_diags:#?}"
        );
        let diags = sema::check(&contract.expect("contract"));
        assert!(diags.is_empty(), "{name}: sema diagnostics: {diags:#?}");
    }
}
