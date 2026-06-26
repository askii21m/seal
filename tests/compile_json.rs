//! The structured JSON output (`compile::result_to_json`) -- the surface a
//! fully-client-side web IDE consumes. These pin that the result carries the
//! fields a frontend needs (address, per-leaf certification, the gate verdict,
//! diagnostics with line/col) and, critically, that a REFUSED contract emits no
//! address. The serializer's well-formedness and escaping are unit-tested in
//! `json.rs`; here we assert structure via substrings.

use seal::compile::{CompileOptions, Target, compile, result_to_json};

fn examples() -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/corpus")
}

fn read(name: &str) -> String {
    std::fs::read_to_string(examples().join(name)).unwrap()
}

#[test]
fn proven_contract_json_has_address_and_certification() {
    let src = read("multisig.sl");
    let args = read("multisig.args.json");
    let result = compile(&src, Some(&args), Target::Fund, CompileOptions::default());
    let json = result_to_json(&result, &src, Some(&args));

    assert!(
        json.starts_with('{') && json.ends_with('}'),
        "must be a JSON object: {json}"
    );
    assert!(json.contains(r#""ok":true"#), "expected ok:true: {json}");
    assert!(
        json.contains(r#""address":"bc1p"#),
        "expected a mainnet p2tr address: {json}"
    );
    assert!(
        json.contains(r#""mayProceed":true"#),
        "gate must allow a proven contract: {json}"
    );
    assert!(
        json.contains(r#""assurance":"#),
        "expected per-leaf certification: {json}"
    );
    assert!(
        json.contains(r#""leaves":["#),
        "expected the lowered leaves: {json}"
    );
    assert!(
        json.contains(r#""outputKey":"#),
        "expected the taproot output key: {json}"
    );
    assert!(
        json.contains(r#""lockfile":"#),
        "expected the lockfile: {json}"
    );
}

#[test]
fn unproven_contract_json_refuses_address() {
    // The gate fixture: two unbounded `relaxed` Int witnesses (a < b) cannot be
    // exhausted, so the gate refuses and NO address is emitted -- the JSON must
    // reflect the refusal, never a fundable address.
    let src = "contract U {\n  extern const k: PublicKey;\n  \
        spend f(relaxed a: Int, relaxed b: Int, s: Signature) {\n    \
        require { a < b, k.check(s) }\n  }\n  keypath None;\n}\n";
    let args =
        "{ \"k\": \"0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c\" }\n";
    let result = compile(src, Some(args), Target::Fund, CompileOptions::default());
    let json = result_to_json(&result, src, Some(args));

    assert!(
        json.contains(r#""mayProceed":false"#),
        "gate must refuse: {json}"
    );
    assert!(
        json.contains(r#""assurance":"unproven""#),
        "leaf must be unproven: {json}"
    );
    assert!(
        !json.contains(r#""address":"#),
        "a refused contract must emit NO address: {json}"
    );
}

#[test]
fn parse_error_json_is_not_ok_with_line_col() {
    // A syntactically broken contract: diagnostics present, ok:false, and each
    // diagnostic carries a 1-based line/col for editor placement.
    let src = "contract {{{ this is not valid";
    let result = compile(src, None, Target::Check, CompileOptions::default());
    let json = result_to_json(&result, src, None);

    assert!(
        json.contains(r#""ok":false"#),
        "a broken parse must not be ok: {json}"
    );
    assert!(
        json.contains(r#""severity":"error""#),
        "expected an error diagnostic: {json}"
    );
    assert!(
        json.contains(r#""line":1"#),
        "expected line/col on the diagnostic: {json}"
    );
}
