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

#[test]
fn leaf_descriptors_are_canonical_miniscript() {
    // The per-leaf Miniscript descriptor Seal emits for each spend, derived from
    // the predicate in canonical order. The differential harness gates the whole
    // expressible fragment against rust-miniscript (parse the descriptor,
    // re-encode, require it equals Seal's own leaf, 1000/1000); these goldens
    // lock the corpus shapes in-repo so the emitter cannot drift.
    let cases: &[(&str, &[&str])] = &[
        (
            "htlc",
            &[
                "and_v(v:sha256(abababababababababababababababababababababababababababababababab),pk(5cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc))",
                "and_v(v:pk(2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c),after(900000))",
            ],
        ),
        (
            "vault",
            &[
                "and_v(v:pk(2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c),older(4320))",
                "and_v(v:pk(f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8),older(12960))",
            ],
        ),
        (
            "multisig",
            &[
                "multi_a(2,2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c,5cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc,f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8)",
            ],
        ),
    ];
    for (name, want) in cases {
        let src = read(&format!("{name}.sl"));
        let args = read(&format!("{name}.args.json"));
        let result = compile(&src, Some(&args), Target::Fund, CompileOptions::default());
        let got: Vec<String> = result
            .descriptors
            .expect("descriptors present after lowering")
            .into_iter()
            .map(|d| d.expect("corpus leaf is Miniscript-expressible"))
            .collect();
        assert_eq!(
            got.iter().map(String::as_str).collect::<Vec<_>>(),
            *want,
            "{name} leaf descriptors"
        );
    }
}

#[test]
fn malleable_threshold_emits_no_descriptor() {
    // `>= M` / `> M` key thresholds are malleable: a third party can strip an
    // excess signature, dropping the count but keeping it above the bound, for a
    // different valid witness. Miniscript's multi_a is exactly-M for that reason,
    // so a `>= M` leaf is NOT a descriptor. The emitter must refuse to name one
    // rather than emit a multi_a that points at a different address than Seal funds.
    let keys = r#"{"keys":["0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c","0x5cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc","0xf28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8"]}"#;
    for op in [">=", ">"] {
        let src = format!(
            "contract M {{ extern const keys: [PublicKey; 3];
                spend f(sigs: [Signature; 3]) {{
                    require sum(k in keys, s in sigs => k.check(s)) {op} 2;
                }} keypath None; }}"
        );
        let result = compile(&src, Some(keys), Target::Fund, CompileOptions::default());
        assert_eq!(
            result.descriptors.expect("lowered"),
            vec![None],
            "`{op} M` must emit no descriptor"
        );
    }
}

#[test]
fn malleable_threshold_warns_pointing_at_eq() {
    // `>= M` / `> M` key thresholds with M below the slot count are malleable;
    // the gate warns (and points at `== M`) rather than silently implying
    // non-malleability. `== M`, and `>= n` (n-of-n, no excess), do not warn.
    let keys = r#"{"keys":["0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c","0x5cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc","0xf28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8"]}"#;
    let warns = |op: &str| {
        let src = format!(
            "contract M {{ extern const keys: [PublicKey; 3];
                spend f(sigs: [Signature; 3]) {{
                    require sum(k in keys, s in sigs => k.check(s)) {op};
                }} keypath None; }}"
        );
        let result = compile(&src, Some(keys), Target::Fund, CompileOptions::default());
        result_to_json(&result, &src, Some(keys)).contains("malleability/threshold")
    };
    assert!(warns(">= 2"), "`>= 2` of 3 is malleable");
    assert!(warns("> 1"), "`> 1` of 3 is malleable");
    assert!(!warns("== 2"), "`== 2` is non-malleable");
    assert!(!warns(">= 3"), "`>= 3` is n-of-n, non-malleable");
}

#[test]
fn contract_tr_descriptor_is_the_full_taproot() {
    // The full importable descriptor: tr(internal_key, {taptree}), with each leaf
    // its Miniscript. rust-miniscript parsing this yields Seal's exact taproot
    // output key (verified in the differential harness, corpus + generated); these
    // goldens lock the corpus, including the NUMS (htlc/vault) and the MuSig2
    // aggregate (multisig) internal keys.
    let cases: &[(&str, &str)] = &[
        (
            "htlc",
            "tr(1319173b03c7cea0bdb834bc39f53d668d4add15531e18b86532d9e4ef83b6ea,{and_v(v:sha256(abababababababababababababababababababababababababababababababab),pk(5cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc)),and_v(v:pk(2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c),after(900000))})",
        ),
        (
            "vault",
            "tr(1319173b03c7cea0bdb834bc39f53d668d4add15531e18b86532d9e4ef83b6ea,{and_v(v:pk(2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c),older(4320)),and_v(v:pk(f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8),older(12960))})",
        ),
        (
            "multisig",
            "tr(e2bdbdbb8fcfc4476f4a5fd6388dd43d5ed311e9d7d794611d4969d2edd78efe,multi_a(2,2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c,5cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc,f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8))",
        ),
    ];
    for (name, want) in cases {
        let src = read(&format!("{name}.sl"));
        let args = read(&format!("{name}.args.json"));
        let result = compile(&src, Some(&args), Target::Fund, CompileOptions::default());
        let json = result_to_json(&result, &src, Some(&args));
        assert!(
            json.contains(&format!("\"descriptor\":\"{want}\"")),
            "{name} contract descriptor missing or wrong"
        );
    }
}
