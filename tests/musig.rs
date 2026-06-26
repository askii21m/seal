//! MuSig2 KeyAgg against the official BIP327 vectors (vendored), plus the
//! corpus contracts assembling real addresses through the keypath, and
//! the full set-semantics property: permuted key injection yields the
//! identical address (KeySort on the key path plus lexicographic threshold
//! chains on the script path, end to end).

use seal::crypto::musig::{aggregate_xonly, key_agg};
use seal::json::{self, Json};

fn hexv(s: &str) -> Vec<u8> {
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).expect("hex"))
        .collect()
}

fn key32(hex: &str) -> [u8; 32] {
    let v = hexv(hex);
    let mut b = [0u8; 32];
    b.copy_from_slice(&v);
    b
}

fn to_hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn get<'a>(obj: &'a Json, key: &str) -> &'a Json {
    let Json::Object(fields) = obj else {
        panic!("expected object")
    };
    &fields.iter().find(|(k, _)| k == key).expect(key).1
}

#[test]
fn bip327_official_key_agg_vectors() {
    let raw = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/vectors/bip327_key_agg_vectors.json"),
    )
    .expect("vendored vectors");
    let v = json::parse(&raw.replace("null", "\"NULL\"")).expect("parse");

    let Json::Array(pubkeys) = get(&v, "pubkeys") else {
        panic!()
    };
    let keys: Vec<Vec<u8>> = pubkeys
        .iter()
        .map(|k| {
            let Json::Str(s) = k else { panic!() };
            hexv(&s.to_lowercase())
        })
        .collect();
    // Every vector key is exactly 33 bytes (the malformed ones differ in
    // prefix or x-range, not length).
    let key33 = |i: usize| -> [u8; 33] {
        let mut b = [0u8; 33];
        b.copy_from_slice(&keys[i]);
        b
    };

    let Json::Array(valid) = get(&v, "valid_test_cases") else {
        panic!()
    };
    assert_eq!(valid.len(), 4);
    for (i, case) in valid.iter().enumerate() {
        let Json::Array(idx) = get(case, "key_indices") else {
            panic!()
        };
        let input: Vec<[u8; 33]> = idx
            .iter()
            .map(|j| {
                let Json::Int(j) = j else { panic!() };
                key33(*j as usize)
            })
            .collect();
        let Json::Str(want) = get(case, "expected") else {
            panic!()
        };
        let got = key_agg(&input).expect("valid case");
        assert_eq!(to_hex(&got), want.to_lowercase(), "valid case {i}");
    }

    let Json::Array(errors) = get(&v, "error_test_cases") else {
        panic!()
    };
    let mut contribution_cases = 0;
    for (i, case) in errors.iter().enumerate() {
        // Tweak-error cases exercise ApplyTweak, which is signing-side
        // machinery the compiler never performs; only the
        // invalid-contribution cases apply to pure KeyAgg.
        let Json::Array(tweaks) = get(case, "tweak_indices") else {
            panic!()
        };
        if !tweaks.is_empty() {
            continue;
        }
        let Json::Array(idx) = get(case, "key_indices") else {
            panic!()
        };
        let input: Vec<[u8; 33]> = idx
            .iter()
            .map(|j| {
                let Json::Int(j) = j else { panic!() };
                key33(*j as usize)
            })
            .collect();
        let err = key_agg(&input).expect_err("error case");
        let Json::Int(signer) = get(get(case, "error"), "signer") else {
            panic!()
        };
        assert!(
            err.contains(&format!("signer {signer}")),
            "error case {i}: {err}"
        );
        contribution_cases += 1;
    }
    assert_eq!(
        contribution_cases, 3,
        "the three invalid-contribution cases"
    );
}

#[test]
fn key_agg_is_order_sensitive_but_aggregate_xonly_is_not() {
    // KeyAgg itself depends on order (the official vectors prove it);
    // the Seal entry point KeySorts first, so the SET decides.
    let a = key32("2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c");
    let b = key32("5cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc");
    let ab = aggregate_xonly(&[a, b]).expect("agg");
    let ba = aggregate_xonly(&[b, a]).expect("agg");
    assert_eq!(ab, ba, "KeySort makes aggregation set-semantic");
}

#[test]
fn xonly_off_curve_is_rejected() {
    // x = 5 is not on the curve; the even-y lift must fail loudly.
    let mut bad = [0u8; 32];
    bad[31] = 5;
    let err = aggregate_xonly(&[
        key32("2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c"),
        bad,
    ])
    .expect_err("off-curve");
    assert!(err.contains("invalid public key"), "{err}");
}

#[test]
fn off_curve_extern_is_rejected_at_bind() {
    // An off-curve PublicKey extern makes every path that pins it
    // permanently unspendable, and is caught at injection with a clear error.
    let (contract, pd) = seal::syntax::parser::parse_source(
        "contract T {
            extern const k: PublicKey;
            spend f(s: Signature) { require k.check(s); }
            keypath None;
        }",
    );
    assert!(pd.is_empty());
    let c = contract.expect("contract");
    let (sd, info) = seal::analysis::sema::analyze(&c);
    assert!(sd.is_empty());
    let err = seal::analysis::consteval::bind_args(
        &info,
        &json::parse(
            r#"{"k": "0x0000000000000000000000000000000000000000000000000000000000000005"}"#,
        )
        .expect("json"),
    )
    .expect_err("off-curve must fail to bind");
    assert!(err[0].contains("not on the secp256k1 curve"), "{err:?}");
}

/// Permuted key injection produces the identical address, through
/// the entire pipeline: KeySort on the key path, lexicographic consuming
/// chains on the script path (both halves of the rule).
#[test]
fn permuted_multisig_injection_yields_identical_address() {
    fn address(args: &str) -> (String, Vec<String>) {
        let src = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/multisig.sl"),
        )
        .expect("multisig.sl");
        let (contract, pd) = seal::syntax::parser::parse_source(&src);
        assert!(pd.is_empty());
        let c = contract.expect("contract");
        let (sd, info) = seal::analysis::sema::analyze(&c);
        assert!(sd.is_empty());
        let mut env =
            seal::analysis::consteval::bind_args(&info, &json::parse(args).expect("json"))
                .expect("bind");
        let inst = seal::analysis::consteval::instantiate(&c, &mut env);
        assert!(inst.is_empty(), "{inst:#?}");
        let (g1, report) = seal::analysis::intervals::analyze(&c, &env);
        assert!(g1.is_empty());
        let (pdiags, _) = seal::analysis::paths::analyze(&c, &info, &env);
        assert!(
            pdiags
                .iter()
                .all(|d| d.severity != seal::diagnostics::Severity::Error)
        );
        let (ldiags, leaves) = seal::codegen::lower::lower(&c, &info, &env, &report);
        assert!(ldiags.is_empty(), "{ldiags:#?}");
        let out = seal::output::taproot::assemble_contract(&c, &env, &leaves).expect("assemble");
        (
            seal::output::bech32m::encode_p2tr("bc", &out.assembled.output_key),
            leaves[0].witness_order.clone(),
        )
    }

    let a = "0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c";
    let b = "0x5cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc";
    let g = "0xf28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8";
    let (addr1, wit1) = address(&format!(
        r#"{{"M": 2, "N": 3, "keys": ["{a}", "{b}", "{g}"]}}"#
    ));
    let (addr2, wit2) = address(&format!(
        r#"{{"M": 2, "N": 3, "keys": ["{g}", "{a}", "{b}"]}}"#
    ));
    assert_eq!(addr1, addr2, "the address depends on the key SET");
    // Only the witness template (slot to key identity) differs: chain
    // order is sorted-key order, physical layout its reverse. Injection 2
    // pairs sigs[0] with g (sorted last, so deepest), sigs[1] with a (first, so top).
    assert_eq!(wit1, vec!["sigs[2]", "sigs[1]", "sigs[0]"]);
    assert_eq!(wit2, vec!["sigs[0]", "sigs[2]", "sigs[1]"]);
}
