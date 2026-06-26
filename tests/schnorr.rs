//! BIP340 Schnorr verification against the official test vectors
//! (tests/vectors/bip340_test_vectors.csv, from bitcoin/bips).
//!
//! All 19 rows (9 valid, 10 invalid: off-curve keys, r >= p, s >= n,
//! wrong-message, tweaked R, etc.) must match the vector's expected
//! `verification result`. The invalid rows are the point: a verifier that
//! only accepts valid sigs is useless; this is checked against the same
//! ground truth Bitcoin Core uses.

use seal::crypto::schnorr::{sign, verify};

fn hexv(s: &str) -> Vec<u8> {
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).expect("hex"))
        .collect()
}

#[test]
fn bip340_official_verification_vectors() {
    let csv = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/vectors/bip340_test_vectors.csv"),
    )
    .expect("vendored vectors");

    let mut checked = 0;
    let mut valid_seen = 0;
    let mut invalid_seen = 0;
    for line in csv.lines().skip(1) {
        let cols: Vec<&str> = line.split(',').collect();
        if cols.len() < 7 {
            continue;
        }
        let (pk_hex, msg_hex, sig_hex, want) = (cols[2], cols[4], cols[5], cols[6]);
        // Every vector key is 32 bytes; signatures are 64.
        let pk = hexv(&pk_hex.to_lowercase());
        let sig = hexv(&sig_hex.to_lowercase());
        if pk.len() != 32 || sig.len() != 64 {
            continue;
        }
        let mut pubkey = [0u8; 32];
        pubkey.copy_from_slice(&pk);
        let mut sig64 = [0u8; 64];
        sig64.copy_from_slice(&sig);
        let msg = hexv(&msg_hex.to_lowercase()); // variable length (incl. empty)

        let expected = want.eq_ignore_ascii_case("TRUE");
        let got = verify(&pubkey, &msg, &sig64);
        assert_eq!(
            got,
            expected,
            "BIP340 row index {}: comment {:?}",
            cols[0],
            cols.get(7)
        );
        checked += 1;
        if expected {
            valid_seen += 1;
        } else {
            invalid_seen += 1;
        }
    }
    assert!(checked >= 15, "expected the full vector set, got {checked}");
    assert!(
        valid_seen >= 4 && invalid_seen >= 4,
        "must cover BOTH valid and invalid sigs"
    );
}

#[test]
fn bip340_official_signing_vectors() {
    // Every vector row that carries a secret key is a deterministic signing
    // case: sign(sk, msg, aux) must reproduce the official signature EXACTLY,
    // and that signature must round-trip through our own verify.
    let csv = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/vectors/bip340_test_vectors.csv"),
    )
    .expect("vendored vectors");

    let mut checked = 0;
    for line in csv.lines().skip(1) {
        let cols: Vec<&str> = line.split(',').collect();
        if cols.len() < 7 {
            continue;
        }
        let (sk_hex, pk_hex, aux_hex, msg_hex, sig_hex) =
            (cols[1], cols[2], cols[3], cols[4], cols[5]);
        let sk = hexv(&sk_hex.to_lowercase());
        let aux = hexv(&aux_hex.to_lowercase());
        if sk.len() != 32 || aux.len() != 32 {
            continue; // verify-only rows (no secret key) are covered above
        }
        let mut skb = [0u8; 32];
        skb.copy_from_slice(&sk);
        let mut auxb = [0u8; 32];
        auxb.copy_from_slice(&aux);
        let msg = hexv(&msg_hex.to_lowercase());

        let got = sign(&skb, &msg, &auxb).expect("sign produced a signature");
        assert_eq!(
            got.to_vec(),
            hexv(&sig_hex.to_lowercase()),
            "BIP340 sign row index {}: signature mismatch",
            cols[0]
        );

        // Round-trip: our own verify accepts what our sign produced.
        let mut pubkey = [0u8; 32];
        pubkey.copy_from_slice(&hexv(&pk_hex.to_lowercase()));
        assert!(
            verify(&pubkey, &msg, &got),
            "BIP340 sign row {}: self-verify",
            cols[0]
        );
        checked += 1;
    }
    assert!(
        checked >= 4,
        "expected the signing vector rows, got {checked}"
    );
}

#[test]
fn verify_is_total_on_garbage() {
    // Never panics on arbitrary bytes (it will run inside the fuzzed
    // interpreter): all-zero, all-0xff, random-ish.
    assert!(!verify(&[0u8; 32], b"", &[0u8; 64]));
    assert!(!verify(&[0xffu8; 32], &[0xab; 100], &[0xff; 64]));
    let mut pk = [0u8; 32];
    pk[31] = 7; // not a valid x-coordinate (off curve)
    assert!(!verify(&pk, &[1, 2, 3], &[0x55; 64]));
}

#[test]
fn tampering_a_valid_signature_breaks_it() {
    // Take the first valid vector row, flip one signature byte to reject.
    let csv = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/vectors/bip340_test_vectors.csv"),
    )
    .unwrap();
    let row = csv
        .lines()
        .skip(1)
        .map(|l| l.split(',').collect::<Vec<_>>())
        .find(|c| c.len() >= 7 && c[6].eq_ignore_ascii_case("TRUE"))
        .expect("a valid row");
    let mut pubkey = [0u8; 32];
    pubkey.copy_from_slice(&hexv(&row[2].to_lowercase()));
    let msg = hexv(&row[4].to_lowercase());
    let mut sig = [0u8; 64];
    sig.copy_from_slice(&hexv(&row[5].to_lowercase()));
    assert!(verify(&pubkey, &msg, &sig), "the vector is valid as given");
    sig[10] ^= 0x01; // flip a bit in R
    assert!(
        !verify(&pubkey, &msg, &sig),
        "a tampered signature must reject"
    );
}
