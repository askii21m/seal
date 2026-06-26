//! Hash primitive vectors: FIPS 180-4 goldens, the RIPEMD-160 paper
//! vectors, boundary-length inputs (the padding edge at 55/56/64 bytes),
//! and 1000-byte differentials generated from python `hashlib` (an
//! independent implementation). BIP340 tagged-hash forms are pinned here
//! and exercised end-to-end by the BIP341 wallet vectors in
//! tests/taproot.rs.

use seal::crypto::ripemd160::ripemd160;
use seal::crypto::sha256::{sha256, tagged_hash};

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

#[test]
fn sha256_fips_and_differential_vectors() {
    let cases: &[(&[u8], &str)] = &[
        (
            b"",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        ),
        (
            b"abc",
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
        ),
        (
            b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
        ),
    ];
    for (input, want) in cases {
        assert_eq!(hex(&sha256(input)), *want);
    }
    // Padding boundaries: 55 (length fits), 56 (length spills), 64 (exact
    // block), 119 (two-block spill), 1000 (many blocks; python hashlib
    // differential).
    let a = |n: usize| vec![b'a'; n];
    let boundary: &[(usize, &str)] = &[
        (
            55,
            "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318",
        ),
        (
            56,
            "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a",
        ),
        (
            64,
            "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb",
        ),
        (
            119,
            "31eba51c313a5c08226adf18d4a359cfdfd8d2e816b13f4af952f7ea6584dcfb",
        ),
        (
            1000,
            "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3",
        ),
    ];
    for (n, want) in boundary {
        assert_eq!(hex(&sha256(&a(*n))), *want, "length {n}");
    }
}

#[test]
fn sha256_incremental_chunking_is_equivalent() {
    // The incremental state must be insensitive to chunk boundaries.
    let data: Vec<u8> = (0..1024u32).map(|i| (i % 251) as u8).collect();
    let oneshot = sha256(&data);
    for chunk in [1usize, 3, 63, 64, 65, 127, 500] {
        let mut h = seal::crypto::sha256::Sha256::new();
        for c in data.chunks(chunk) {
            h.update(c);
        }
        assert_eq!(h.finalize(), oneshot, "chunk size {chunk}");
    }
}

#[test]
fn tagged_hash_vectors() {
    // tagged(tag, msg) = SHA256(SHA256(tag) || SHA256(tag) || msg).
    // python-generated goldens for the three taproot tags.
    assert_eq!(
        hex(&tagged_hash("TapLeaf", &[])),
        "5212c288a377d1f8164962a5a13429f9ba6a7b84e59776a52c6637df2106facb"
    );
    assert_eq!(
        hex(&tagged_hash("TapBranch", &[&[0u8; 32], &[0u8; 32]])),
        "71631291874b9eaf623c2498caeafabf206ce9125321bd5c9d963bd8a4d91b83"
    );
    assert_eq!(
        hex(&tagged_hash("TapTweak", &[&[0xabu8; 32]])),
        "d13c7d16f74ea2c7cca8d98eb7a47d45759695c7a97945092e307c8adf47b7b9"
    );
}

#[test]
fn ripemd160_paper_and_differential_vectors() {
    let cases: &[(&[u8], &str)] = &[
        (b"", "9c1185a5c5e9fc54612808977ee8f548b2258d31"),
        (b"abc", "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"),
        (
            b"message digest",
            "5d0689ef49d2fae572b881b123a85ffa21595f36",
        ),
    ];
    for (input, want) in cases {
        assert_eq!(hex(&ripemd160(input)), *want);
    }
    // 1000 bytes: many blocks + the two-block padding path (python
    // hashlib differential).
    assert_eq!(
        hex(&ripemd160(&vec![b'a'; 1000])),
        "aa69deee9a8922e92f8105e007f76110f381e9cf"
    );
}

#[test]
fn hash160_composition() {
    // hash160 = RIPEMD160(SHA256(x)): the 20-byte commitment form.
    let h = ripemd160(&sha256(b"seal"));
    assert_eq!(h.len(), 20);
    // Deterministic: same input, same digest.
    assert_eq!(h, ripemd160(&sha256(b"seal")));
}
