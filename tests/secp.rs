//! secp256k1 correctness gates.
//!
//! Three independent ground truths must agree with this implementation:
//! 1. the official BIP340 test vectors (Bitcoin Core's own ground truth):
//!    every (secret key, public key) row is a k*G check;
//! 2. an independent from-scratch python reference (big-int arithmetic):
//!    field add/sub/mul/inv, sqrt, k*G, point addition, k*H;
//! 3. algebraic identities that don't depend on either: n*G = infinity,
//!    (n-1)*G = -G (same x, odd y), 5G + 7G = 12G.

use seal::crypto::secp::{N, Point, U256, generator};

fn u(hex: &str) -> U256 {
    let mut b = [0u8; 32];
    for i in 0..32 {
        b[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).expect("hex");
    }
    U256::from_be_bytes(&b)
}

fn hex32(b: [u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

#[test]
fn k_g_python_differential_vectors() {
    // (k, x, y-parity) from the independent python reference.
    let cases = [
        (
            "0000000000000000000000000000000000000000000000000000000000000001",
            "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798",
            true, // y = 483a... even
        ),
        (
            "0000000000000000000000000000000000000000000000000000000000000002",
            "c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5",
            true, // 1ae1... even
        ),
        (
            "0000000000000000000000000000000000000000000000000000000000000003",
            "f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9",
            true, // 388f... even
        ),
        (
            "00000000000000000000000000000000000000000000000000000000deadbeef",
            "76d2fdf1302d1fa9556f4df94ec84cefba6d482e54f47c6c2a238c1baa560f0e",
            true, // b754...8a even
        ),
        (
            "6ab9f1eb8f7d3388f4f9d586f66e99fd54080df2c446f0e58668b09c08a16dd0",
            "669b8afcec803a0d323e9a17f3ea8e68e8abe5a278020a929adbec52421adbd0",
            false, // aab1...ed odd
        ),
        (
            "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140",
            "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798",
            false, // (n-1)*G = -G: same x as G, odd y (b7c5...77)
        ),
    ];
    for (k, want_x, want_even) in cases {
        let p = generator() * u(k);
        assert_eq!(hex32(p.x_bytes().expect("affine")), want_x, "k = {k}");
        assert_eq!(p.has_even_y(), want_even, "k = {k}");
    }
}

#[test]
fn n_g_is_infinity() {
    assert_eq!(generator() * N, Point::Infinity);
}

#[test]
fn point_addition_python_differential() {
    // 5G + 7G = 12G, all three from the python reference.
    let p5 = generator() * u("0000000000000000000000000000000000000000000000000000000000000005");
    let p7 = generator() * u("0000000000000000000000000000000000000000000000000000000000000007");
    assert_eq!(
        hex32(p5.x_bytes().unwrap()),
        "2f8bde4d1a07209355b4a7250a5c5128e88b84bddc619ab7cba8d569b240efe4"
    );
    assert_eq!(
        hex32(p7.x_bytes().unwrap()),
        "5cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc"
    );
    let sum = p5 + p7;
    assert_eq!(
        hex32(sum.x_bytes().unwrap()),
        "d01115d548e7561b15c38f004d734633687cf4419620095bc5b0f47070afe85a"
    );
    // The y from python (a9f3...27) is odd.
    assert!(!sum.has_even_y());
    // And doubling: G + G must equal 2*G.
    let g2 = generator() + generator();
    assert_eq!(
        hex32(g2.x_bytes().unwrap()),
        "c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5"
    );
}

#[test]
fn lift_x_and_nums_point() {
    // The BIP341 NUMS point H lifts to an even-y point whose y matches
    // the python reference; k*H matches too (the NUMS keypath path).
    let mut hx = [0u8; 32];
    for (i, b) in hx.iter_mut().enumerate() {
        let s = "50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0";
        *b = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).unwrap();
    }
    let h = Point::lift_x(&hx).expect("H is on the curve");
    assert!(h.has_even_y(), "lift_x returns the even-y point");
    assert_eq!(
        hex32(h.x_bytes().unwrap()),
        "50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0"
    );
    let k = u("425177f60337c5ac575deff100b5f20dc674f5a369f79ac61c1e7c45dea49b74");
    let kh = h * k;
    assert_eq!(
        hex32(kh.x_bytes().unwrap()),
        "1e80a63a869d53d9012a4e931e891e5ffcedfe71daa375dba1bcac70c9c94c20"
    );
    // ky = ...2d7e294d ends odd (parity = the low bit).
    assert!(!kh.has_even_y());
}

#[test]
fn lift_x_rejects_off_curve_and_oversized() {
    // x = 5 is not on secp256k1 (5^3+7 = 132 is a non-residue mod p).
    let mut five = [0u8; 32];
    five[31] = 5;
    assert!(Point::lift_x(&five).is_none());
    // x >= p is an invalid field encoding.
    let ff = [0xffu8; 32];
    assert!(Point::lift_x(&ff).is_none());
}

#[test]
fn bip340_official_vectors_k_g() {
    // Every row of the official BIP340 CSV with a secret key is a k*G
    // ground-truth check: pubkey = x(k*G).
    let csv = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/vectors/bip340_test_vectors.csv"),
    )
    .expect("vendored vectors");
    let mut checked = 0;
    for line in csv.lines().skip(1) {
        let cols: Vec<&str> = line.split(',').collect();
        if cols.len() < 3 || cols[1].is_empty() {
            continue;
        }
        let (sk, pk) = (cols[1], cols[2]);
        if sk.len() != 64 {
            continue;
        }
        let p = generator() * u(&sk.to_lowercase());
        assert_eq!(
            hex32(p.x_bytes().expect("affine")),
            pk.to_lowercase(),
            "BIP340 row: sk {sk}"
        );
        checked += 1;
    }
    assert!(
        checked >= 4,
        "expected several secret-key rows, got {checked}"
    );
}

#[test]
fn u256_byte_round_trip() {
    // Field-level differentials live as unit tests inside secp.rs (they
    // reach the private Fe ops); the byte codec is the public surface.
    let v = u("f55ff16f66f43360266b95db6f8fec01d76031054306ae4a4b380598f6cfd114");
    assert_eq!(
        hex32(v.to_be_bytes()),
        "f55ff16f66f43360266b95db6f8fec01d76031054306ae4a4b380598f6cfd114"
    );
    assert!(v.ge(U256::ZERO) && !U256::ZERO.ge(U256::ONE));
}
