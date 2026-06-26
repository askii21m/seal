//! BIP340 Schnorr signature verification and signing.
//!
//! `verify` provides the interpreter's CHECKSIG with real cryptographic
//! verification. `sign` exists for the test and regtest harnesses (which use
//! disposable test keys to drive the Bitcoin Core differential); the COMPILER
//! holds no secrets and never signs -- signing lives here only so the harness
//! can produce real signatures Core will accept.
//!
//! Both are checked against the BIP340 test vectors
//! (tests/vectors/bip340_test_vectors.csv): every `verify` matches the
//! vector's expected result (including invalid-signature rows), and every
//! `sign` row reproduces the vector's signature exactly (BIP340 signing is
//! deterministic given the auxiliary randomness).
//!
//! Public data only (see secp.rs's security model): variable-time, chosen
//! for auditability.

use crate::crypto::secp::{
    Fe, N, Point, U256, add_mod_n, generator, mul_mod_n, neg_scalar, scalar_mod_n,
};
use crate::crypto::sha256::tagged_hash;

/// BIP340 `Verify(pk, m, sig)`: `pk` is a 32-byte x-only key, `sig` is the
/// 64-byte `bytes(R.x) || bytes(s)`, `m` the (variable-length) message.
/// Returns `false` on any failure (no panics, no error variants).
pub fn verify(pubkey: &[u8; 32], msg: &[u8], sig: &[u8; 64]) -> bool {
    // P = lift_x(int(pk)); fail if x >= p or x is off-curve.
    let Some(p) = Point::lift_x(pubkey) else {
        return false;
    };

    // r = int(sig[0:32]); fail if r >= field size p.
    let mut r_bytes = [0u8; 32];
    r_bytes.copy_from_slice(&sig[0..32]);
    if Fe::from_be_bytes(&r_bytes).is_none() {
        return false;
    }

    // s = int(sig[32:64]); fail if s >= group order n.
    let mut s_bytes = [0u8; 32];
    s_bytes.copy_from_slice(&sig[32..64]);
    let s = U256::from_be_bytes(&s_bytes);
    if s.ge(N) {
        return false;
    }

    // e = int(hash_BIP0340/challenge(bytes(r) || bytes(P) || m)) mod n.
    let Some(px) = p.x_bytes() else { return false };
    let e_bytes = tagged_hash("BIP0340/challenge", &[&r_bytes, &px, msg]);
    let e = scalar_mod_n(U256::from_be_bytes(&e_bytes));

    // R = s*G - e*P.
    let big_r = generator() * s + -(p * e);

    // Accept iff R is finite, has even y, and x(R) == r.
    match big_r {
        Point::Infinity => false,
        affine => affine.has_even_y() && affine.x_bytes() == Some(r_bytes),
    }
}

/// BIP340 `Sign(sk, m, aux)`: the 64-byte signature `bytes(R) || bytes(s)`, or
/// None for an out-of-range secret key or a degenerate (zero) nonce.
/// Deterministic given `aux` (the auxiliary randomness; all-zero is allowed).
/// For the test/regtest harnesses only -- see the module note.
pub fn sign(seckey: &[u8; 32], msg: &[u8], aux: &[u8; 32]) -> Option<[u8; 64]> {
    // d' = int(sk); fail unless 0 < d' < n.
    let d0 = U256::from_be_bytes(seckey);
    if d0.is_zero() || d0.ge(N) {
        return None;
    }
    // P = d'*G; d = d' if P has even y, else n - d' (the x-only convention).
    let pp = generator() * d0;
    let px = pp.x_bytes()?;
    let d = if pp.has_even_y() { d0 } else { neg_scalar(d0) };

    // t = bytes(d) XOR hash_BIP0340/aux(aux).
    let h_aux = tagged_hash("BIP0340/aux", &[aux]);
    let dbytes = d.to_be_bytes();
    let mut t = [0u8; 32];
    for i in 0..32 {
        t[i] = dbytes[i] ^ h_aux[i];
    }

    // k' = int(hash_BIP0340/nonce(t || bytes(P) || m)) mod n; fail if zero.
    let rand = tagged_hash("BIP0340/nonce", &[&t, &px, msg]);
    let k0 = scalar_mod_n(U256::from_be_bytes(&rand));
    if k0.is_zero() {
        return None;
    }
    // R = k'*G; k = k' if R has even y, else n - k'.
    let rr = generator() * k0;
    let rx = rr.x_bytes()?;
    let k = if rr.has_even_y() { k0 } else { neg_scalar(k0) };

    // e = int(hash_BIP0340/challenge(bytes(R) || bytes(P) || m)) mod n.
    let e_bytes = tagged_hash("BIP0340/challenge", &[&rx, &px, msg]);
    let e = scalar_mod_n(U256::from_be_bytes(&e_bytes));

    // s = (k + e*d) mod n.
    let s = add_mod_n(k, mul_mod_n(e, d));
    let mut sig = [0u8; 64];
    sig[0..32].copy_from_slice(&rx);
    sig[32..64].copy_from_slice(&s.to_be_bytes());
    Some(sig)
}
