//! MuSig2 key aggregation (BIP327 KeySort + KeyAgg): the key-path half
//! of the canonical key-ordering rule. The script-path threshold sorts
//! lexicographically; the key path KeySorts before KeyAgg, so the ADDRESS
//! depends on the key SET in both halves.
//!
//! Only aggregation lives here: signing (nonces, partial signatures) is
//! wallet business and never enters the compiler. See secp.rs's security
//! model, which handles public data only.
//!
//! Ground truth is the official BIP327 key_agg_vectors.json, vendored:
//! valid cases (including the duplicate-key coefficient rule) and the
//! invalid-contribution error cases.
//!
//! # The x-only convention (BIP390 alignment)
//!
//! Seal `PublicKey` values are 32-byte x-only. BIP327 aggregates
//! 33-byte compressed keys. The bridge is the BIP390 `musig()` descriptor
//! convention: an x-only key contributes as its EVEN-Y lift (`02 || x`).

use crate::crypto::secp::{Point, U256, scalar_mod_n};
use crate::crypto::sha256::tagged_hash;

/// BIP327 KeySort: lexicographic order of the compressed encodings.
pub fn key_sort(keys: &mut [[u8; 33]]) {
    keys.sort_unstable();
}

/// BIP327 KeyAgg over compressed keys, in the given order (callers that
/// want set semantics KeySort first). Returns the x-only aggregate.
pub fn key_agg(keys: &[[u8; 33]]) -> Result<[u8; 32], String> {
    if keys.is_empty() {
        return Err("key aggregation needs at least one key".into());
    }
    // Validate every contribution up front (error names the signer).
    let mut points = Vec::with_capacity(keys.len());
    for (i, k) in keys.iter().enumerate() {
        let p = Point::from_compressed(k)
            .ok_or_else(|| format!("signer {i}: invalid public key contribution"))?;
        points.push(p);
    }

    // L = hash of "KeyAgg list" over (pk_1 || ... || pk_n).
    let chunks: Vec<&[u8]> = keys.iter().map(|k| k.as_slice()).collect();
    let l = tagged_hash("KeyAgg list", &chunks);

    // pk2 = the first key differing from keys[0]; keys equal to pk2 get
    // coefficient 1 (the optimization that makes 2-of-2 cheap, BIP327).
    let pk2 = keys.iter().find(|k| **k != keys[0]);

    let mut q = Point::Infinity;
    for (k, p) in keys.iter().zip(&points) {
        let a = if Some(k) == pk2 {
            U256::ONE
        } else {
            let h = tagged_hash("KeyAgg coefficient", &[&l, k.as_slice()]);
            scalar_mod_n(U256::from_be_bytes(&h))
        };
        q = q + (*p * a);
    }
    q.x_bytes()
        .ok_or_else(|| "aggregate key is the point at infinity".to_string())
}

/// The Seal entry point: x-only keys, KeySort, KeyAgg, x-only
/// aggregate. Each x-only key contributes as its even-y lift (`02 || x`,
/// the BIP390 convention).
pub fn aggregate_xonly(keys: &[[u8; 32]]) -> Result<[u8; 32], String> {
    let mut compressed: Vec<[u8; 33]> = keys
        .iter()
        .map(|x| {
            let mut c = [0u8; 33];
            c[0] = 0x02;
            c[1..].copy_from_slice(x);
            c
        })
        .collect();
    key_sort(&mut compressed);
    key_agg(&compressed)
}
