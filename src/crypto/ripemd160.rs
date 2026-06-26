//! RIPEMD-160: zero-dependency, for `hash160` const-evaluation
//! (`RIPEMD160(SHA256(x))`, the 20-byte commitment form).
//!
//! Correctness gates: the published paper vectors plus a 1000-byte
//! differential generated from python `hashlib` (tests/sha256.rs, one
//! suite for both hash primitives). Public data only; constant-time is a
//! non-goal (see sha256.rs).

/// One-shot RIPEMD-160.
pub fn ripemd160(data: &[u8]) -> [u8; 20] {
    let mut state: [u32; 5] = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];
    let total_bits = (data.len() as u64).wrapping_mul(8);

    let mut iter = data.chunks_exact(64);
    for block in &mut iter {
        let mut b = [0u8; 64];
        b.copy_from_slice(block);
        compress(&mut state, &b);
    }
    // Padding: 0x80, zeros to 56 mod 64, 64-bit LE bit length.
    let rem = iter.remainder();
    let mut last = [0u8; 128];
    last[..rem.len()].copy_from_slice(rem);
    last[rem.len()] = 0x80;
    let blocks = if rem.len() + 9 <= 64 { 1 } else { 2 };
    let end = blocks * 64;
    last[end - 8..end].copy_from_slice(&total_bits.to_le_bytes());
    for i in 0..blocks {
        let mut b = [0u8; 64];
        b.copy_from_slice(&last[i * 64..i * 64 + 64]);
        compress(&mut state, &b);
    }

    let mut out = [0u8; 20];
    for (i, w) in state.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&w.to_le_bytes());
    }
    out
}

fn compress(state: &mut [u32; 5], block: &[u8; 64]) {
    let mut x = [0u32; 16];
    for (i, chunk) in block.chunks_exact(4).enumerate() {
        x[i] = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
    }

    let f = |round: usize, b: u32, c: u32, d: u32| -> u32 {
        match round {
            0 => b ^ c ^ d,
            1 => (b & c) | (!b & d),
            2 => (b | !c) ^ d,
            3 => (b & d) | (c & !d),
            _ => b ^ (c | !d),
        }
    };

    let (mut al, mut bl, mut cl, mut dl, mut el) =
        (state[0], state[1], state[2], state[3], state[4]);
    let (mut ar, mut br, mut cr, mut dr, mut er) =
        (state[0], state[1], state[2], state[3], state[4]);

    for j in 0..80 {
        let round = j / 16;
        // Left line: f1..f5 with K.
        let t = al
            .wrapping_add(f(round, bl, cl, dl))
            .wrapping_add(x[R_L[j] as usize])
            .wrapping_add(K_L[round])
            .rotate_left(S_L[j] as u32)
            .wrapping_add(el);
        al = el;
        el = dl;
        dl = cl.rotate_left(10);
        cl = bl;
        bl = t;
        // Right line: f5..f1 with K'.
        let t = ar
            .wrapping_add(f(4 - round, br, cr, dr))
            .wrapping_add(x[R_R[j] as usize])
            .wrapping_add(K_R[round])
            .rotate_left(S_R[j] as u32)
            .wrapping_add(er);
        ar = er;
        er = dr;
        dr = cr.rotate_left(10);
        cr = br;
        br = t;
    }

    let t = state[1].wrapping_add(cl).wrapping_add(dr);
    state[1] = state[2].wrapping_add(dl).wrapping_add(er);
    state[2] = state[3].wrapping_add(el).wrapping_add(ar);
    state[3] = state[4].wrapping_add(al).wrapping_add(br);
    state[4] = state[0].wrapping_add(bl).wrapping_add(cr);
    state[0] = t;
}

const K_L: [u32; 5] = [0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e];
const K_R: [u32; 5] = [0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000];

/// Message word order, left line.
const R_L: [u8; 80] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, //
    7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8, //
    3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12, //
    1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2, //
    4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13,
];
/// Message word order, right line.
const R_R: [u8; 80] = [
    5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12, //
    6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2, //
    15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13, //
    8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14, //
    12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11,
];
/// Rotation amounts, left line.
const S_L: [u8; 80] = [
    11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8, //
    7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12, //
    11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5, //
    11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12, //
    9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6,
];
/// Rotation amounts, right line.
const S_R: [u8; 80] = [
    8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6, //
    9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11, //
    9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5, //
    15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8, //
    8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11,
];
