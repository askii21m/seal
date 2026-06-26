//! Bech32m (BIP350) P2TR address encoding, witness v1.
//!
//! The seven BIP341 wallet vectors each carry the expected `bip350Address`,
//! and tests/taproot.rs asserts every one byte-for-byte. Structural property
//! tests (round-trip, checksum sensitivity) live in the same suite.

const CHARSET: &[u8; 32] = b"qpzry9x8gf2tvdw0s3jn54khce6mua7l";
const GEN: [u32; 5] = [
    0x3b6a_57b2,
    0x2650_8e6d,
    0x1ea1_19fa,
    0x3d42_33dd,
    0x2a14_62b3,
];
/// The bech32m checksum constant (BIP350; bech32 used 1).
const BECH32M_CONST: u32 = 0x2bc8_30a3;

fn polymod(values: &[u8]) -> u32 {
    let mut chk: u32 = 1;
    for &v in values {
        let b = chk >> 25;
        chk = (chk & 0x1ff_ffff) << 5 ^ v as u32;
        for (i, g) in GEN.iter().enumerate() {
            if (b >> i) & 1 == 1 {
                chk ^= g;
            }
        }
    }
    chk
}

fn hrp_expand(hrp: &str) -> Vec<u8> {
    let mut v: Vec<u8> = hrp.bytes().map(|c| c >> 5).collect();
    v.push(0);
    v.extend(hrp.bytes().map(|c| c & 31));
    v
}

/// 8-bit to 5-bit regrouping with padding (the encode direction).
fn convert_to_5bit(data: &[u8]) -> Vec<u8> {
    let mut acc: u32 = 0;
    let mut bits = 0u32;
    let mut out = Vec::with_capacity(data.len() * 8 / 5 + 1);
    for &b in data {
        acc = (acc << 8) | b as u32;
        bits += 8;
        while bits >= 5 {
            bits -= 5;
            out.push(((acc >> bits) & 31) as u8);
        }
    }
    if bits > 0 {
        out.push(((acc << (5 - bits)) & 31) as u8);
    }
    out
}

/// Encode a witness-v1 (taproot) program as a bech32m address.
/// `hrp` is "bc" for mainnet (the only v1 target).
pub fn encode_p2tr(hrp: &str, program: &[u8; 32]) -> String {
    let mut data = vec![1u8]; // witness version 1
    data.extend(convert_to_5bit(program));
    let mut values = hrp_expand(hrp);
    values.extend(&data);
    values.extend([0u8; 6]);
    let chk = polymod(&values) ^ BECH32M_CONST;
    let mut s = String::with_capacity(hrp.len() + 1 + data.len() + 6);
    s.push_str(hrp);
    s.push('1');
    for d in &data {
        s.push(CHARSET[*d as usize] as char);
    }
    for i in 0..6 {
        let idx = ((chk >> (5 * (5 - i))) & 31) as usize;
        s.push(CHARSET[idx] as char);
    }
    s
}

/// Checksum validity for a bech32m string. Used by structural tests and the
/// `seal test` harness; not a full address decoder.
pub fn verify_checksum(s: &str) -> bool {
    let Some((hrp, data)) = s.rsplit_once('1') else {
        return false;
    };
    if hrp.is_empty() || data.len() < 6 {
        return false;
    }
    let mut values = hrp_expand(&hrp.to_lowercase());
    for c in data.bytes() {
        let Some(pos) = CHARSET.iter().position(|&x| x == c.to_ascii_lowercase()) else {
            return false;
        };
        values.push(pos as u8);
    }
    polymod(&values) == BECH32M_CONST
}
