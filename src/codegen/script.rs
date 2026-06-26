//! Tapscript opcodes, serialization, and the poison gate.
//!
//! The opcode set here is exactly the Seal-usable set: nothing else is
//! representable, so the type system makes most poison emission impossible.
//! The serializer enforces minimal pushes; [`verify_script`] re-decodes the
//! final bytes and checks every opcode position against the poison list,
//! structurally, since poison byte values legitimately occur inside push
//! data (a key may contain `0x7e`).
//!
//! Number encoding is CScriptNum: little-endian sign-magnitude, minimal
//! (no trailing zero bytes except to carry the sign bit); `0` is the empty
//! vector.

/// One tapscript operation. `Push` carries raw data; `PushNum` is lowered to
/// the minimal numeric push form at serialization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    Push(Vec<u8>),
    PushNum(i64),
    If,
    NotIf,
    Else,
    EndIf,
    Verify,
    Drop,
    Drop2,
    Dup,
    Nip,
    Over,
    Pick,
    Roll,
    Swap,
    Tuck,
    Size,
    Equal,
    EqualVerify,
    Add1,
    Sub1,
    Negate,
    Abs,
    Not,
    ZeroNotEqual,
    Add,
    Sub,
    BoolAnd,
    BoolOr,
    NumEqual,
    NumEqualVerify,
    NumNotEqual,
    LessThan,
    GreaterThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
    Min,
    Max,
    Within,
    Ripemd160,
    Sha1,
    Sha256,
    Hash160,
    Hash256,
    CheckSig,
    CheckSigVerify,
    CheckSigAdd,
    Cltv,
    Csv,
}

impl Op {
    fn byte(&self) -> u8 {
        match self {
            Op::Push(_) | Op::PushNum(_) => unreachable!("pushes serialize specially"),
            Op::If => 0x63,
            Op::NotIf => 0x64,
            Op::Else => 0x67,
            Op::EndIf => 0x68,
            Op::Verify => 0x69,
            Op::Drop => 0x75,
            Op::Drop2 => 0x6d,
            Op::Dup => 0x76,
            Op::Nip => 0x77,
            Op::Over => 0x78,
            Op::Pick => 0x79,
            Op::Roll => 0x7a,
            Op::Swap => 0x7c,
            Op::Tuck => 0x7d,
            Op::Size => 0x82,
            Op::Equal => 0x87,
            Op::EqualVerify => 0x88,
            Op::Add1 => 0x8b,
            Op::Sub1 => 0x8c,
            Op::Negate => 0x8f,
            Op::Abs => 0x90,
            Op::Not => 0x91,
            Op::ZeroNotEqual => 0x92,
            Op::Add => 0x93,
            Op::Sub => 0x94,
            Op::BoolAnd => 0x9a,
            Op::BoolOr => 0x9b,
            Op::NumEqual => 0x9c,
            Op::NumEqualVerify => 0x9d,
            Op::NumNotEqual => 0x9e,
            Op::LessThan => 0x9f,
            Op::GreaterThan => 0xa0,
            Op::LessThanOrEqual => 0xa1,
            Op::GreaterThanOrEqual => 0xa2,
            Op::Min => 0xa3,
            Op::Max => 0xa4,
            Op::Within => 0xa5,
            Op::Ripemd160 => 0xa6,
            Op::Sha1 => 0xa7,
            Op::Sha256 => 0xa8,
            Op::Hash160 => 0xa9,
            Op::Hash256 => 0xaa,
            Op::CheckSig => 0xac,
            Op::CheckSigVerify => 0xad,
            Op::CheckSigAdd => 0xba,
            Op::Cltv => 0xb1,
            Op::Csv => 0xb2,
        }
    }

    fn name(&self) -> String {
        match self {
            Op::Push(data) => format!("<{}>", hex(data)),
            Op::PushNum(n) => n.to_string(),
            other => format!("{other:?}").to_uppercase(),
        }
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// CScriptNum encoding: LE sign-magnitude, minimal. Handles the full 5-byte
/// timelock domain (values up to 2^32-1 need 5 bytes when the high bit sets).
pub fn encode_num(v: i64) -> Vec<u8> {
    if v == 0 {
        return Vec::new();
    }
    let neg = v < 0;
    let mut abs = v.unsigned_abs();
    let mut out = Vec::new();
    while abs > 0 {
        out.push((abs & 0xff) as u8);
        abs >>= 8;
    }
    // If the top bit of the last byte is set, it would read as a sign bit:
    // carry the sign in an extra byte.
    if out.last().expect("nonzero") & 0x80 != 0 {
        out.push(if neg { 0x80 } else { 0x00 });
    } else if neg {
        *out.last_mut().expect("nonzero") |= 0x80;
    }
    out
}

/// Serialize ops to script bytes, enforcing minimal pushes.
pub fn serialize(ops: &[Op]) -> Vec<u8> {
    let mut out = Vec::new();
    for op in ops {
        match op {
            Op::PushNum(n) => match n {
                0 => out.push(0x00),                 // OP_0
                -1 => out.push(0x4f),                // OP_1NEGATE
                1..=16 => out.push(0x50 + *n as u8), // OP_1..OP_16
                _ => push_data(&mut out, &encode_num(*n)),
            },
            Op::Push(data) => {
                debug_assert!(data.len() <= 520, "stack element cap (consensus)");
                // Minimal-form rule: data representable as a small-int op
                // must use it. The lowerer routes numbers through PushNum,
                // so raw Push data here is keys/hashes (never 0/1-byte
                // small ints by construction; debug-checked).
                debug_assert!(
                    !(data.len() == 1 && (data[0] <= 16 || data[0] == 0x81)),
                    "small ints must use PushNum"
                );
                push_data(&mut out, data);
            }
            other => out.push(other.byte()),
        }
    }
    out
}

fn push_data(out: &mut Vec<u8>, data: &[u8]) {
    match data.len() {
        0 => out.push(0x00), // OP_0: empty vector
        1..=75 => {
            out.push(data.len() as u8);
            out.extend_from_slice(data);
        }
        76..=255 => {
            out.push(0x4c); // OP_PUSHDATA1
            out.push(data.len() as u8);
            out.extend_from_slice(data);
        }
        _ => {
            out.push(0x4d); // OP_PUSHDATA2
            out.extend_from_slice(&(data.len() as u16).to_le_bytes());
            out.extend_from_slice(data);
        }
    }
}

/// Human-readable assembly.
pub fn asm(ops: &[Op]) -> String {
    ops.iter().map(Op::name).collect::<Vec<_>>().join(" ")
}

/// The poison gate (opcode safety): re-decode the serialized script and
/// check every OPCODE position. Returns Err on poison, truncated pushes, or
/// oversized elements. This is the last line of defense: the `Op` type
/// already cannot express poison.
pub fn verify_script(bytes: &[u8]) -> Result<(), String> {
    const POISON: &[u8] = &[
        0x50, 0x62, 0x65, 0x66, // RESERVED, VER, VERIF, VERNOTIF
        0x7e, 0x7f, 0x80, 0x81, // CAT, SUBSTR, LEFT, RIGHT
        0x83, 0x84, 0x85, 0x86, // INVERT, AND, OR, XOR
        0x89, 0x8a, // RESERVED1, RESERVED2
        0x8d, 0x8e, // 2MUL, 2DIV
        0x95, 0x96, 0x97, 0x98, 0x99, // MUL, DIV, MOD, LSHIFT, RSHIFT
        0xae, 0xaf, // CHECKMULTISIG(VERIFY)
        0xff, // INVALIDOPCODE
    ];
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        i += 1;
        let data_len = match b {
            0x01..=0x4b => b as usize,
            0x4c => {
                let n = *bytes.get(i).ok_or("truncated PUSHDATA1")? as usize;
                i += 1;
                n
            }
            0x4d => {
                let lo = *bytes.get(i).ok_or("truncated PUSHDATA2")? as usize;
                let hi = *bytes.get(i + 1).ok_or("truncated PUSHDATA2")? as usize;
                i += 2;
                lo | (hi << 8)
            }
            0x4e => return Err("PUSHDATA4 is never minimal for <=520-byte elements".into()),
            _ => {
                if POISON.contains(&b) || (0xbb..=0xfe).contains(&b) {
                    return Err(format!("poison opcode 0x{b:02x} at offset {}", i - 1));
                }
                continue;
            }
        };
        if data_len > 520 {
            return Err(format!(
                "push of {data_len} bytes exceeds the 520-byte element cap"
            ));
        }
        if i + data_len > bytes.len() {
            return Err("truncated push data".into());
        }
        i += data_len;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cscriptnum_golden_encodings() {
        // Verified against Bitcoin Core's CScriptNum semantics.
        assert_eq!(encode_num(0), Vec::<u8>::new());
        assert_eq!(encode_num(1), vec![0x01]);
        assert_eq!(encode_num(-1), vec![0x81]);
        assert_eq!(encode_num(127), vec![0x7f]);
        assert_eq!(encode_num(128), vec![0x80, 0x00]); // sign-bit carry
        assert_eq!(encode_num(-128), vec![0x80, 0x80]);
        assert_eq!(encode_num(255), vec![0xff, 0x00]);
        assert_eq!(encode_num(256), vec![0x00, 0x01]);
        assert_eq!(encode_num(-255), vec![0xff, 0x80]);
        assert_eq!(encode_num(4320), vec![0xe0, 0x10]);
        assert_eq!(encode_num(900_000), vec![0xa0, 0xbb, 0x0d]);
        assert_eq!(encode_num(2_147_483_647), vec![0xff, 0xff, 0xff, 0x7f]);
        // The 5-byte timelock domain.
        assert_eq!(
            encode_num(2_147_483_648),
            vec![0x00, 0x00, 0x00, 0x80, 0x00]
        );
        assert_eq!(
            encode_num(4_294_967_295),
            vec![0xff, 0xff, 0xff, 0xff, 0x00]
        );
    }

    #[test]
    fn minimal_push_forms() {
        assert_eq!(serialize(&[Op::PushNum(0)]), vec![0x00]);
        assert_eq!(serialize(&[Op::PushNum(1)]), vec![0x51]);
        assert_eq!(serialize(&[Op::PushNum(16)]), vec![0x60]);
        assert_eq!(serialize(&[Op::PushNum(-1)]), vec![0x4f]);
        assert_eq!(serialize(&[Op::PushNum(17)]), vec![0x01, 0x11]);
        let key = vec![0xab; 32];
        let s = serialize(&[Op::Push(key.clone())]);
        assert_eq!(s[0], 32);
        assert_eq!(&s[1..], &key[..]);
        let big = vec![0x01; 80];
        let s = serialize(&[Op::Push(big)]);
        assert_eq!(s[0], 0x4c); // PUSHDATA1 above 75
        assert_eq!(s[1], 80);
    }

    #[test]
    fn poison_gate_is_structural() {
        // A key containing the OP_CAT byte (0x7e) inside push DATA is fine,
        let mut key = vec![0x7e; 32];
        key[0] = 0x00;
        let ok = serialize(&[Op::Push(key), Op::CheckSig]);
        assert!(verify_script(&ok).is_ok());
        // but 0x7e in OPCODE position is poison.
        assert!(verify_script(&[0x7e]).is_err());
        assert!(verify_script(&[0xae]).is_err()); // CHECKMULTISIG
        assert!(verify_script(&[0xbb]).is_err()); // OP_SUCCESS block
        // Truncated push data is caught.
        assert!(verify_script(&[0x05, 0x01, 0x02]).is_err());
        // The emitted set itself is clean.
        let all = serialize(&[
            Op::If,
            Op::PushNum(5),
            Op::Add,
            Op::EndIf,
            Op::Sha256,
            Op::CheckSigAdd,
            Op::Csv,
            Op::Drop,
        ]);
        assert!(verify_script(&all).is_ok());
    }

    #[test]
    fn asm_reads() {
        let ops = [
            Op::PushNum(2),
            Op::Pick,
            Op::Sha256,
            Op::Push(vec![0xab, 0xcd]),
            Op::EqualVerify,
        ];
        assert_eq!(asm(&ops), "2 PICK SHA256 <abcd> EQUALVERIFY");
    }
}
