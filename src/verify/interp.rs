//! A reference tapscript interpreter: the lowering's differential oracle. It
//! re-decodes the SERIALIZED script bytes (independent of the `Op`
//! representation) and executes them under BIP342 consensus semantics, so a
//! compiled script is run, not merely read.
//!
//! # Why this exists (the money-safety argument)
//!
//! Crypto and taproot assembly are checked against official BIP vectors:
//! independent ground truth. The LOWERING was not: until this interpreter,
//! no compiled script had ever executed. A reference interpreter lets every
//! path be exercised: the satisfier builds an honest witness, the
//! interpreter runs `script(witness)` and MUST succeed; an adversarial
//! witness MUST fail. Bitcoin Core on regtest is the final, fully
//! independent oracle; this is the fast in-process one that also runs in
//! every `cargo test`.
//!
//! # Faithfulness
//!
//! Mirrors Core's `EvalScript` for the curated opcode set: CScriptNum
//! (<= 4-byte operands, minimal encoding required), `CastToBool` (negative
//! zero is false), MINIMALIF (the `OP_IF` argument is exactly `{}` or
//! `{0x01}` in tapscript), the CHECKSIG trichotomy (empty is false,
//! non-empty-valid is true, non-empty-invalid is ABORT), the 1000-element
//! stack limit, the 520-byte element limit, and tail CLEANSTACK (exactly
//! one truthy element).
//!
//! Signature verification and CLTV/CSV are supplied by a [`Context`]: the
//! in-process tests use an oracle so they need no transaction; the regtest
//! path defers the whole check to Core. NOT a consensus implementation: it
//! validates OUR scripts, it is not a node.

use crate::crypto::ripemd160::ripemd160;
use crate::crypto::sha1::sha1;
use crate::crypto::sha256::sha256;

/// Execution context: the transaction fields CLTV/CSV read, plus the
/// signature-validity oracle CHECKSIG consults.
pub struct Context<'a> {
    /// The spending tx's `nLockTime` (BIP65 / CLTV).
    pub locktime: u32,
    /// The spending input's `nSequence` (BIP112 / CSV).
    pub sequence: u32,
    /// The spending tx's version (CSV requires >= 2).
    pub tx_version: u32,
    /// `(x-only pubkey, signature)` to "is this a valid signature?". The
    /// interpreter handles the empty-signature (decline) case itself and
    /// only calls this for NON-empty signatures.
    pub verify_sig: &'a dyn Fn(&[u8], &[u8]) -> bool,
}

/// BIP341/342 limits.
const MAX_STACK: usize = 1000;
const MAX_ELEMENT: usize = 520;
/// `nSequence` bits (BIP68): the disable flag and the type flag.
const SEQUENCE_LOCKTIME_DISABLE_FLAG: u32 = 1 << 31;
const SEQUENCE_LOCKTIME_TYPE_FLAG: u32 = 1 << 22;
const SEQUENCE_LOCKTIME_MASK: u32 = 0x0000_ffff | SEQUENCE_LOCKTIME_TYPE_FLAG;
/// CLTV threshold: below this an operand is a height, at/above a unix time.
const LOCKTIME_THRESHOLD: i64 = 500_000_000;

/// Run a serialized tapscript leaf against an initial witness stack.
/// `Ok(())` means the script SUCCEEDED (exactly one truthy element left);
/// `Err` carries the consensus reason it failed.
pub fn execute(script: &[u8], witness: &[Vec<u8>], ctx: &Context) -> Result<(), String> {
    let mut stack: Vec<Vec<u8>> = witness.to_vec();
    if stack.len() > MAX_STACK {
        return Err("initial witness exceeds the 1000-element stack limit".into());
    }
    for e in &stack {
        if e.len() > MAX_ELEMENT {
            return Err("witness element exceeds the 520-byte limit".into());
        }
    }

    // Conditional-execution stack (IF/ELSE/ENDIF). An op runs only when
    // every entry is true.
    let mut cond: Vec<bool> = Vec::new();
    let executing = |cond: &[bool]| cond.iter().all(|&b| b);

    let mut i = 0usize;
    while i < script.len() {
        let op = script[i];
        i += 1;
        let exec = executing(&cond);

        // Push opcodes.
        if op == 0x4e {
            return Err("OP_PUSHDATA4 is invalid (never minimal)".into());
        }
        if let Some(len) = push_len(op, script, &mut i)? {
            if exec {
                let start = i;
                let end = start
                    .checked_add(len)
                    .filter(|e| *e <= script.len())
                    .ok_or("truncated push data")?;
                let data = script[start..end].to_vec();
                if data.len() > MAX_ELEMENT {
                    return Err("push exceeds the 520-byte element limit".into());
                }
                push(&mut stack, data)?;
            }
            i += len;
            continue;
        }
        // Small-integer / OP_0 / OP_1NEGATE pushes.
        if let Some(v) = small_push(op) {
            if exec {
                push(&mut stack, v)?;
            }
            continue;
        }

        // Conditionals are evaluated even inside a skipped branch (to track
        // nesting), but only POP the stack when executing.
        match op {
            0x63 | 0x64 => {
                // OP_IF / OP_NOTIF
                let mut value = false;
                if exec {
                    let top = pop(&mut stack)?;
                    // MINIMALIF (tapscript consensus): {} or {0x01} only.
                    if !(top.is_empty() || top == [0x01]) {
                        return Err("OP_IF argument is not minimal ({} or 0x01)".into());
                    }
                    value = cast_to_bool(&top);
                    if op == 0x64 {
                        value = !value;
                    }
                }
                cond.push(value);
                continue;
            }
            0x67 => {
                // OP_ELSE
                let last = cond.last_mut().ok_or("OP_ELSE with no OP_IF")?;
                *last = !*last;
                continue;
            }
            0x68 => {
                // OP_ENDIF
                cond.pop().ok_or("OP_ENDIF with no OP_IF")?;
                continue;
            }
            _ => {}
        }

        if !exec {
            continue; // inside a not-taken branch: skip non-conditionals
        }

        // Executed opcodes.
        dispatch(op, &mut stack, ctx)?;
        if stack.len() > MAX_STACK {
            return Err("stack exceeds the 1000-element limit".into());
        }
    }

    if !cond.is_empty() {
        return Err("unbalanced OP_IF/OP_ENDIF".into());
    }
    // Tail CLEANSTACK: exactly one element, and it must be truthy.
    match stack.as_slice() {
        [only] if cast_to_bool(only) => Ok(()),
        [_] => Err("script left a false value on the stack".into()),
        _ => Err(format!(
            "CLEANSTACK: script left {} elements, not 1",
            stack.len()
        )),
    }
}

/// Dispatch a non-push, non-conditional opcode.
fn dispatch(op: u8, stack: &mut Vec<Vec<u8>>, ctx: &Context) -> Result<(), String> {
    match op {
        0x69 => {
            // OP_VERIFY
            let v = pop(stack)?;
            if !cast_to_bool(&v) {
                return Err("OP_VERIFY failed".into());
            }
        }
        0x75 => {
            pop(stack)?; // OP_DROP
        }
        0x6d => {
            // OP_2DROP
            pop(stack)?;
            pop(stack)?;
        }
        0x76 => {
            // OP_DUP
            let top = top(stack, 0)?.clone();
            push(stack, top)?;
        }
        0x77 => {
            // OP_NIP: remove second-from-top
            let n = stack.len();
            if n < 2 {
                return Err("OP_NIP needs 2 elements".into());
            }
            stack.remove(n - 2);
        }
        0x78 => {
            // OP_OVER: copy second-from-top
            let v = top(stack, 1)?.clone();
            push(stack, v)?;
        }
        0x79 => {
            // OP_PICK: copy the nth-from-top
            let n = num(&pop(stack)?, 4)?;
            let v = pick(stack, n)?;
            push(stack, v)?;
        }
        0x7a => {
            // OP_ROLL: move the nth-from-top
            let n = num(&pop(stack)?, 4)?;
            if n < 0 || n as usize >= stack.len() {
                return Err("OP_ROLL index out of range".into());
            }
            let idx = stack.len() - 1 - n as usize;
            let v = stack.remove(idx);
            push(stack, v)?;
        }
        0x7c => {
            // OP_SWAP
            let n = stack.len();
            if n < 2 {
                return Err("OP_SWAP needs 2 elements".into());
            }
            stack.swap(n - 1, n - 2);
        }
        0x7d => {
            // OP_TUCK: copy top below the second element
            let n = stack.len();
            if n < 2 {
                return Err("OP_TUCK needs 2 elements".into());
            }
            let topv = stack[n - 1].clone();
            stack.insert(n - 2, topv);
        }
        0x82 => {
            // OP_SIZE: push the length of the top (without popping)
            let len = top(stack, 0)?.len() as i64;
            push(stack, encode_num(len))?;
        }
        0x87 | 0x88 => {
            // OP_EQUAL / OP_EQUALVERIFY: bytewise
            let b = pop(stack)?;
            let a = pop(stack)?;
            let eq = a == b;
            if op == 0x88 {
                if !eq {
                    return Err("OP_EQUALVERIFY failed".into());
                }
            } else {
                push(stack, bool_vec(eq))?;
            }
        }
        0x8b | 0x8c | 0x8f | 0x90 | 0x91 | 0x92 => {
            // Unary numeric: 1ADD, 1SUB, NEGATE, ABS, NOT, 0NOTEQUAL
            let x = num(&pop(stack)?, 4)?;
            let r = match op {
                0x8b => x + 1,
                0x8c => x - 1,
                0x8f => -x,
                0x90 => x.abs(),
                0x91 => i64::from(x == 0),
                _ => i64::from(x != 0), // 0x92
            };
            push(stack, encode_num(r))?;
        }
        0x93 | 0x94 | 0x9a | 0x9b | 0x9c | 0x9d | 0x9e | 0x9f | 0xa0 | 0xa1 | 0xa2 | 0xa3
        | 0xa4 => {
            // Binary numeric.
            let b = num(&pop(stack)?, 4)?;
            let a = num(&pop(stack)?, 4)?;
            let r = match op {
                0x93 => a + b,                       // ADD
                0x94 => a - b,                       // SUB
                0x9a => i64::from(a != 0 && b != 0), // BOOLAND
                0x9b => i64::from(a != 0 || b != 0), // BOOLOR
                0x9c | 0x9d => i64::from(a == b),    // NUMEQUAL / VERIFY
                0x9e => i64::from(a != b),           // NUMNOTEQUAL
                0x9f => i64::from(a < b),            // LESSTHAN
                0xa0 => i64::from(a > b),            // GREATERTHAN
                0xa1 => i64::from(a <= b),           // LESSTHANOREQUAL
                0xa2 => i64::from(a >= b),           // GREATERTHANOREQUAL
                0xa3 => a.min(b),                    // MIN
                _ => a.max(b),                       // MAX (0xa4)
            };
            if op == 0x9d {
                if r == 0 {
                    return Err("OP_NUMEQUALVERIFY failed".into());
                }
            } else {
                push(stack, encode_num(r))?;
            }
        }
        0xa5 => {
            // OP_WITHIN: x in [lo, hi)
            let hi = num(&pop(stack)?, 4)?;
            let lo = num(&pop(stack)?, 4)?;
            let x = num(&pop(stack)?, 4)?;
            push(stack, bool_vec(lo <= x && x < hi))?;
        }
        0xa6 => {
            let v = pop(stack)?; // RIPEMD160
            push(stack, ripemd160(&v).to_vec())?;
        }
        0xa7 => {
            let v = pop(stack)?; // SHA1 (valid in tapscript; Core executes it)
            push(stack, sha1(&v).to_vec())?;
        }
        0xa8 => {
            let v = pop(stack)?; // SHA256
            push(stack, sha256(&v).to_vec())?;
        }
        0xa9 => {
            let v = pop(stack)?; // HASH160 = RIPEMD160(SHA256)
            push(stack, ripemd160(&sha256(&v)).to_vec())?;
        }
        0xaa => {
            let v = pop(stack)?; // HASH256 = SHA256(SHA256)
            push(stack, sha256(&sha256(&v)).to_vec())?;
        }
        0xac | 0xad => {
            // OP_CHECKSIG / OP_CHECKSIGVERIFY
            let pubkey = pop(stack)?;
            let sig = pop(stack)?;
            let ok = check_sig(&sig, &pubkey, ctx)?;
            if op == 0xad {
                if !ok {
                    return Err("OP_CHECKSIGVERIFY failed".into());
                }
            } else {
                push(stack, bool_vec(ok))?;
            }
        }
        0xba => {
            // OP_CHECKSIGADD: pops (sig, n, pubkey); pushes n + (1|0)
            let pubkey = pop(stack)?;
            let n = num(&pop(stack)?, 4)?;
            let sig = pop(stack)?;
            let ok = check_sig(&sig, &pubkey, ctx)?;
            push(stack, encode_num(n + i64::from(ok)))?;
        }
        0xb1 => {
            // OP_CHECKLOCKTIMEVERIFY (CLTV): leaves the operand
            let operand = num_5(top(stack, 0)?)?;
            check_locktime(operand, ctx)?;
        }
        0xb2 => {
            // OP_CHECKSEQUENCEVERIFY (CSV): leaves the operand
            let operand = num_5(top(stack, 0)?)?;
            check_sequence(operand, ctx)?;
        }
        other => return Err(format!("unsupported opcode 0x{other:02x}")),
    }
    Ok(())
}

// --- CHECKSIG / timelocks ---

/// BIP342 `EvalChecksigTapscript`, modeled byte-for-byte (faithful for ANY
/// input, not just compiler-emitted scripts, so the interpreter stands in
/// for Core when fuzzed on arbitrary bytes):
///
/// - **empty public key is ABORT** (`SCRIPT_ERR_PUBKEYTYPE`), regardless of
///   the signature (even an empty one);
/// - **32-byte key**: BIP340 - an empty sig is `false`; a non-empty sig
///   that fails verification ABORTS; a valid one is `true`;
/// - **other key size**: an unknown (upgradeable) type - the signature is
///   NOT verified and the result is `sig.len() > 0` (the forward-compat
///   "treated as valid" hook).
///
/// The result is `success = sig.len() > 0` in the non-abort cases. (The
/// compiler only ever emits 32-byte keys behind a never-elided SIZE
/// airlock, so only the 32-byte branch is reachable in practice; the rest
/// is modeled for faithfulness. The tapscript sigops budget is a
/// tx-validation concern, not script execution, guaranteed statically by
/// the validation-budget check, and is not modeled here.)
fn check_sig(sig: &[u8], pubkey: &[u8], ctx: &Context) -> Result<bool, String> {
    if pubkey.is_empty() {
        return Err("CHECKSIG: empty public key (SCRIPT_ERR_PUBKEYTYPE) aborts".into());
    }
    if pubkey.len() == 32 && !sig.is_empty() && !(ctx.verify_sig)(pubkey, sig) {
        return Err("CHECKSIG: a non-empty signature failed to verify (script aborts)".into());
    }
    // 32-byte + empty sig is false; 32-byte + valid is true; unknown key
    // type means no verify, success iff the sig is non-empty (upgrade hook).
    Ok(!sig.is_empty())
}

/// BIP65 CLTV check (the operand stays on the stack).
fn check_locktime(operand: i64, ctx: &Context) -> Result<(), String> {
    if operand < 0 {
        return Err("CLTV operand is negative".into());
    }
    let tx_lt = i64::from(ctx.locktime);
    // Both must be on the same side of the height/time threshold.
    let same_kind = (operand < LOCKTIME_THRESHOLD) == (tx_lt < LOCKTIME_THRESHOLD);
    if !same_kind {
        return Err("CLTV: operand and nLockTime are different lock types".into());
    }
    if operand > tx_lt {
        return Err("CLTV: nLockTime has not reached the required value".into());
    }
    if ctx.sequence == 0xffff_ffff {
        return Err("CLTV: input nSequence is final, disabling nLockTime".into());
    }
    Ok(())
}

/// BIP112 CSV check (the operand stays on the stack).
fn check_sequence(operand: i64, ctx: &Context) -> Result<(), String> {
    if operand < 0 {
        return Err("CSV operand is negative".into());
    }
    let operand = operand as u32;
    // If the disable bit is set in the operand, CSV is a no-op (BIP112).
    if operand & SEQUENCE_LOCKTIME_DISABLE_FLAG != 0 {
        return Ok(());
    }
    if ctx.tx_version < 2 {
        return Err("CSV: tx version < 2".into());
    }
    if ctx.sequence & SEQUENCE_LOCKTIME_DISABLE_FLAG != 0 {
        return Err("CSV: input nSequence disable bit is set".into());
    }
    let tx_seq = ctx.sequence & SEQUENCE_LOCKTIME_MASK;
    let want = operand & SEQUENCE_LOCKTIME_MASK;
    // Type (block vs time) must match.
    if (tx_seq & SEQUENCE_LOCKTIME_TYPE_FLAG) != (want & SEQUENCE_LOCKTIME_TYPE_FLAG) {
        return Err("CSV: relative-lock types differ (blocks vs time)".into());
    }
    if want > tx_seq {
        return Err("CSV: input nSequence has not reached the required age".into());
    }
    Ok(())
}

/// Whether an `after(operand)` timelock holds against the spend context, by the
/// same BIP65 (CLTV) / BIP112 (CSV) rules the script enforces. `is_rel` picks
/// CSV (relative) over CLTV (absolute). Exposed for the certifier so the
/// predicate evaluates a timelock exactly as the emitted opcode does; the
/// certifier checks the opcode's PRESENCE and operand independently by
/// certifying at both a satisfying and a just-violating context.
pub(crate) fn timelock_ok(operand: i64, is_rel: bool, ctx: &Context) -> bool {
    if is_rel {
        check_sequence(operand, ctx).is_ok()
    } else {
        check_locktime(operand, ctx).is_ok()
    }
}

// --- stack + number helpers ---

fn push(stack: &mut Vec<Vec<u8>>, v: Vec<u8>) -> Result<(), String> {
    if v.len() > MAX_ELEMENT {
        return Err("push exceeds the 520-byte element limit".into());
    }
    stack.push(v);
    if stack.len() > MAX_STACK {
        return Err("stack exceeds the 1000-element limit".into());
    }
    Ok(())
}

fn pop(stack: &mut Vec<Vec<u8>>) -> Result<Vec<u8>, String> {
    stack.pop().ok_or_else(|| "stack underflow".into())
}

/// The element `n` from the top (0 = top).
fn top(stack: &[Vec<u8>], n: usize) -> Result<&Vec<u8>, String> {
    let len = stack.len();
    if n >= len {
        return Err("stack underflow".into());
    }
    Ok(&stack[len - 1 - n])
}

fn pick(stack: &[Vec<u8>], n: i64) -> Result<Vec<u8>, String> {
    if n < 0 || n as usize >= stack.len() {
        return Err("OP_PICK index out of range".into());
    }
    Ok(stack[stack.len() - 1 - n as usize].clone())
}

/// `OP_TRUE`/`OP_FALSE`-style boolean result vector.
fn bool_vec(b: bool) -> Vec<u8> {
    if b { vec![1] } else { Vec::new() }
}

/// Core's `CastToBool`: true unless every byte is zero except possibly a
/// trailing `0x80` (negative zero).
fn cast_to_bool(v: &[u8]) -> bool {
    for (i, &b) in v.iter().enumerate() {
        if b != 0 {
            return !(i == v.len() - 1 && b == 0x80);
        }
    }
    false
}

/// Decode a CScriptNum operand: up to `max_len` bytes, minimal encoding
/// required (as Core does for numeric opcodes).
fn num(v: &[u8], max_len: usize) -> Result<i64, String> {
    if v.len() > max_len {
        return Err(format!(
            "number is {} bytes (operands are <= {max_len})",
            v.len()
        ));
    }
    decode_minimal(v)
}

/// CLTV/CSV read up to 5 bytes (the operand can exceed the 4-byte
/// arithmetic domain: a uint32 plus sign byte).
fn num_5(v: &[u8]) -> Result<i64, String> {
    if v.len() > 5 {
        return Err("locktime operand exceeds 5 bytes".into());
    }
    decode_minimal(v)
}

/// Independent CScriptNum decode (LE sign-magnitude), enforcing minimality.
fn decode_minimal(v: &[u8]) -> Result<i64, String> {
    if v.is_empty() {
        return Ok(0);
    }
    // Minimal-encoding check (Core's fRequireMinimal): a trailing
    // zero-magnitude byte is only allowed to carry the sign bit of the
    // byte below it.
    let last = v[v.len() - 1];
    if last & 0x7f == 0 && (v.len() == 1 || (v[v.len() - 2] & 0x80) == 0) {
        return Err("non-minimal number encoding".into());
    }
    let mut result: i64 = 0;
    for (i, &b) in v.iter().enumerate() {
        result |= (b as i64) << (8 * i);
    }
    if last & 0x80 != 0 {
        // Negative: strip the sign bit from the top byte, negate.
        let sign_bit = 0x80i64 << (8 * (v.len() - 1));
        return Ok(-(result & !sign_bit));
    }
    Ok(result)
}

/// Independent CScriptNum encode (minimal). Cross-checked against
/// `script::encode_num` and round-tripped in tests.
fn encode_num(n: i64) -> Vec<u8> {
    if n == 0 {
        return Vec::new();
    }
    let neg = n < 0;
    let mut mag = n.unsigned_abs();
    let mut out = Vec::new();
    while mag > 0 {
        out.push((mag & 0xff) as u8);
        mag >>= 8;
    }
    // If the high bit of the top byte is set, add a sign byte; else fold
    // the sign into the top byte.
    if out.last().is_some_and(|b| b & 0x80 != 0) {
        out.push(if neg { 0x80 } else { 0x00 });
    } else if neg {
        let last = out.len() - 1;
        out[last] |= 0x80;
    }
    out
}

// --- byte decoding ---

/// If `op` opens a data push, return its payload length and leave `i`
/// positioned at the payload (consuming any length prefix). `None` for
/// non-push opcodes.
fn push_len(op: u8, script: &[u8], i: &mut usize) -> Result<Option<usize>, String> {
    match op {
        0x01..=0x4b => Ok(Some(op as usize)),
        0x4c => {
            let n = *script.get(*i).ok_or("truncated PUSHDATA1")? as usize;
            *i += 1;
            Ok(Some(n))
        }
        0x4d => {
            let lo = *script.get(*i).ok_or("truncated PUSHDATA2")? as usize;
            let hi = *script.get(*i + 1).ok_or("truncated PUSHDATA2")? as usize;
            *i += 2;
            Ok(Some(lo | (hi << 8)))
        }
        _ => Ok(None),
    }
}

/// OP_0 / OP_1NEGATE / OP_1..OP_16 to the pushed value.
fn small_push(op: u8) -> Option<Vec<u8>> {
    match op {
        0x00 => Some(Vec::new()),             // OP_0 / OP_FALSE
        0x4f => Some(vec![0x81]),             // OP_1NEGATE
        0x51..=0x60 => Some(vec![op - 0x50]), // OP_1..OP_16
        _ => None,
    }
}

/// Machine-checked proofs (Kani). Compiled only under `cargo kani` (the
/// `#[cfg(kani)]` gate keeps them out of every normal build, so the compiler
/// stays zero-dependency). They prove, symbolically over the WHOLE input
/// domain (not by enumeration), the consensus-critical number-codec invariants
/// the interpreter rests on.
#[cfg(kani)]
mod kani_proofs {
    use super::{cast_to_bool, decode_minimal};
    use crate::codegen::script::encode_num;

    /// The lowering's CScriptNum encoder and the interpreter's decoder are
    /// EXACT INVERSES over the whole 4-byte operand domain (+/-(2^31-1)). This is
    /// a machine-checked slice of the lowering<->interpreter agreement: for
    /// EVERY representable operand, what the compiler emits is what the
    /// interpreter reads back.
    #[kani::proof]
    #[kani::unwind(6)] // encode/decode loops run at most 5 times (<=5-byte numbers)
    fn encode_then_decode_is_identity() {
        let n: i64 = kani::any();
        let m = i64::from(i32::MAX); // 2^31 - 1, the 4-byte CScriptNum magnitude
        kani::assume(n >= -m && n <= m);
        let enc = encode_num(n);
        assert!(enc.len() <= 4);
        assert_eq!(decode_minimal(&enc), Ok(n));
    }

    // `num` (the operand reader) is `if v.len() > max_len { Err } else
    // decode_minimal(v) }` -- a total length guard over the proven-total
    // `decode_minimal`, so its totality is a corollary of the proof below and
    // needs no separate harness.

    /// `decode_minimal` is total on the full <=5-byte range CLTV/CSV can read:
    /// it never panics (no shift overflow, no out-of-bounds) on any input.
    #[kani::proof]
    #[kani::unwind(7)]
    fn decode_minimal_is_total() {
        let bytes: [u8; 5] = kani::any();
        let len: usize = kani::any();
        kani::assume(len <= 5);
        let _ = decode_minimal(&bytes[..len]);
    }

    /// The MINIMALITY rule, machine-checked: `decode_minimal` accepts an operand
    /// encoding ONLY if it is the canonical (minimal) form -- for any accepted
    /// <=4-byte `v`, re-encoding the value reproduces `v` exactly. Together with
    /// `encode_then_decode_is_identity` this makes encode/decode a BIJECTION
    /// between values and minimal encodings, so no value has an alternate operand
    /// encoding (a number-malleability vector ruled out in the TCB).
    #[kani::proof]
    #[kani::unwind(6)]
    fn decode_accepts_only_minimal() {
        let bytes: [u8; 4] = kani::any();
        let len: usize = kani::any();
        kani::assume(len <= 4);
        let v = &bytes[..len];
        if let Ok(n) = decode_minimal(v) {
            assert_eq!(encode_num(n).as_slice(), v);
        }
    }

    /// The boolean coercion every `OP_VERIFY`/`OP_IF`/CLEANSTACK rests on: an
    /// encoded operand `n` is truthy IFF `n != 0`. Machine-checks that the
    /// interpreter's accept/reject on a numeric stack top matches its value's
    /// sign-nonzeroness over the whole 4-byte domain.
    #[kani::proof]
    #[kani::unwind(6)]
    fn cast_to_bool_of_number_is_nonzero() {
        let n: i64 = kani::any();
        let m = i64::from(i32::MAX);
        kani::assume(n >= -m && n <= m);
        assert_eq!(cast_to_bool(&encode_num(n)), n != 0);
    }
}
