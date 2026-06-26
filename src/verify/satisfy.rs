//! The satisfier: build a witness stack from a high-level spend plan.
//!
//! "Compiles implies spendable" is the money-safety property: every path a
//! contract declares must have a witness the script accepts. The satisfier
//! turns a per-spend assignment of parameter values into the concrete
//! witness stack (in the leaf's compiler-owned witness order), so the
//! differential against the interpreter (and `seal test` on regtest) is
//! automatic and fuzzable, not hand-built.
//!
//! Encoding mirrors lowering: `Int` to minimal CScriptNum, `Bool` to `{}` or
//! `{0x01}`, `Bytes`/`Hash`/`PublicKey` to raw, a `Signature` slot to either
//! a caller-supplied signature marker (the real thing comes from a wallet
//! or test key, never the compiler) or the canonical empty decline.

use crate::analysis::consteval::{ConstValue, Env};
use crate::analysis::sema::{HashAlg, Len, SpendSig, Ty};
use crate::codegen::lower::LoweredLeaf;
use crate::codegen::script::encode_num;

/// A high-level value for one spend parameter.
#[derive(Debug, Clone)]
pub enum SatValue {
    Int(i64),
    Bool(bool),
    Bytes(Vec<u8>),
    /// A signature slot: `true` supplies a valid signature (the marker),
    /// `false` declines with the canonical empty vector.
    Sig(bool),
    /// Per-element values for an array parameter.
    Array(Vec<SatValue>),
}

/// Build the witness stack for a lowered leaf from `params` (by parameter
/// name) and the spend signature (for types and array lengths).
/// `sig_marker` is the bytes used for a present signature: a real
/// signature in `seal test`, a sentinel for the mock-oracle differential.
///
/// Errors when a slot can't be filled (missing param, type/shape mismatch),
/// so a bad plan fails loudly.
pub fn build_witness(
    leaf: &LoweredLeaf,
    sig: &SpendSig,
    env: &Env,
    params: &[(String, SatValue)],
    sig_marker: &[u8],
) -> Result<Vec<Vec<u8>>, String> {
    // Expand every parameter into its slot-to-bytes entries.
    let mut slots: Vec<(String, Vec<u8>)> = Vec::new();
    for p in &sig.params {
        let value = params
            .iter()
            .find(|(n, _)| *n == p.name)
            .map(|(_, v)| v)
            .ok_or_else(|| format!("no spend value for parameter `{}`", p.name))?;
        expand(&p.name, &p.ty, value, env, sig_marker, &mut slots)?;
    }

    // Assemble in the leaf's witness order: every slot is a declared param.
    let mut stack = Vec::with_capacity(leaf.witness_order.len());
    for name in &leaf.witness_order {
        let bytes = slots
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, b)| b.clone())
            .ok_or_else(|| format!("witness slot `{name}` has no value"))?;
        stack.push(bytes);
    }
    Ok(stack)
}

/// Expand one (possibly array) parameter into its leaf slots.
fn expand(
    name: &str,
    ty: &Ty,
    value: &SatValue,
    env: &Env,
    sig_marker: &[u8],
    out: &mut Vec<(String, Vec<u8>)>,
) -> Result<(), String> {
    match ty {
        Ty::Array(elem, len) => {
            let n = array_len(len, env)?;
            let SatValue::Array(items) = value else {
                return Err(format!(
                    "`{name}` is an array of {n}, but the plan is not an array"
                ));
            };
            if items.len() != n {
                return Err(format!(
                    "`{name}` expects {n} elements, plan has {}",
                    items.len()
                ));
            }
            for (i, item) in items.iter().enumerate() {
                expand(&format!("{name}[{i}]"), elem, item, env, sig_marker, out)?;
            }
            Ok(())
        }
        _ => {
            out.push((
                name.to_string(),
                encode_scalar(name, ty, value, sig_marker)?,
            ));
            Ok(())
        }
    }
}

/// Encode one scalar parameter value as its witness bytes.
fn encode_scalar(
    name: &str,
    ty: &Ty,
    value: &SatValue,
    sig_marker: &[u8],
) -> Result<Vec<u8>, String> {
    match (ty, value) {
        (Ty::Int, SatValue::Int(n)) => Ok(encode_num(*n)),
        (Ty::Bool, SatValue::Bool(b)) => Ok(if *b { vec![0x01] } else { Vec::new() }),
        (Ty::Signature, SatValue::Sig(present)) => Ok(if *present {
            sig_marker.to_vec()
        } else {
            Vec::new()
        }),
        (Ty::PublicKey, SatValue::Bytes(b)) if b.len() == 32 => Ok(b.clone()),
        (Ty::Bytes(len), SatValue::Bytes(b)) => match len {
            Len::Lit(n) if b.len() == *n as usize => Ok(b.clone()),
            Len::Named(_) => Ok(b.clone()), // length resolved at runtime
            _ => Err(format!(
                "`{name}`: byte length mismatch ({} bytes)",
                b.len()
            )),
        },
        (Ty::Hash(alg), SatValue::Bytes(b)) if b.len() == hash_len(*alg) => Ok(b.clone()),
        _ => Err(format!("`{name}`: value does not match its type")),
    }
}

fn array_len(len: &Len, env: &Env) -> Result<usize, String> {
    match len {
        Len::Lit(n) => Ok(*n as usize),
        Len::Named(name) => match env.get(name) {
            Some(ConstValue::Int(v)) if *v >= 0 => Ok(*v as usize),
            _ => Err(format!("array length `{name}` did not instantiate")),
        },
    }
}

fn hash_len(alg: HashAlg) -> usize {
    match alg {
        HashAlg::Sha256 | HashAlg::Hash256 => 32,
        HashAlg::Hash160 | HashAlg::Ripemd160 | HashAlg::Sha1 => 20,
    }
}
