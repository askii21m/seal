//! Worst-case satisfaction cost: the LARGEST valid witness a script-path spend
//! can require, plus the leaf script and control block, as weight units and
//! virtual bytes. This is the fee/vsize bound a wallet reserves against (the
//! analog of Miniscript's `max_satisfaction_size`).
//!
//! "Worst case" = every signature slot is a present 65-byte BIP340 signature
//! (64 sig bytes + a sighash-type byte: SIGHASH_DEFAULT omits the byte for a
//! 64-byte sig, but a bare `<pubkey> CHECKSIG` cannot force SIGHASH_DEFAULT, so
//! 65 is the largest *valid* element), every `Int` its 5-byte CScriptNum
//! maximum, every `Bool` one byte, every `Bytes<N>`/`Hash` its full length. A
//! threshold path's cheapest satisfaction is smaller, but the bound a fee must
//! cover is the largest a *valid* witness can be -- so the per-element maximum
//! is exactly the right figure, and it is exact (no satisfaction search needed).
//!
//! Two figures come out of this:
//!
//! * `max_witness_weight` -- the serialized witness STACK at 1 WU/byte (BIP141):
//!   the per-input item-count plus, for each stack item (the witness elements,
//!   the revealed leaf script, and the control block), its compact-size length
//!   prefix plus its bytes. This is `max_satisfaction_size`: the part that
//!   varies between leaves, so it is the right figure to compare paths by.
//!
//! * `max_input_weight` -- the full per-INPUT weight (Bitcoin Core's
//!   `GetTransactionInputWeight`): the witness above PLUS the input's
//!   non-witness base counted at 4 WU/byte -- prevout (32 txid + 4 vout = 36) +
//!   empty scriptSig length (1) + nSequence (4) = 41 bytes => 164 WU. This is
//!   the honest marginal cost of spending the input in *any* transaction; it is
//!   what "cost to spend this path" means. It excludes transaction-level
//!   overhead (version, marker/flag, in/out counts, nLockTime, the outputs),
//!   which is shared across all inputs and not attributable to one path.
//!
//! vbytes = weight / 4.

/// Per-input non-witness base, in weight units: prevout (36) + empty scriptSig
/// compact-size length (1) + nSequence (4) = 41 bytes, each at 4 WU/byte.
const INPUT_BASE_WEIGHT: u64 = 4 * (36 + 1 + 4);

use crate::analysis::consteval::{ConstValue, Env};
use crate::analysis::sema::{ContractInfo, HashAlg, Len, Ty};
use crate::codegen::lower::LoweredLeaf;
use crate::output::taproot::Assembled;

#[derive(Debug, Clone)]
pub struct SpendCost {
    pub name: String,
    /// The revealed leaf script, in bytes.
    pub script_bytes: usize,
    /// The control block (`0xc0|parity ‖ internal_key ‖ merkle_path`), in bytes.
    pub control_bytes: usize,
    /// The worst-case witness STACK elements (the satisfaction), in bytes
    /// (excludes script + control, which are separate stack items).
    pub witness_elem_bytes: usize,
    /// The whole input witness serialized (item count + every item's
    /// compact-size prefix + bytes), i.e. the spend's added weight in WU.
    pub max_witness_weight: u64,
    /// `max_witness_weight / 4`.
    pub max_vbytes: f64,
    /// Full per-input weight: `max_witness_weight + INPUT_BASE_WEIGHT` (the
    /// input's prevout + empty scriptSig + nSequence at 4 WU/byte). The honest
    /// "cost to spend this path"; excludes shared transaction-level overhead.
    pub max_input_weight: u64,
    /// `max_input_weight / 4`.
    pub max_input_vbytes: f64,
}

/// Per-spend worst-case cost. Leaves and assembled leaves are in the same
/// (declaration / input) order.
pub fn analyze(
    info: &ContractInfo,
    env: &Env,
    leaves: &[LoweredLeaf],
    asm: &Assembled,
) -> Vec<SpendCost> {
    let mut out = Vec::new();
    for (leaf, al) in leaves.iter().zip(&asm.leaves) {
        let Some(sig) = info.spends.iter().find(|s| s.name == leaf.name) else {
            continue;
        };

        // Witness stack item byte-lengths, in spend order: the satisfaction
        // elements (only the slots actually in this leaf's witness -- dead
        // elements eliminated by the optimizer are absent), then the script,
        // then the control block.
        let mut sizes: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
        for p in &sig.params {
            slot_sizes(&p.name, &p.ty, env, &mut sizes);
        }
        let mut items: Vec<usize> = leaf
            .witness_order
            .iter()
            .filter_map(|s| sizes.get(s).copied())
            .collect();
        let witness_elem_bytes: usize = items.iter().sum();
        items.push(leaf.script.len());
        items.push(al.control_block.len());

        // Serialized witness: item count + each item's (compactsize + bytes).
        let serialized: usize =
            compact_size(items.len()) + items.iter().map(|&l| compact_size(l) + l).sum::<usize>();

        let max_witness_weight = serialized as u64;
        let max_input_weight = max_witness_weight + INPUT_BASE_WEIGHT;
        out.push(SpendCost {
            name: leaf.name.clone(),
            script_bytes: leaf.script.len(),
            control_bytes: al.control_block.len(),
            witness_elem_bytes,
            max_witness_weight,
            max_vbytes: max_witness_weight as f64 / 4.0,
            max_input_weight,
            max_input_vbytes: max_input_weight as f64 / 4.0,
        });
    }
    out
}

/// Map each witness slot a value of `ty` contributes to its worst-case byte
/// length, keyed by slot name (`name`, or `name[i]` per array element), so the
/// caller can keep only the slots actually present in a leaf's `witness_order`.
fn slot_sizes(name: &str, ty: &Ty, env: &Env, out: &mut std::collections::HashMap<String, usize>) {
    let scalar = match ty {
        Ty::Array(elem, len) => {
            let n = resolve_len(len, env).unwrap_or(0);
            for i in 0..n {
                slot_sizes(&format!("{name}[{i}]"), elem, env, out);
            }
            return;
        }
        Ty::Bool => 1,
        Ty::Int => 5,        // CScriptNum, worst-case
        Ty::Signature => 65, // BIP340 sig (64) + sighash-type byte; largest valid (matches limits.rs)
        Ty::PublicKey => 32,
        Ty::Bytes(len) => resolve_len(len, env).unwrap_or(0),
        Ty::Hash(alg) => hash_len(*alg),
        Ty::LockTimeAbs | Ty::LockTimeRel => return, // not witness data
    };
    out.insert(name.to_string(), scalar);
}

fn hash_len(alg: HashAlg) -> usize {
    match alg {
        HashAlg::Sha256 | HashAlg::Hash256 => 32,
        HashAlg::Hash160 | HashAlg::Ripemd160 | HashAlg::Sha1 => 20,
    }
}

fn resolve_len(len: &Len, env: &Env) -> Option<usize> {
    match len {
        Len::Lit(n) => Some(*n as usize),
        Len::Named(name) => match env.get(name) {
            Some(ConstValue::Int(v)) if *v >= 0 => Some(*v as usize),
            _ => None,
        },
    }
}

/// Bitcoin compact-size encoding length for a count/length `n`.
fn compact_size(n: usize) -> usize {
    if n < 0xfd {
        1
    } else if n <= 0xffff {
        3
    } else if n <= 0xffff_ffff {
        5
    } else {
        9
    }
}
