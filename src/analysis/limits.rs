//! Resource limits: reject a contract that could never produce a standard,
//! spendable transaction (and whose compilation would only burn memory). The
//! bounds are consensus/standardness-derived, and the pass runs AFTER
//! instantiation (array lengths concrete) but BEFORE lowering, so an over-limit
//! contract is rejected before any large allocation -- closing the OOM/DoS
//! vector that an unbounded `[T; N]` or comprehension range would otherwise open.
//!
//! Three bounds:
//!   - **witness stack arity <= 1000** (BIP342: the initial witness stack is
//!     part of the 1000-element execution stack limit) -- the primary guard
//!     against a huge witness array `[T; 2_000_000_000]`;
//!   - **each witness element <= 520 bytes** (the consensus element-size limit);
//!   - **comprehension unroll <= 400_000** -- each unrolled iteration emits at
//!     least one script byte, and a standard transaction is at most 400_000
//!     weight units (the leaf script is ~1 WU/byte of witness), so more than
//!     this is definitionally unspendable as standard; bounding it pre-lowering
//!     also caps the compiler's allocation. (A comprehension over a WITNESS
//!     array is already bounded by the arity limit; this catches const-array and
//!     const-range comprehensions.)

use crate::analysis::consteval::{ConstValue, Env, eval_in_env};
use crate::analysis::sema::{ContractInfo, HashAlg, Len, SpendSig, Ty};
use crate::diagnostics::Diagnostic;
use crate::syntax::ast::{Contract, Expr, Item, Seq, Spend, Stmt};

const MAX_WITNESS_ELEMENTS: u64 = 1000;
const MAX_ELEMENT_BYTES: usize = 520;
const MAX_UNROLL: u64 = 400_000;
/// Conservative per-binder length when a binder's sequence is not const (a
/// witness array); such a binder is already bounded by the arity limit, so this
/// only matters for NESTED comprehensions, where the product is checked.
const WITNESS_BINDER_CAP: u64 = MAX_WITNESS_ELEMENTS;

/// Diagnostics for every resource bound a spend would exceed.
pub fn analyze(contract: &Contract, info: &ContractInfo, env: &Env) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    for item in &contract.items {
        let Item::Spend(s) = item else { continue };
        let Some(sig) = info.spends.iter().find(|x| x.name == s.name.text) else {
            continue;
        };
        check_spend(s, sig, env, &mut diags);
    }
    diags
}

fn check_spend(s: &Spend, sig: &SpendSig, env: &Env, out: &mut Vec<Diagnostic>) {
    // Witness arity and per-element size, from the declared parameter types.
    let mut arity: u64 = 0;
    for p in &sig.params {
        arity = arity.saturating_add(witness_arity(&p.ty, env));
        if let Some(bytes) = element_max_bytes(&p.ty, env)
            && bytes > MAX_ELEMENT_BYTES
        {
            out.push(
                Diagnostic::error(
                    "limits/element",
                    format!(
                        "a witness element of `{}` can be {bytes} bytes, over the {MAX_ELEMENT_BYTES}-byte consensus element limit",
                        p.name
                    ),
                    s.span,
                )
                .with_note("this contract can never be spent as standard"),
            );
        }
    }
    if arity > MAX_WITNESS_ELEMENTS {
        out.push(
            Diagnostic::error(
                "limits/witness-stack",
                format!(
                    "spend `{}` needs {arity} witness elements, over the {MAX_WITNESS_ELEMENTS}-element consensus stack limit",
                    s.name.text
                ),
                s.span,
            )
            .with_note("this contract can never be spent as standard"),
        );
    }

    // Comprehension unroll (the lowered script's size driver).
    for stmt in &s.body {
        match stmt {
            Stmt::Let { value, .. } => check_unroll(value, env, 1, s, out),
            Stmt::Require(req) => {
                for item in &req.items {
                    check_unroll(item, env, 1, s, out);
                }
            }
        }
    }
}

/// Number of witness stack elements a value of `ty` occupies (an array spreads
/// to one element per leaf scalar).
fn witness_arity(ty: &Ty, env: &Env) -> u64 {
    match ty {
        Ty::Array(elem, len) => {
            let n = resolve_len(len, env).unwrap_or(0) as u64;
            n.saturating_mul(witness_arity(elem, env))
        }
        _ => 1,
    }
}

/// Worst-case byte size of a single witness element of `ty`'s leaf scalar (an
/// array's elements are each their own stack element).
fn element_max_bytes(ty: &Ty, env: &Env) -> Option<usize> {
    match ty {
        Ty::Bool => Some(1),
        Ty::Int => Some(5),        // CScriptNum, worst-case sign-extended
        Ty::Signature => Some(65), // 64-byte BIP340 sig + optional sighash byte
        Ty::PublicKey => Some(32),
        Ty::Bytes(len) => resolve_len(len, env),
        Ty::Hash(alg) => Some(hash_len(*alg)),
        Ty::Array(elem, _) => element_max_bytes(elem, env),
        Ty::LockTimeAbs | Ty::LockTimeRel => None, // not witness data
    }
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

/// Walk `e`, multiplying the unroll factor through nested comprehensions;
/// flag any comprehension whose cumulative unroll exceeds the bound.
fn check_unroll(e: &Expr, env: &Env, mult: u64, s: &Spend, out: &mut Vec<Diagnostic>) {
    if let Expr::Comprehension {
        binders,
        where_clauses,
        body,
        acc,
        span,
        ..
    } = e
    {
        let count = binders
            .iter()
            .map(|b| binder_len(&b.seq, env))
            .max()
            .unwrap_or(0);
        let cum = mult.saturating_mul(count);
        if cum > MAX_UNROLL {
            out.push(
                Diagnostic::error(
                    "limits/unroll",
                    format!(
                        "spend `{}` unrolls a comprehension {cum} times, over the {MAX_UNROLL}-iteration budget",
                        s.name.text
                    ),
                    *span,
                )
                .with_note("the lowered script would exceed a standard transaction's weight"),
            );
            return; // one report per offending comprehension; do not recurse deeper
        }
        if let Some(a) = acc {
            check_unroll(&a.init, env, mult, s, out);
        }
        for b in binders {
            if let Seq::Expr(se) = &b.seq {
                check_unroll(se, env, mult, s, out);
            }
        }
        for w in where_clauses {
            check_unroll(w, env, cum, s, out);
        }
        check_unroll(body, env, cum, s, out);
        return;
    }
    for child in children(e) {
        check_unroll(child, env, mult, s, out);
    }
}

/// The iteration count of one binder sequence: the exact length for a const
/// array / literal range, or the witness-array cap otherwise (a witness array
/// is bounded by the arity limit; the cap only bites under nesting).
fn binder_len(seq: &Seq, env: &Env) -> u64 {
    match seq {
        Seq::Range {
            lo, hi, inclusive, ..
        } => match (eval_int(lo, env), eval_int(hi, env)) {
            (Some(l), Some(h)) => {
                let end = if *inclusive { h.saturating_add(1) } else { h };
                (end - l).max(0) as u64
            }
            _ => WITNESS_BINDER_CAP,
        },
        Seq::Expr(e) => match eval_in_env(e, env).0 {
            Some(ConstValue::Array(items)) => items.len() as u64,
            _ => WITNESS_BINDER_CAP,
        },
    }
}

fn eval_int(e: &Expr, env: &Env) -> Option<i128> {
    match eval_in_env(e, env).0 {
        Some(ConstValue::Int(n)) => Some(n),
        _ => None,
    }
}

/// Direct sub-expressions of `e` (for the recursive unroll walk).
fn children(e: &Expr) -> Vec<&Expr> {
    match e {
        Expr::Member { base, .. } => vec![base],
        Expr::Unary { operand, .. } => vec![operand],
        Expr::Binary { lhs, rhs, .. } => vec![lhs, rhs],
        Expr::Compare { first, rest, .. } => {
            let mut v = vec![first.as_ref()];
            v.extend(rest.iter().map(|(_, e)| e));
            v
        }
        Expr::In { value, lo, hi, .. } => vec![value, lo, hi],
        Expr::Index { base, index, .. } => vec![base, index],
        Expr::Call { callee, args, .. } => {
            let mut v = vec![callee.as_ref()];
            v.extend(args.iter().map(|a| &a.value));
            v
        }
        Expr::TypedCtor { args, .. } => args.iter().map(|a| &a.value).collect(),
        Expr::ArrayLit { elems, .. } => elems.iter().collect(),
        // Comprehension handled in check_unroll; leaves have no children.
        _ => Vec::new(),
    }
}
