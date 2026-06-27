//! The concrete Tapscript Miniscript expression for a spend's leaf, derived from
//! the predicate in the SAME canonical order the lowering emits, so re-encoding it
//! reproduces Seal's own leaf bytes. Returns None for predicates outside the
//! Miniscript-expressible fragment (lets, counts, ranges, weighted sums).
//!
//! This is fund-safety-relevant: the string here is what a user would import into
//! Miniscript tooling, so it must encode to exactly the leaf Seal funds. Every
//! emitted expression is gated against rust-miniscript in the differential
//! harness: parse it, re-encode, and require the bytes equal Seal's leaf.

use crate::analysis::consteval::{ConstValue, Env, LockAbs, LockRel, eval_in_env};
use crate::codegen::lower::{is_verify_only_item, item_tail_rank};
use crate::syntax::ast::{CmpOp, Expr, Seq, Spend, Stmt};

/// The Miniscript expression for `spend`'s single leaf, or None when the spend is
/// not Miniscript-expressible.
pub fn spend_descriptor(spend: &Spend, env: &Env) -> Option<String> {
    // Miniscript has no intermediates: a single require block, no `let`s.
    let items = match spend.body.as_slice() {
        [Stmt::Require(req)] => &req.items,
        _ => return None,
    };
    if items.is_empty() {
        return None;
    }
    // A lone threshold is the whole leaf (multi_a, or the n-of-n AND-chain).
    if let [only] = items.as_slice()
        && let Some(d) = threshold_fragment(only, env)
    {
        return Some(d);
    }
    // Canonical order: tail-rank, then the last timelock hoisted to the tail (the
    // optimizer's trailing-CSV/CLTV), mirroring `lower` + `hoist_timelock_to_tail`.
    let mut ordered: Vec<&Expr> = items.iter().collect();
    ordered.sort_by_key(|it| item_tail_rank(it));
    if let Some(pos) = ordered.iter().rposition(|it| is_verify_only_item(it)) {
        let tl = ordered.remove(pos);
        ordered.push(tl);
    }
    let frags: Vec<String> = ordered
        .iter()
        .map(|it| fragment(it, env))
        .collect::<Option<_>>()?;
    Some(nest_and_v(&frags))
}

/// `and_v(v:f1, and_v(v:f2, .. fn))`: every fragment but the last is verify-wrapped
/// (the last leaves the leaf's result on the stack).
fn nest_and_v(frags: &[String]) -> String {
    match frags {
        [f] => f.clone(),
        [f, rest @ ..] => format!("and_v(v:{},{})", f, nest_and_v(rest)),
        [] => String::new(),
    }
}

fn fragment(item: &Expr, env: &Env) -> Option<String> {
    after_fragment(item, env)
        .or_else(|| pk_fragment(item, env))
        .or_else(|| hashlock_fragment(item, env))
        .or_else(|| threshold_fragment(item, env))
}

/// `after(lock)` -> `older(n)` (relative) / `after(n)` (absolute).
fn after_fragment(item: &Expr, env: &Env) -> Option<String> {
    let Expr::Call { callee, args, .. } = item else {
        return None;
    };
    let Expr::Name(f) = callee.as_ref() else {
        return None;
    };
    if f.text != "after" || args.len() != 1 {
        return None;
    }
    match eval_in_env(&args[0].value, env).0? {
        ConstValue::LockRel(LockRel::Blocks(b)) => Some(format!("older({b})")),
        ConstValue::LockRel(LockRel::Units(u)) => {
            Some(format!("older({})", u32::from(u) | (1 << 22)))
        }
        ConstValue::LockAbs(LockAbs::Height(h)) => Some(format!("after({h})")),
        ConstValue::LockAbs(LockAbs::Time(t)) => Some(format!("after({t})")),
        _ => None,
    }
}

/// `k.check(s)` -> `pk(<key hex>)`.
fn pk_fragment(item: &Expr, env: &Env) -> Option<String> {
    let Expr::Call { callee, args, .. } = item else {
        return None;
    };
    let Expr::Member { base, member, .. } = callee.as_ref() else {
        return None;
    };
    if member.text != "check" || args.len() != 1 {
        return None;
    }
    let ConstValue::Bytes(k) = eval_in_env(base, env).0? else {
        return None;
    };
    Some(format!("pk({})", hex(&k)))
}

/// `sha256(p) == h` -> `sha256(<hex>)`, and the other hash algorithms.
fn hashlock_fragment(item: &Expr, env: &Env) -> Option<String> {
    let Expr::Compare { first, rest, .. } = item else {
        return None;
    };
    let [(CmpOp::Eq, rhs)] = rest.as_slice() else {
        return None;
    };
    let Expr::Call { callee, args, .. } = first.as_ref() else {
        return None;
    };
    let Expr::Name(f) = callee.as_ref() else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    let alg = match f.text.as_str() {
        "sha256" => "sha256",
        "hash160" => "hash160",
        "hash256" => "hash256",
        "ripemd160" => "ripemd160",
        _ => return None,
    };
    let ConstValue::Bytes(h) = eval_in_env(rhs, env).0? else {
        return None;
    };
    Some(format!("{alg}({})", hex(&h)))
}

/// `sum(k in keys, s in sigs => k.check(s)) == M` (or `>= M`) -> `multi_a(M, ..)`
/// with keys lexicographically sorted (as Seal emits), collapsing to the n-of-n
/// AND-chain when M equals the key count.
fn threshold_fragment(item: &Expr, env: &Env) -> Option<String> {
    let Expr::Compare { first, rest, .. } = item else {
        return None;
    };
    let [(op, rhs)] = rest.as_slice() else {
        return None;
    };
    if !matches!(op, CmpOp::Eq | CmpOp::Ge) {
        return None;
    }
    let Expr::Comprehension {
        callee,
        binders,
        where_clauses,
        body,
        ..
    } = first.as_ref()
    else {
        return None;
    };
    if callee.text != "sum" || !where_clauses.is_empty() {
        return None;
    }
    let Expr::Call {
        callee: c2, args, ..
    } = body.as_ref()
    else {
        return None;
    };
    let Expr::Member { base, member, .. } = c2.as_ref() else {
        return None;
    };
    if member.text != "check" || args.len() != 1 {
        return None;
    }
    let Expr::Name(kb) = base.as_ref() else {
        return None;
    };
    let mut keys: Option<Vec<Vec<u8>>> = None;
    for b in binders {
        if b.name.text == kb.text {
            let Seq::Expr(seq) = &b.seq else {
                return None;
            };
            let ConstValue::Array(elems) = eval_in_env(seq, env).0? else {
                return None;
            };
            let mut ks = Vec::with_capacity(elems.len());
            for e in elems {
                let ConstValue::Bytes(k) = e else {
                    return None;
                };
                ks.push(k);
            }
            keys = Some(ks);
        }
    }
    let mut keys = keys?;
    keys.sort();
    let ConstValue::Int(m) = eval_in_env(rhs, env).0? else {
        return None;
    };
    let n = keys.len() as i128;
    if m < 1 || m > n {
        return None;
    }
    let hexes: Vec<String> = keys.iter().map(|k| hex(k)).collect();
    if m == n {
        let frags: Vec<String> = hexes.iter().map(|h| format!("pk({h})")).collect();
        Some(nest_and_v(&frags))
    } else {
        Some(format!("multi_a({m},{})", hexes.join(",")))
    }
}

fn hex(b: &[u8]) -> String {
    use std::fmt::Write;
    b.iter().fold(String::with_capacity(b.len() * 2), |mut s, x| {
        let _ = write!(s, "{x:02x}");
        s
    })
}
