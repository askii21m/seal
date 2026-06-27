//! The symbolic decision procedure (Phase 3 of the verification program).
//! Where `certify`'s enumeration only WINDOWS an Int
//! leaf (`BoundedChecked`) or gives up on a too-large domain (`Unbounded`),
//! this module PROVES the three-way equivalence
//!
//! ```text
//! eval_predicate  ⟺  exec(naive)  ⟺  exec(optimized)
//! ```
//!
//! over the leaf's COMPLETE domain, without enumeration.
//!
//! # Independence and soundness
//!
//! Like `certify`, this is an INDEPENDENT oracle: it imports only
//! `ast`/`certify`(the one evaluator)/`consteval`/`interp`/`satisfy`/`sema`
//! -- never `lower` or `optimize` internals -- so it cannot inherit a bug from
//! the pass it checks.
//!
//! The one soundness invariant: **every `Proven` verdict is witnessed by
//! agreement established by operating on the ACTUAL optimized-script bytes**
//! (Engine A re-EXECUTES them at a covering set; Engine B will decode-and-equate
//! them), never by a model that ASSUMES the optimized script's structure. Any
//! construct the procedure cannot model EXACTLY makes it return `None`, and
//! `certify` keeps its existing (already-sound) verdict. A bug here can only
//! ever cost a proof, never produce a false one.
//!
//! # Engine A -- single Int witness variable
//!
//! For a leaf with exactly one scalar `Int` witness parameter `x` (every other
//! parameter finitely enumerable: `Bool`/`Signature`/arrays of those), fix the
//! other parameters to each of their finitely-many values ("slices"). Within a
//! slice the leaf is a function of `x` alone. We prove three-way agreement over
//! the ENTIRE machine domain `M = ±(2^31-1)` like so:
//!
//!  1. Symbolically execute the naive and optimized scripts, and walk the source
//!     predicate, as PIECEWISE-AFFINE functions of `x`, collecting a SUPERSET of
//!     every breakpoint (the integer `x` values at which any of the three can
//!     change). The fragment has no multiplication (`ast::BinaryOp` is `Add`/
//!     `Sub`), so the only breakpoint sources are the comparison/`within`/`min`/
//!     `max`/`abs` crossings, all collected; anything else -> abstain (`None`).
//!  2. Between two consecutive breakpoints every affine atom is monotone, so
//!     each of the three programs is CONSTANT on the open gap. We therefore prove
//!     agreement by RE-EXECUTING all three at one representative `x` per gap (and
//!     at each breakpoint, and at the `M` extremes, and just outside `M`).
//!     Re-execution -- not the symbolic values -- is the soundness anchor: a bug
//!     in the piecewise-affine algebra can only add spurious breakpoints (more
//!     sampling) or, if it dropped one, be caught by the exhaustive reduced-`M`
//!     property test; it can never make a non-equal leaf look equal.
//!  3. Out of `M`: any `x` whose CScriptNum encoding exceeds 4 bytes (or is
//!     non-minimal) is rejected by `num(v,4)` on the first numeric op that
//!     consumes it -- and in this fragment `x` is ONLY ever consumed numerically
//!     (else step 1 abstains) -- so BOTH scripts reject it identically. We
//!     confirm at `±(M+1)` and argue the rest structurally.
//!
//! Engine A abstains on `OP_IF`/`OP_NOTIF` (branching), bytewise `OP_EQUAL`,
//! `OP_SIZE`, the hash ops, and CLTV/CSV -- none appear in a single-Int affine
//! leaf like `mirage`. Engine B (a separate increment) handles the no-Int
//! structural cases such as `cat_bounty`.

use std::collections::BTreeSet;

use crate::analysis::consteval::{ConstValue, Env, MACHINE_MAX};
use crate::analysis::sema::{Len, SpendSig, Ty};
use crate::codegen::lower::LoweredLeaf;
use crate::syntax::ast::{BinaryOp, CmpOp, Expr, Stmt, UnaryOp};
use crate::verify::certify::{ProvenKind, eval_predicate};
use crate::verify::interp::{Context, execute};
use crate::verify::satisfy::{SatValue, build_witness};

/// A guard on the symbolic work per slice: abstain rather than blow up.
const MAX_CUTS: usize = 4096;
/// A guard on the number of slices (product of the non-Int finite domains).
const MAX_SLICES: u128 = 1 << 16;

/// Attempt a full-domain proof of a spend leaf. `Some(kind)` ONLY when
/// equivalence is genuinely proven over the complete domain; `None` otherwise
/// (the caller then keeps its enumeration verdict). Total and panic-free.
#[allow(clippy::too_many_arguments)]
pub(crate) fn try_prove(
    body: &[Stmt],
    sig: &SpendSig,
    env: &Env,
    naive: &LoweredLeaf,
    opt: &LoweredLeaf,
    marker: &[u8],
    ctx: &Context,
) -> Option<ProvenKind> {
    if let Some(k) = engine_a(body, sig, env, naive, opt, marker, ctx) {
        return Some(k);
    }
    if let Some(k) = engine_an(body, sig, env, naive, opt, marker, ctx) {
        return Some(k);
    }
    engine_b(body, sig, env, naive, opt)
}

// --- Engine A: single Int witness variable ---

#[allow(clippy::too_many_arguments)]
fn engine_a(
    body: &[Stmt],
    sig: &SpendSig,
    env: &Env,
    naive: &LoweredLeaf,
    opt: &LoweredLeaf,
    marker: &[u8],
    ctx: &Context,
) -> Option<ProvenKind> {
    // Exactly one scalar Int parameter, and no Int hidden inside an array (an
    // array-of-Int would be a multi-variable problem Engine A does not handle).
    let int_params: Vec<&str> = sig
        .params
        .iter()
        .filter(|p| matches!(p.ty, Ty::Int))
        .map(|p| p.name.as_str())
        .collect();
    if int_params.len() != 1 {
        return None;
    }
    if sig.params.iter().any(|p| ty_has_array_int(&p.ty)) {
        return None;
    }
    let xname = int_params[0].to_string();

    // Finite domains for every OTHER parameter (so each "slice" fixes them and
    // leaves the leaf a function of x alone). Abstain if any is not finite.
    let mut other: Vec<(String, Vec<SatValue>)> = Vec::new();
    let mut slices: u128 = 1;
    for p in &sig.params {
        if p.name == xname {
            continue;
        }
        let d = finite_domain(&p.ty, env)?;
        slices = slices.checked_mul(d.len() as u128)?;
        if slices > MAX_SLICES {
            return None;
        }
        other.push((p.name.clone(), d));
    }

    let mut cells_proven: usize = 0;
    for s in 0..slices {
        // Decode `s` (mixed radix) into one concrete value per other parameter.
        let mut c = s;
        let mut fixed: Vec<(String, SatValue)> = Vec::with_capacity(other.len());
        for (name, dom) in &other {
            let idx = (c % dom.len() as u128) as usize;
            c /= dom.len() as u128;
            fixed.push((name.clone(), dom[idx].clone()));
        }

        // A complete breakpoint set for this slice, from BOTH scripts (so a
        // buggy/divergent opt cannot hide a transition between sampled points)
        // AND the source predicate (so a T1 transition is bracketed too).
        let mut bps: BTreeSet<i128> = BTreeSet::new();
        collect_script_breakpoints(naive, sig, env, &xname, &fixed, marker, ctx, &mut bps)?;
        collect_script_breakpoints(opt, sig, env, &xname, &fixed, marker, ctx, &mut bps)?;
        collect_pred_breakpoints(body, env, &xname, &mut bps)?;

        // The covering set: every breakpoint, one interior point per gap, the
        // in-M extremes, and the just-out-of-M sentinels. Each gap is constant
        // for all three (no breakpoint inside), so its representative decides it.
        let cover = covering_points(&bps);
        cells_proven = cells_proven.saturating_add(cover.len());

        for x in cover {
            let plan = full_plan(&xname, x, &fixed);
            let naive_ok = run(naive, sig, env, &plan, marker, ctx)?;
            let opt_ok = run(opt, sig, env, &plan, marker, ctx)?;
            // T2: optimizer must match the naive lowering at every point.
            if naive_ok != opt_ok {
                return None;
            }
            let in_m = (-MACHINE_MAX..=MACHINE_MAX).contains(&x);
            if !in_m {
                // Out of the 4-byte CScriptNum domain: both MUST reject. If the
                // script somehow accepts an over-long operand, the model does not
                // hold -- abstain rather than risk a false proof.
                if naive_ok {
                    return None;
                }
                continue;
            }
            // T1: the independent predicate must match the naive script. The
            // symbolic engine never models timelocks (it abstains on `after`),
            // so pass no timelock context.
            match eval_predicate(body, &plan, env, ctx.verify_sig, marker, None) {
                Some(pred) if pred == naive_ok => {}
                _ => return None, // disagreement OR an abstain -> cannot prove T1 here
            }
        }
    }

    Some(ProvenKind::FullInt {
        var: xname,
        breakpoints: cells_proven,
    })
}

/// Build + execute one leaf at a concrete plan; `Some(true)` = the script
/// accepted, `Some(false)` = rejected/aborted, `None` = the witness could not
/// be built (abstain).
fn run(
    leaf: &LoweredLeaf,
    sig: &SpendSig,
    env: &Env,
    plan: &[(String, SatValue)],
    marker: &[u8],
    ctx: &Context,
) -> Option<bool> {
    let stack = build_witness(leaf, sig, env, plan, marker).ok()?;
    Some(execute(&leaf.script, &stack, ctx).is_ok())
}

/// The full witness plan for a slice: the Int param set to `x`, the others to
/// their fixed slice values.
fn full_plan(xname: &str, x: i128, fixed: &[(String, SatValue)]) -> Vec<(String, SatValue)> {
    let mut plan = Vec::with_capacity(fixed.len() + 1);
    plan.push((xname.to_string(), SatValue::Int(x as i64)));
    plan.extend(fixed.iter().cloned());
    plan
}

/// Finite SatValue choices for a non-Int parameter type, or `None` if the type
/// is not finitely enumerable here. Mirrors `certify::param_domain`'s encoding
/// choices but returns only the satisfier values (Engine A needs no `Val`).
fn finite_domain(ty: &Ty, env: &Env) -> Option<Vec<SatValue>> {
    match ty {
        Ty::Bool => Some(vec![SatValue::Bool(false), SatValue::Bool(true)]),
        Ty::Signature => Some(vec![SatValue::Sig(false), SatValue::Sig(true)]),
        Ty::Array(elem, len) => {
            let n = resolve_len(len, env)?;
            if n > 24 {
                return None;
            }
            let base = finite_domain(elem, env)?;
            let total = base.len().checked_pow(n as u32)?;
            if total as u128 > MAX_SLICES {
                return None;
            }
            let mut out = Vec::with_capacity(total);
            for combo in 0..total {
                let mut c = combo;
                let mut items = Vec::with_capacity(n);
                for _ in 0..n {
                    items.push(base[c % base.len()].clone());
                    c /= base.len();
                }
                out.push(SatValue::Array(items));
            }
            Some(out)
        }
        // Int (the variable, handled separately) and Bytes/Hash/PublicKey are
        // not finitely enumerable as a slice dimension.
        _ => None,
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

fn ty_has_array_int(ty: &Ty) -> bool {
    match ty {
        Ty::Array(elem, _) => matches!(**elem, Ty::Int) || ty_has_array_int(elem),
        _ => false,
    }
}

/// From a complete breakpoint set, produce the integer points to test: each
/// breakpoint and its immediate neighbors, one interior point of every gap, the
/// in-`M` extremes, and the just-out-of-`M` sentinels. Generous on purpose --
/// extra points only cost a little execution; the soundness need is that every
/// cell (constant region) is hit at least once.
fn covering_points(bps: &BTreeSet<i128>) -> Vec<i128> {
    let m = MACHINE_MAX;
    let mut pts: BTreeSet<i128> = BTreeSet::new();
    pts.insert(-m);
    pts.insert(m);
    pts.insert(-(m + 1)); // out of M (5-byte operand)
    pts.insert(m + 1);

    // In-range breakpoints and their neighbors.
    let clamped: Vec<i128> = bps
        .iter()
        .copied()
        .filter(|b| (-m..=m).contains(b))
        .collect();
    for &b in &clamped {
        for d in [-1, 0, 1] {
            let p = b + d;
            if (-m..=m).contains(&p) {
                pts.insert(p);
            }
        }
    }
    // One interior point per gap between consecutive sorted sample anchors.
    let mut anchors: Vec<i128> = std::iter::once(-m)
        .chain(clamped.iter().copied())
        .chain(std::iter::once(m))
        .collect();
    anchors.sort_unstable();
    anchors.dedup();
    for w in anchors.windows(2) {
        let (lo, hi) = (w[0], w[1]);
        if hi - lo >= 2 {
            pts.insert(lo + (hi - lo) / 2);
        }
    }
    pts.into_iter().collect()
}

// --- breakpoints from the source predicate (T1 coverage) ---

/// Collect a superset of the source predicate's breakpoints in `x`, by
/// evaluating the predicate through the SAME piecewise-affine algebra the script
/// pass uses (so nested `min`/`max`/`abs`/`within` are handled exactly). The
/// breakpoints of the resulting 0/1 function are its cuts. Returns `None`
/// (abstain) if `x` reaches any position not reducible to that fragment (a hash
/// argument, an index, a comprehension over x, a bytewise equality...).
///
/// Opaque booleans -- `k.check(sig)` and anything x-free we cannot fold -- are
/// modeled as the constant `1`: sound for a breakpoint SUPERSET (treating them
/// as true never hides a downstream breakpoint; if actually false the real
/// predicate is constant there, a subset). The actual truth is checked by
/// `eval_predicate` at the covering points, not here.
fn collect_pred_breakpoints(
    body: &[Stmt],
    env: &Env,
    xname: &str,
    out: &mut BTreeSet<i128>,
) -> Option<()> {
    let mut scope: Vec<(String, Pwa)> = Vec::new();
    for stmt in body {
        match stmt {
            Stmt::Let { name, value, .. } => {
                let v = pred_pwa(value, &scope, env, xname)?;
                scope.push((name.text.clone(), v));
            }
            Stmt::Require(req) => {
                for item in &req.items {
                    // `after(lock)` is a timelock, never a function of x.
                    if is_call(item, "after") {
                        guard_no_x(item, xname)?;
                        continue;
                    }
                    let p = pred_pwa(item, &scope, env, xname)?;
                    for &c in &p.cuts {
                        out.insert(c);
                    }
                    // Bound the accumulated cut set, mirroring the script side's
                    // MAX_CUTS guard (real predicates have far fewer cuts).
                    if out.len() > MAX_CUTS {
                        return None;
                    }
                }
            }
        }
    }
    Some(())
}

/// Evaluate a predicate expression to a piecewise-affine function of `x` (a
/// numeric value, or a 0/1-valued boolean). `None` to abstain.
fn pred_pwa(e: &Expr, scope: &[(String, Pwa)], env: &Env, xname: &str) -> Option<Pwa> {
    match e {
        Expr::Int { text, .. } => Some(Pwa::constant(parse_int(text)?)),
        Expr::Bool { value, .. } => Some(Pwa::constant(*value as i128)),
        Expr::Name(id) if id.text == xname => Some(Pwa::identity()),
        Expr::Name(id) => {
            if let Some((_, p)) = scope.iter().rev().find(|(n, _)| *n == id.text) {
                return Some(p.clone());
            }
            match env.get(&id.text) {
                Some(ConstValue::Int(n)) => Some(Pwa::constant(*n)),
                Some(ConstValue::Bool(b)) => Some(Pwa::constant(*b as i128)),
                _ => None, // a non-numeric const used as a value -> abstain
            }
        }
        Expr::Unary {
            op: UnaryOp::Neg,
            operand,
            ..
        } => Some(pwa_neg(&pred_pwa(operand, scope, env, xname)?)),
        Expr::Unary {
            op: UnaryOp::Not,
            operand,
            ..
        } => {
            // logical not of a 0/1 bool: (b == 0)
            pwa_cmp(
                &pred_pwa(operand, scope, env, xname)?,
                CmpOp::Eq,
                &Pwa::constant(0),
            )
        }
        Expr::Binary { op, lhs, rhs, .. } => {
            let a = pred_pwa(lhs, scope, env, xname)?;
            let b = pred_pwa(rhs, scope, env, xname)?;
            match op {
                BinaryOp::Add => pwa_add(&a, &b),
                BinaryOp::Sub => pwa_sub(&a, &b),
            }
        }
        Expr::Compare { first, rest, .. } => {
            let mut acc = Pwa::constant(1);
            let mut prev = pred_pwa(first, scope, env, xname)?;
            for (op, next) in rest {
                let nv = pred_pwa(next, scope, env, xname)?;
                acc = pwa_min(&acc, &pwa_cmp(&prev, *op, &nv)?)?;
                prev = nv;
            }
            Some(acc)
        }
        Expr::In {
            value,
            lo,
            hi,
            inclusive,
            ..
        } => {
            let v = pred_pwa(value, scope, env, xname)?;
            let lo = pred_pwa(lo, scope, env, xname)?;
            let hi = pred_pwa(hi, scope, env, xname)?;
            let ge = pwa_cmp(&v, CmpOp::Ge, &lo)?;
            let up = if *inclusive { CmpOp::Le } else { CmpOp::Lt };
            let hic = pwa_cmp(&v, up, &hi)?;
            pwa_min(&ge, &hic)
        }
        Expr::Call { callee, args, .. } => {
            // `X.check(Y)` (a member call): an opaque boolean, modeled as 1; just
            // ensure x does not hide in its arguments.
            if let Expr::Member { member, .. } = callee.as_ref() {
                if member.text == "check" {
                    for a in args {
                        guard_no_x(&a.value, xname)?;
                    }
                    return Some(Pwa::constant(1));
                }
                guard_no_x(e, xname)?;
                return Some(Pwa::constant(1)); // any other opaque member result, x-free
            }
            let Expr::Name(f) = callee.as_ref() else {
                return guard_no_x(e, xname).map(|_| Pwa::constant(1));
            };
            match (f.text.as_str(), args.len()) {
                ("min", 2) => pwa_min(
                    &pred_pwa(&args[0].value, scope, env, xname)?,
                    &pred_pwa(&args[1].value, scope, env, xname)?,
                ),
                ("max", 2) => pwa_max(
                    &pred_pwa(&args[0].value, scope, env, xname)?,
                    &pred_pwa(&args[1].value, scope, env, xname)?,
                ),
                ("abs", 1) => pwa_abs(&pred_pwa(&args[0].value, scope, env, xname)?),
                ("int", 1) => pred_pwa(&args[0].value, scope, env, xname),
                ("select", 3) => {
                    let c = pred_pwa(&args[0].value, scope, env, xname)?;
                    let t = pred_pwa(&args[1].value, scope, env, xname)?;
                    let f = pred_pwa(&args[2].value, scope, env, xname)?;
                    pwa_select(&c, &t, &f)
                }
                // hashes etc.: x must not appear, and the result is non-numeric
                // (so it can only feed a bytewise op, which we abstain on anyway).
                _ => {
                    guard_no_x(e, xname)?;
                    None
                }
            }
        }
        // Anything else: x must not appear (else outside the model -> abstain).
        other => {
            guard_no_x(other, xname)?;
            None
        }
    }
}

fn is_call(e: &Expr, name: &str) -> bool {
    matches!(e, Expr::Call { callee, .. } if matches!(callee.as_ref(), Expr::Name(f) if f.text == name))
}

/// Abstain unless `x` does not appear anywhere in `e`.
fn guard_no_x(e: &Expr, xname: &str) -> Option<()> {
    if mentions(e, xname) { None } else { Some(()) }
}

fn mentions(e: &Expr, xname: &str) -> bool {
    let mut found = false;
    walk(e, &mut |n| {
        if let Expr::Name(id) = n
            && id.text == xname
        {
            found = true;
        }
    });
    found
}

fn parse_int(text: &str) -> Option<i128> {
    let t: String = text.chars().filter(|c| *c != '_').collect();
    if let Some(hex) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        i128::from_str_radix(hex, 16).ok()
    } else {
        t.parse::<i128>().ok()
    }
}

/// Pre-order AST walk (only the variants that can carry a `Name`), for
/// `mentions`.
fn walk(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    match e {
        Expr::Member { base, .. } => walk(base, f),
        Expr::Index { base, index, .. } => {
            walk(base, f);
            walk(index, f);
        }
        Expr::Unary { operand, .. } => walk(operand, f),
        Expr::Binary { lhs, rhs, .. } => {
            walk(lhs, f);
            walk(rhs, f);
        }
        Expr::Compare { first, rest, .. } => {
            walk(first, f);
            for (_, e) in rest {
                walk(e, f);
            }
        }
        Expr::In { value, lo, hi, .. } => {
            walk(value, f);
            walk(lo, f);
            walk(hi, f);
        }
        Expr::Call { callee, args, .. } => {
            walk(callee, f);
            for a in args {
                walk(&a.value, f);
            }
        }
        Expr::TypedCtor { args, .. } => {
            for a in args {
                walk(&a.value, f);
            }
        }
        Expr::ArrayLit { elems, .. } => {
            for e in elems {
                walk(e, f);
            }
        }
        Expr::Comprehension {
            acc,
            binders,
            where_clauses,
            body,
            ..
        } => {
            if let Some(a) = acc {
                walk(&a.init, f);
            }
            for b in binders {
                match &b.seq {
                    crate::syntax::ast::Seq::Expr(e) => walk(e, f),
                    crate::syntax::ast::Seq::Range { lo, hi, .. } => {
                        walk(lo, f);
                        walk(hi, f);
                    }
                }
            }
            for w in where_clauses {
                walk(w, f);
            }
            walk(body, f);
        }
        Expr::Int { .. }
        | Expr::Str { .. }
        | Expr::Bool { .. }
        | Expr::Duration { .. }
        | Expr::Name(_) => {}
    }
}

// --- breakpoints from a script (piecewise-affine symbolic execution) ---

/// A symbolic stack value during single-`x` execution: a CScriptNum that is a
/// piecewise-affine function of `x` (`Num`), or concrete bytes (`Bytes`, e.g. a
/// fixed signature/pubkey/data push). Values are decoded to `Num` lazily when a
/// numeric op consumes them, mirroring the interpreter.
#[derive(Clone)]
enum SymVal {
    Num(Pwa),
    Bytes(Vec<u8>),
}

/// Build the symbolic initial stack for a slice (the `x` slot is the identity
/// function of x; every other slot is its concrete bytes) and symbolically
/// execute `leaf`, inserting the breakpoints of its accept-function into `out`.
/// `None` (abstain) on any construct outside the affine no-branch fragment.
#[allow(clippy::too_many_arguments)]
fn collect_script_breakpoints(
    leaf: &LoweredLeaf,
    sig: &SpendSig,
    env: &Env,
    xname: &str,
    fixed: &[(String, SatValue)],
    marker: &[u8],
    ctx: &Context,
    out: &mut BTreeSet<i128>,
) -> Option<()> {
    // Concrete witness for the slice (x set to a dummy; its slot is overwritten
    // with the symbolic identity below).
    let dummy = full_plan(xname, 0, fixed);
    let stack0 = build_witness(leaf, sig, env, &dummy, marker).ok()?;
    let xi = leaf.witness_order.iter().position(|n| n == xname)?;

    let init: Vec<SymVal> = stack0
        .iter()
        .enumerate()
        .map(|(i, b)| {
            if i == xi {
                SymVal::Num(Pwa::identity())
            } else {
                SymVal::Bytes(b.clone())
            }
        })
        .collect();

    let accept = sym_accept(&leaf.script, init, ctx)?;
    for &c in &accept.cuts {
        out.insert(c);
    }
    Some(())
}

/// Symbolically execute a straight-line (no-branch) affine script over the
/// single variable x, returning the accept-function as a piecewise 0/1 `Pwa`
/// (its cuts are the breakpoints). `None` on any opcode outside the modeled
/// fragment, on a stack/type error, or on a cut-count blowup -- all of which
/// make Engine A abstain (sound: `certify` keeps its verdict).
fn sym_accept(script: &[u8], init: Vec<SymVal>, ctx: &Context) -> Option<Pwa> {
    let mut stack = init;
    // `live` is the conjunction of every VERIFY/...VERIFY condition so far: the
    // accept-function is `live AND truthy(top)` at the end.
    let mut live = Pwa::constant(1);
    let mut i = 0usize;

    while i < script.len() {
        let op = script[i];
        i += 1;

        // Pushes.
        if op == 0x4e {
            return None; // PUSHDATA4
        }
        if let Some(len) = push_len(op, script, &mut i)? {
            let end = i.checked_add(len)?;
            if end > script.len() {
                return None;
            }
            stack.push(SymVal::Bytes(script[i..end].to_vec()));
            i = end;
            continue;
        }
        if let Some(v) = small_push(op) {
            stack.push(SymVal::Bytes(v));
            continue;
        }

        match op {
            // --- stack ops (shape only; no x-dependence introduced) ---
            0x75 => {
                stack.pop()?; // DROP
            }
            0x6d => {
                stack.pop()?;
                stack.pop()?; // 2DROP
            }
            0x76 => {
                let t = stack.last()?.clone(); // DUP
                stack.push(t);
            }
            0x77 => {
                // NIP
                let n = stack.len();
                if n < 2 {
                    return None;
                }
                stack.remove(n - 2);
            }
            0x78 => {
                // OVER
                let n = stack.len();
                if n < 2 {
                    return None;
                }
                stack.push(stack[n - 2].clone());
            }
            0x7c => {
                // SWAP
                let n = stack.len();
                if n < 2 {
                    return None;
                }
                stack.swap(n - 1, n - 2);
            }
            0x7d => {
                // TUCK
                let n = stack.len();
                if n < 2 {
                    return None;
                }
                let t = stack[n - 1].clone();
                stack.insert(n - 2, t);
            }
            // PICK/ROLL with a CONSTANT depth (the only kind the compiler emits)
            // -- depth must be a concrete number, not x-dependent.
            0x79 | 0x7a => {
                let d = as_const_num(&stack.pop()?)?;
                if d < 0 || d as usize >= stack.len() {
                    return None;
                }
                let idx = stack.len() - 1 - d as usize;
                if op == 0x79 {
                    stack.push(stack[idx].clone()); // PICK: copy
                } else {
                    let v = stack.remove(idx); // ROLL: move
                    stack.push(v);
                }
            }
            // --- arithmetic / comparison (the affine core) ---
            0x69 => {
                // VERIFY: fold the popped condition into `live`.
                let c = to_num(stack.pop()?)?;
                live = pwa_min(&live, &pwa_truthy_strict(&c)?)?; // AND of 0/1 values
            }
            0x8b | 0x8c | 0x8f | 0x90 | 0x91 | 0x92 => {
                // Unary numeric: 1ADD,1SUB,NEGATE,ABS,NOT,0NOTEQUAL
                let x = to_num(stack.pop()?)?;
                let r = match op {
                    0x8b => pwa_add_const(&x, 1),
                    0x8c => pwa_add_const(&x, -1),
                    0x8f => pwa_neg(&x),
                    0x90 => pwa_abs(&x)?,
                    0x91 => pwa_cmp_const(&x, CmpKind::EqZero)?,
                    _ => pwa_cmp_const(&x, CmpKind::NeZero)?, // 0x92
                };
                stack.push(SymVal::Num(r));
            }
            0x93 | 0x94 | 0x9a | 0x9b | 0x9c | 0x9d | 0x9e | 0x9f | 0xa0 | 0xa1 | 0xa2 | 0xa3
            | 0xa4 => {
                // Binary numeric.
                let b = to_num(stack.pop()?)?;
                let a = to_num(stack.pop()?)?;
                if op == 0x9d {
                    // NUMEQUALVERIFY: fold into `live`, push nothing.
                    let eq = pwa_cmp(&a, CmpOp::Eq, &b)?;
                    live = pwa_min(&live, &eq)?;
                    continue;
                }
                let r = match op {
                    0x93 => pwa_add(&a, &b)?,
                    0x94 => pwa_sub(&a, &b)?,
                    0x9a => pwa_min(&pwa_truthy_strict(&a)?, &pwa_truthy_strict(&b)?)?, // BOOLAND
                    0x9b => pwa_max(&pwa_truthy_strict(&a)?, &pwa_truthy_strict(&b)?)?, // BOOLOR
                    0x9c => pwa_cmp(&a, CmpOp::Eq, &b)?,
                    0x9e => pwa_cmp(&a, CmpOp::Ne, &b)?,
                    0x9f => pwa_cmp(&a, CmpOp::Lt, &b)?,
                    0xa0 => pwa_cmp(&a, CmpOp::Gt, &b)?,
                    0xa1 => pwa_cmp(&a, CmpOp::Le, &b)?,
                    0xa2 => pwa_cmp(&a, CmpOp::Ge, &b)?,
                    0xa3 => pwa_min(&a, &b)?,
                    _ => pwa_max(&a, &b)?, // 0xa4 MAX
                };
                stack.push(SymVal::Num(r));
            }
            0xa5 => {
                // WITHIN: x in [lo, hi)  ==  lo <= x AND x < hi
                let hi = to_num(stack.pop()?)?;
                let lo = to_num(stack.pop()?)?;
                let x = to_num(stack.pop()?)?;
                let ge = pwa_cmp(&x, CmpOp::Ge, &lo)?;
                let lt = pwa_cmp(&x, CmpOp::Lt, &hi)?;
                stack.push(SymVal::Num(pwa_min(&ge, &lt)?));
            }
            // CHECKSIG/CHECKSIGADD: the sig+key are CONCRETE in this slice, so
            // the result is a constant in x (evaluate via the shared oracle).
            0xac | 0xad => {
                let pubkey = to_bytes(stack.pop()?)?;
                let sig = to_bytes(stack.pop()?)?;
                let ok = check_sig_const(&sig, &pubkey, ctx)?;
                if op == 0xad {
                    // CHECKSIGVERIFY
                    live = pwa_min(&live, &Pwa::constant(ok as i128))?;
                } else {
                    stack.push(SymVal::Num(Pwa::constant(ok as i128)));
                }
            }
            0xba => {
                // CHECKSIGADD: n + (1|0)
                let pubkey = to_bytes(stack.pop()?)?;
                let n = to_num(stack.pop()?)?;
                let sig = to_bytes(stack.pop()?)?;
                let ok = check_sig_const(&sig, &pubkey, ctx)?;
                stack.push(SymVal::Num(pwa_add_const(&n, ok as i128)));
            }
            // Everything else (IF/NOTIF/ELSE/ENDIF, EQUAL, SIZE, hashes,
            // CLTV/CSV, ...) is outside Engine A's fragment: abstain.
            _ => return None,
        }
        if total_cuts(&stack, &live) > MAX_CUTS {
            return None;
        }
    }

    // Tail CLEANSTACK: exactly one element left, accept = live AND truthy(top).
    if stack.len() != 1 {
        return None;
    }
    let top = to_num(stack.pop()?)?;
    pwa_min(&live, &pwa_truthy_strict(&top)?)
}

fn total_cuts(stack: &[SymVal], live: &Pwa) -> usize {
    live.cuts.len()
        + stack
            .iter()
            .map(|v| match v {
                SymVal::Num(p) => p.cuts.len(),
                SymVal::Bytes(_) => 0,
            })
            .sum::<usize>()
}

/// A concrete numeric value from a symbolic value (only when it is constant in
/// x); used for PICK/ROLL depths. `None` if x-dependent or non-numeric.
fn as_const_num(v: &SymVal) -> Option<i64> {
    match v {
        SymVal::Bytes(b) => decode_minimal(b).ok(),
        SymVal::Num(p) => p.as_constant().and_then(|c| i64::try_from(c).ok()),
    }
}

/// Coerce a symbolic value to a numeric `Pwa` (decoding concrete bytes as a
/// CScriptNum). `None` if the bytes are not a valid <=4-byte minimal number.
fn to_num(v: SymVal) -> Option<Pwa> {
    match v {
        SymVal::Num(p) => Some(p),
        SymVal::Bytes(b) => {
            if b.len() > 4 {
                return None;
            }
            Some(Pwa::constant(decode_minimal(&b).ok()? as i128))
        }
    }
}

fn to_bytes(v: SymVal) -> Option<Vec<u8>> {
    match v {
        SymVal::Bytes(b) => Some(b),
        SymVal::Num(_) => None, // a symbolic number is never a key/sig in our scripts
    }
}

/// Evaluate CHECKSIG on concrete operands, mirroring `interp::check_sig`. The
/// result is a fixed bool (the slice fixes the signature), so it is constant in
/// x. Returns `None` (abstain) on the ABORT cases -- but an abort means the real
/// script rejects for all x in this slice, which the re-execution at the
/// covering points will reflect, so abstaining is the safe choice.
fn check_sig_const(sig: &[u8], pubkey: &[u8], ctx: &Context) -> Option<bool> {
    if pubkey.is_empty() {
        return None; // ABORT in interp -> abstain
    }
    if pubkey.len() == 32 && !sig.is_empty() && !(ctx.verify_sig)(pubkey, sig) {
        return None; // non-empty invalid sig ABORTS -> abstain
    }
    Some(!sig.is_empty())
}

// --- the piecewise-affine algebra over a single integer variable x ---

/// `a0 + a1*x`.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Aff {
    a0: i128,
    a1: i128,
}
impl Aff {
    fn eval(self, x: i128) -> Option<i128> {
        self.a1.checked_mul(x)?.checked_add(self.a0)
    }
}

/// A piecewise-affine function of `x`. `cuts` are strictly-increasing integers;
/// `pieces[i]` (length `cuts.len()+1`) applies on cell `i`, i.e. for
/// `cuts[i-1] <= x < cuts[i]` with `cuts[-1] = -inf`, `cuts[len] = +inf`. `cuts`
/// is always a SUPERSET of the true breakpoints, so each cell is a single
/// affine region.
#[derive(Clone, PartialEq, Eq)]
struct Pwa {
    cuts: Vec<i128>,
    pieces: Vec<Aff>,
}

impl Pwa {
    fn constant(c: i128) -> Pwa {
        Pwa {
            cuts: vec![],
            pieces: vec![Aff { a0: c, a1: 0 }],
        }
    }
    fn identity() -> Pwa {
        Pwa {
            cuts: vec![],
            pieces: vec![Aff { a0: 0, a1: 1 }],
        }
    }
    fn as_constant(&self) -> Option<i128> {
        if self.pieces.len() == 1 && self.pieces[0].a1 == 0 {
            Some(self.pieces[0].a0)
        } else {
            None
        }
    }
    /// The piece (affine) governing value at `x`.
    fn piece_at(&self, x: i128) -> Aff {
        // cell i is the number of cuts <= x.
        let i = self.cuts.partition_point(|&c| c <= x);
        self.pieces[i]
    }
    /// A representative integer inside cell `i` (used to look up a coarser
    /// function on a finer grid). Cells are `[cuts[i-1], cuts[i])`.
    fn cell_rep(&self, i: usize) -> i128 {
        if i == 0 {
            // The leftmost cell `(-inf, cuts[0])`; or the whole line if no cuts.
            self.cuts.first().map_or(0, |c| c - 1)
        } else {
            self.cuts[i - 1] // the cell's included lower bound
        }
    }
}

/// Add cuts bracketing where the affine `c0 + c1*x` crosses zero, so the sign
/// change is at a cell boundary. The crossing is `x* = -c0/c1`, with
/// `q = div_euclid(-c0, c1)` satisfying `|x* - q| < 1`; the integer transition
/// thus lies in `{q, q+1}`. We insert `{q-1, q, q+1, q+2}` -- a deliberately
/// generous window so any div_euclid rounding subtlety still leaves the
/// transition strictly inside the bracketed cuts. Extra cuts only add sampling;
/// they can never hide a breakpoint. No crossing when `c1 == 0`.
///
/// `None` on i128 overflow: for a compilable contract the interval engine bounds
/// every magnitude to M, so this is unreachable -- but abstaining (rather than
/// computing a wrapped, possibly mis-placed cut that could HIDE a breakpoint) is
/// the only sound response, so the caller propagates it.
fn bracket_crossing(c0: i128, c1: i128, out: &mut BTreeSet<i128>) -> Option<()> {
    if c1 == 0 {
        return Some(());
    }
    let q = c0.checked_neg()?.div_euclid(c1);
    for d in -1..=2 {
        out.insert(q.checked_add(d)?);
    }
    Some(())
}

/// Merge two cut lists into a sorted-unique superset.
fn merge_cuts(a: &[i128], b: &[i128]) -> Vec<i128> {
    let mut s: BTreeSet<i128> = a.iter().copied().collect();
    s.extend(b.iter().copied());
    s.into_iter().collect()
}

/// Re-express `p` over a finer cut set `cuts` (a superset of `p.cuts`): each new
/// cell lies inside one old cell, so its affine is the old piece there.
fn refine(p: &Pwa, cuts: &[i128]) -> Pwa {
    if cuts == p.cuts.as_slice() {
        return p.clone();
    }
    let n = cuts.len() + 1;
    let mut pieces = Vec::with_capacity(n);
    let tmp = Pwa {
        cuts: cuts.to_vec(),
        pieces: vec![Aff { a0: 0, a1: 0 }; n],
    };
    for i in 0..n {
        let rep = tmp.cell_rep(i);
        pieces.push(p.piece_at(rep));
    }
    Pwa {
        cuts: cuts.to_vec(),
        pieces,
    }
}

/// Combine two functions cellwise where the result is affine (ADD/SUB): no new
/// breakpoints.
fn pwa_zip(a: &Pwa, b: &Pwa, f: impl Fn(Aff, Aff) -> Option<Aff>) -> Option<Pwa> {
    let cuts = merge_cuts(&a.cuts, &b.cuts);
    let ra = refine(a, &cuts);
    let rb = refine(b, &cuts);
    let mut pieces = Vec::with_capacity(ra.pieces.len());
    for (pa, pb) in ra.pieces.iter().zip(&rb.pieces) {
        pieces.push(f(*pa, *pb)?);
    }
    Some(normalize(Pwa { cuts, pieces }))
}

fn pwa_add(a: &Pwa, b: &Pwa) -> Option<Pwa> {
    pwa_zip(a, b, |x, y| {
        Some(Aff {
            a0: x.a0.checked_add(y.a0)?,
            a1: x.a1.checked_add(y.a1)?,
        })
    })
}
fn pwa_sub(a: &Pwa, b: &Pwa) -> Option<Pwa> {
    pwa_zip(a, b, |x, y| {
        Some(Aff {
            a0: x.a0.checked_sub(y.a0)?,
            a1: x.a1.checked_sub(y.a1)?,
        })
    })
}
fn pwa_neg(a: &Pwa) -> Pwa {
    let pieces = a
        .pieces
        .iter()
        .map(|p| Aff {
            a0: -p.a0,
            a1: -p.a1,
        })
        .collect();
    Pwa {
        cuts: a.cuts.clone(),
        pieces,
    }
}
fn pwa_add_const(a: &Pwa, c: i128) -> Pwa {
    let pieces = a
        .pieces
        .iter()
        .map(|p| Aff {
            a0: p.a0 + c,
            a1: p.a1,
        })
        .collect();
    Pwa {
        cuts: a.cuts.clone(),
        pieces,
    }
}

/// Generic combiner for ops whose result, on each maximal linear region, is one
/// of the two operand pieces (min/max) or a constant 0/1 (comparisons): refine
/// to the union cut set, split each cell at the integer crossing of `(a - b)`
/// (so no subcell straddles it), and on each subcell call `piece` with the two
/// operand affines and the subcell's representative `x`. `None` on overflow.
fn pwa_piecewise(a: &Pwa, b: &Pwa, piece: impl Fn(Aff, Aff, i128) -> Aff) -> Option<Pwa> {
    let base_cuts = merge_cuts(&a.cuts, &b.cuts);
    let ra0 = refine(a, &base_cuts);
    let rb0 = refine(b, &base_cuts);

    // Split each base cell at the integer crossing of (a - b). Checked
    // subtraction: an overflow (unreachable for a compilable contract, whose
    // magnitudes the interval engine bounds to M) forces a sound abstain rather
    // than a wrapped, possibly breakpoint-hiding cut.
    let mut all_cuts: BTreeSet<i128> = base_cuts.iter().copied().collect();
    for (pa, pb) in ra0.pieces.iter().zip(&rb0.pieces) {
        let c0 = pa.a0.checked_sub(pb.a0)?;
        let c1 = pa.a1.checked_sub(pb.a1)?;
        bracket_crossing(c0, c1, &mut all_cuts)?;
    }
    let cuts: Vec<i128> = all_cuts.into_iter().collect();
    let ra = refine(a, &cuts);
    let rb = refine(b, &cuts);
    let frame = Pwa {
        cuts: cuts.clone(),
        pieces: vec![Aff { a0: 0, a1: 0 }; cuts.len() + 1],
    };
    let mut pieces = Vec::with_capacity(cuts.len() + 1);
    for i in 0..(cuts.len() + 1) {
        let rep = frame.cell_rep(i);
        // ensure the operands evaluate (overflow -> abstain), then pick.
        ra.pieces[i].eval(rep)?;
        rb.pieces[i].eval(rep)?;
        pieces.push(piece(ra.pieces[i], rb.pieces[i], rep));
    }
    Some(normalize(Pwa { cuts, pieces }))
}

fn pwa_min(a: &Pwa, b: &Pwa) -> Option<Pwa> {
    pwa_piecewise(a, b, |pa, pb, rep| match (pa.eval(rep), pb.eval(rep)) {
        (Some(x), Some(y)) => {
            if x <= y {
                pa
            } else {
                pb
            }
        }
        _ => pa,
    })
}
fn pwa_max(a: &Pwa, b: &Pwa) -> Option<Pwa> {
    pwa_piecewise(a, b, |pa, pb, rep| match (pa.eval(rep), pb.eval(rep)) {
        (Some(x), Some(y)) => {
            if x >= y {
                pa
            } else {
                pb
            }
        }
        _ => pa,
    })
}

/// `a op b` as a 0/1-valued piecewise function (breakpoint where a-b crosses 0).
fn pwa_cmp(a: &Pwa, op: CmpOp, b: &Pwa) -> Option<Pwa> {
    pwa_piecewise(a, b, move |pa, pb, rep| {
        let v = match (pa.eval(rep), pb.eval(rep)) {
            (Some(x), Some(y)) => cmp_val(x, op, y),
            _ => 0,
        };
        Aff { a0: v, a1: 0 }
    })
}

/// `select(cond, t, f)`: `cond` is a 0/1 function whose breakpoints are cuts, so
/// within each cell it is constant -- pick `t`'s or `f`'s piece accordingly.
fn pwa_select(cond: &Pwa, t: &Pwa, f: &Pwa) -> Option<Pwa> {
    let cuts = merge_cuts(&merge_cuts(&cond.cuts, &t.cuts), &f.cuts);
    let rc = refine(cond, &cuts);
    let rt = refine(t, &cuts);
    let rf = refine(f, &cuts);
    let frame = Pwa {
        cuts: cuts.clone(),
        pieces: vec![Aff { a0: 0, a1: 0 }; cuts.len() + 1],
    };
    let mut pieces = Vec::with_capacity(cuts.len() + 1);
    for i in 0..(cuts.len() + 1) {
        let rep = frame.cell_rep(i);
        let c = rc.pieces[i].eval(rep)?;
        pieces.push(if c != 0 { rt.pieces[i] } else { rf.pieces[i] });
    }
    Some(normalize(Pwa { cuts, pieces }))
}

fn cmp_val(x: i128, op: CmpOp, y: i128) -> i128 {
    let b = match op {
        CmpOp::Eq => x == y,
        CmpOp::Ne => x != y,
        CmpOp::Lt => x < y,
        CmpOp::Le => x <= y,
        CmpOp::Gt => x > y,
        CmpOp::Ge => x >= y,
    };
    b as i128
}

enum CmpKind {
    EqZero,
    NeZero,
}
/// `x == 0` / `x != 0` (OP_NOT / OP_0NOTEQUAL) as a 0/1 function.
fn pwa_cmp_const(a: &Pwa, kind: CmpKind) -> Option<Pwa> {
    let op = match kind {
        CmpKind::EqZero => CmpOp::Eq,
        CmpKind::NeZero => CmpOp::Ne,
    };
    pwa_cmp(a, op, &Pwa::constant(0))
}

/// `abs(x)`: split each cell at its sign change.
fn pwa_abs(a: &Pwa) -> Option<Pwa> {
    let mut all_cuts: BTreeSet<i128> = a.cuts.iter().copied().collect();
    for p in &a.pieces {
        bracket_crossing(p.a0, p.a1, &mut all_cuts)?;
    }
    let cuts: Vec<i128> = all_cuts.into_iter().collect();
    let ra = refine(a, &cuts);
    let frame = Pwa {
        cuts: cuts.clone(),
        pieces: vec![Aff { a0: 0, a1: 0 }; cuts.len() + 1],
    };
    let mut pieces = Vec::with_capacity(cuts.len() + 1);
    for i in 0..(cuts.len() + 1) {
        let rep = frame.cell_rep(i);
        let p = ra.pieces[i];
        let v = p.eval(rep)?;
        pieces.push(if v < 0 {
            Aff {
                a0: -p.a0,
                a1: -p.a1,
            }
        } else {
            p
        });
    }
    Some(normalize(Pwa { cuts, pieces }))
}

/// Drop a cut whose two adjacent pieces are identical (keeps representations
/// small; purely cosmetic for soundness, but bounds growth).
fn normalize(p: Pwa) -> Pwa {
    if p.cuts.is_empty() {
        return p;
    }
    let mut cuts = Vec::with_capacity(p.cuts.len());
    let mut pieces = Vec::with_capacity(p.pieces.len());
    pieces.push(p.pieces[0]);
    for i in 0..p.cuts.len() {
        let prev = *pieces.last().unwrap();
        let next = p.pieces[i + 1];
        if prev.a0 == next.a0 && prev.a1 == next.a1 {
            continue; // same affine across the cut: redundant
        }
        cuts.push(p.cuts[i]);
        pieces.push(next);
    }
    Pwa { cuts, pieces }
}

// --- byte decoding helpers (copied from interp.rs to keep this an independent
// oracle; semantics must match byte-for-byte) ---

fn push_len(op: u8, script: &[u8], i: &mut usize) -> Option<Option<usize>> {
    match op {
        0x01..=0x4b => Some(Some(op as usize)),
        0x4c => {
            let n = *script.get(*i)? as usize;
            *i += 1;
            Some(Some(n))
        }
        0x4d => {
            let lo = *script.get(*i)? as usize;
            let hi = *script.get(*i + 1)? as usize;
            *i += 2;
            Some(Some(lo | (hi << 8)))
        }
        // not a push opcode
        _ => Some(None),
    }
}

fn small_push(op: u8) -> Option<Vec<u8>> {
    match op {
        0x00 => Some(Vec::new()),
        0x4f => Some(vec![0x81]),
        0x51..=0x60 => Some(vec![op - 0x50]),
        _ => None,
    }
}

/// CScriptNum decode (LE sign-magnitude), minimality enforced -- identical to
/// `interp::decode_minimal`.
fn decode_minimal(v: &[u8]) -> Result<i64, ()> {
    if v.is_empty() {
        return Ok(0);
    }
    if v.len() > 5 {
        return Err(()); // beyond any CScriptNum operand; also keeps shifts < 64
    }
    let last = v[v.len() - 1];
    if last & 0x7f == 0 && (v.len() == 1 || (v[v.len() - 2] & 0x80) == 0) {
        return Err(());
    }
    let mut result: i64 = 0;
    for (i, &b) in v.iter().enumerate() {
        result |= (b as i64) << (8 * i);
    }
    if last & 0x80 != 0 {
        let sign_bit = 0x80i64 << (8 * (v.len() - 1));
        return Ok(-(result & !sign_bit));
    }
    Ok(result)
}

// =============================================================================
// Engine A_n: n DECOUPLED Int witness variables (the decoupled grid).
//
// The 2-variable case, generalized to any `n` (the "n Int + cell cap" phase).
// Generalizes Engine A's 1-D breakpoint+re-execute to
// an n-D GRID arrangement, restricted to the case where every affine atom
// involves exactly ONE of the `n` variables (axis-aligned, "decoupled"). Then the
// arrangement of all atom-hyperplanes is a GRID (each hyperplane is `x_i = c`, an
// axis-aligned cut), and a SOUND cover is the PRODUCT of `n` independent Engine-A
// covers: the Cartesian product of `covering_points(cuts_i)`, re-executed
// three-way. No lattice search -- the 1-D completeness argument applies on each
// axis independently, and every integer point of every grid cell (and every
// integer-containing face) is hit because each axis's cover hits every 1-D cell
// AND every breakpoint and `±1`. The thin-band unsoundness cannot arise: there
// are NO diagonal hyperplanes, so a cell's lattice points are never confined to a
// non-representative coordinate.
//
// The ONLY new machinery over Engine A is an AXIS TAG on each symbolic numeric
// value (`Const` or `Var(i)`) and a guard that ABSTAINS on any binary op that
// would combine two DIFFERENT variables (a diagonal/coupling atom like `x_i <
// x_j` or `x_i + x_j < k`). Within a single axis the entire piecewise-affine
// `Pwa` algebra is reused VERBATIM (a `Var(i)` value's `pwa.cuts` are the cuts of
// axis `i`). The guard licenses treating the axes independently; it is
// conservative -- any doubt -> `None` -> abstain -> `Unbounded` (safe;
// under-approximation never loses money, only a false `Proven` does). Coupled
// contracts stay `Unbounded` until the full CAD-with-lattice phase.
//
// Soundness rests on (re-execution anchor + grid completeness), exactly as Engine
// A: re-executing the ACTUAL naive/opt bytes and the predicate at each grid point
// is what decides agreement; the arrangement math only chooses WHERE to sample.
// Because no atom couples the axes (every cross-axis op abstains), the
// accept-function is SEPARABLE -- `accept(x) = C . Π_i F_i(x_i)` -- so `F_i`'s
// breakpoints are exactly `live[i].cuts`, and the grid of the `n` 1-D covers is
// complete. The exponential blow-up of the product is bounded by a CELL CAP:
// over the cap -> abstain -> `Unbounded` (graceful degradation, §3.6). The
// reduced-domain exhaustive gate validates completeness on n-D boxes (n = 2, 3).

/// Per-slice grid cap: abstain if a single slice's n-D grid exceeds this (safe ->
/// `Unbounded`). Real decoupled contracts have a handful of cuts per axis.
const MAX_GRID_N: usize = 1 << 16;
/// Cumulative grid-point budget across all slices, bounding total re-executions
/// per `try_prove` call. Over the budget -> abstain (safe). A pathological input
/// (many axes / many cuts) degrades gracefully; real contracts are orders of
/// magnitude under it.
const MAX_TOTAL_GRID_N: u128 = 1 << 16;
/// A sanity cap on the number of Int witness variables. Beyond this the grid cap
/// would abstain anyway; this bounds the per-point plan/mixed-radix work first.
const MAX_INT_VARS: usize = 8;

/// The axis a symbolic numeric value depends on. `Const` is independent of every
/// variable (a literal, a fixed param's bytes, a CHECKSIG result in this slice);
/// `Var(i)` depends on exactly variable `i`. The decoupled grid is sound
/// precisely while no value is ever a function of two DIFFERENT variables.
#[derive(Clone, Copy, PartialEq, Eq)]
enum AxisN {
    Const,
    Var(u32),
}

/// Combine the axes of two operands of a binary numeric op. `Const` is the
/// identity; the SAME variable is closed; two DIFFERENT variables form a DIAGONAL
/// (a coupling atom) and return `None` so the executor abstains -- the
/// conservative guard that keeps the grid decomposition sound.
fn combine_axis(a: AxisN, b: AxisN) -> Option<AxisN> {
    use AxisN::{Const, Var};
    match (a, b) {
        (Const, x) | (x, Const) => Some(x),
        (Var(i), Var(j)) if i == j => Some(Var(i)),
        (Var(_), Var(_)) => None,
    }
}

/// A symbolic stack value during decoupled n-`x` execution: an axis-tagged
/// piecewise-affine CScriptNum (`Num`), or concrete bytes (`Bytes`). Mirrors the
/// 1-D `SymVal`, with the axis tag the only addition.
#[derive(Clone, PartialEq)]
enum SymValN {
    Num { pwa: Pwa, axis: AxisN },
    Bytes(Vec<u8>),
}

/// An open `OP_IF`/`OP_NOTIF` frame during decoupled execution. Both arms are
/// executed symbolically and merged at `OP_ENDIF` (a per-slot `pwa_select` on the
/// guard, or a static pick when the guard is constant). The guard is kept as a
/// `Pwa` (always 0/1-valued -- a non-bool guard would risk a MINIMALIF abort whose
/// breakpoints we could miss, so the executor abstains on one).
struct IfFrameN {
    guard_pwa: Pwa,
    guard_axis: AxisN,
    negated: bool,
    saved: Vec<SymValN>,
    then_done: Option<Vec<SymValN>>,
}

/// True iff the piecewise function is 0/1-valued everywhere (each piece a constant
/// in `{0, 1}`). Such a value is always minimally encoded (`{}` / `{0x01}`), so it
/// never triggers a MINIMALIF abort when consumed by `OP_IF` -- the precondition
/// that lets the executor model a branch without tracking an abort domain.
fn is_bool_pwa(p: &Pwa) -> bool {
    p.pieces
        .iter()
        .all(|pc| pc.a1 == 0 && (pc.a0 == 0 || pc.a0 == 1))
}

/// Coerce a symbolic value to an axis-tagged `Pwa`. Concrete bytes decode to a
/// `Const`. `None` if the bytes are not a valid <=4-byte minimal number.
fn to_num_n(v: SymValN) -> Option<(Pwa, AxisN)> {
    match v {
        SymValN::Num { pwa, axis } => Some((pwa, axis)),
        SymValN::Bytes(b) => {
            if b.len() > 4 {
                return None;
            }
            Some((
                Pwa::constant(decode_minimal(&b).ok()? as i128),
                AxisN::Const,
            ))
        }
    }
}

fn to_bytes_n(v: SymValN) -> Option<Vec<u8>> {
    match v {
        SymValN::Bytes(b) => Some(b),
        SymValN::Num { .. } => None,
    }
}

/// A concrete numeric value from a symbolic value (only when constant in EVERY
/// variable); used for PICK/ROLL depths. A genuinely-constant `Pwa` qualifies on
/// any axis.
fn as_const_num_n(v: &SymValN) -> Option<i64> {
    match v {
        SymValN::Bytes(b) => decode_minimal(b).ok(),
        SymValN::Num { pwa, .. } => pwa.as_constant().and_then(|c| i64::try_from(c).ok()),
    }
}

/// `truthy(v)` (CastToBool) as a 0/1 `Pwa`: 1 where `a != 0`. PROPAGATES an
/// overflow `None` (abstain) instead of swallowing it -- silently returning a
/// constant 0 would DROP a breakpoint and could hide a script/predicate
/// divergence (a false proof), so abstaining is the only sound response. Overflow
/// is unreachable for a compilable contract (the interval engine bounds every
/// magnitude to M), so this never abstains in practice. Used by BOTH engines.
fn pwa_truthy_strict(a: &Pwa) -> Option<Pwa> {
    pwa_cmp(a, CmpOp::Ne, &Pwa::constant(0))
}

fn total_cuts_n(stack: &[SymValN], live: &[Pwa]) -> usize {
    live.iter().map(|p| p.cuts.len()).sum::<usize>()
        + stack
            .iter()
            .map(|v| match v {
                SymValN::Num { pwa, .. } => pwa.cuts.len(),
                SymValN::Bytes(_) => 0,
            })
            .sum::<usize>()
}

/// Symbolically execute a straight-line (no-branch) decoupled-affine script over
/// the `n_vars` variables (axes `Var(0)..Var(n-1)`), returning the per-axis
/// accept-functions `live[i]`: 0/1 piecewise functions whose cuts are the
/// breakpoints of axis `i` in the script's accept-function. Because every binary
/// op abstains on a cross-axis combine, the accept is separable
/// `C . Π_i live[i](x_i)`, so each `live[i]` carries the complete breakpoint set
/// for axis `i`. `None` on any opcode outside the modeled fragment, a coupling
/// atom, a stack/type error, or a cut-count blowup -- all of which make the engine
/// abstain (sound).
fn sym_accept_n(
    script: &[u8],
    init: Vec<SymValN>,
    ctx: &Context,
    n_vars: usize,
) -> Option<Vec<Pwa>> {
    let mut stack = init;
    // The accept is `(Π_i live[i](x_i)) AND (any const conjunct)`; each
    // VERIFY/...VERIFY/top condition folds into the axis it belongs to. A const
    // condition contributes no cut (its truth is decided by re-execution), so it
    // is not folded -- the cut superset is unaffected and re-execution anchors it.
    let mut live: Vec<Pwa> = vec![Pwa::constant(1); n_vars];
    // Open OP_IF/OP_NOTIF frames (Phase 3 branching). A branch over an affine
    // guard is another cutting hyperplane: both arms execute symbolically and
    // merge at ENDIF. `in_branch` (frames non-empty) forbids a conditional abort
    // (a VERIFY-family op inside a branch), which is not modeled.
    let mut frames: Vec<IfFrameN> = Vec::new();
    let mut i = 0usize;

    // Fold a 0/1 `Pwa` into the live function of its axis (no-op for `Const`).
    let fold = |live: &mut [Pwa], axis: AxisN, t: &Pwa| -> Option<()> {
        if let AxisN::Var(v) = axis {
            let slot = &mut live[v as usize];
            *slot = pwa_min(slot, t)?;
        }
        Some(())
    };

    while i < script.len() {
        let op = script[i];
        i += 1;

        // Pushes (identical shape to sym_accept).
        if op == 0x4e {
            return None; // PUSHDATA4
        }
        if let Some(len) = push_len(op, script, &mut i)? {
            let end = i.checked_add(len)?;
            if end > script.len() {
                return None;
            }
            stack.push(SymValN::Bytes(script[i..end].to_vec()));
            i = end;
            continue;
        }
        if let Some(v) = small_push(op) {
            stack.push(SymValN::Bytes(v));
            continue;
        }

        match op {
            // --- branching: OP_IF / OP_NOTIF / OP_ELSE / OP_ENDIF ---
            0x63 | 0x64 => {
                // Pop the guard. It MUST be 0/1-valued (a comparison/bool result):
                // a non-bool value risks a MINIMALIF abort whose breakpoints we
                // cannot see here, so we abstain. The guard's flip points become
                // cuts of the merged value at ENDIF (via pwa_select).
                let (g_pwa, g_axis) = to_num_n(stack.pop()?)?;
                if !is_bool_pwa(&g_pwa) {
                    return None;
                }
                frames.push(IfFrameN {
                    guard_pwa: g_pwa,
                    guard_axis: g_axis,
                    negated: op == 0x64,
                    saved: stack.clone(),
                    then_done: None,
                });
            }
            0x67 => {
                // OP_ELSE: stash the then-branch result, restore the pre-IF stack.
                let f = frames.last_mut()?;
                if f.then_done.is_some() {
                    return None; // a second ELSE in one frame
                }
                let saved = f.saved.clone();
                f.then_done = Some(std::mem::replace(&mut stack, saved));
            }
            0x68 => {
                // OP_ENDIF: merge the two arms. Both must leave the SAME stack depth.
                let f = frames.pop()?;
                let (then_s, else_s) = match f.then_done {
                    Some(t) => (t, std::mem::take(&mut stack)),
                    None => (std::mem::take(&mut stack), f.saved.clone()),
                };
                if then_s.len() != else_s.len() {
                    return None;
                }
                stack = if let Some(c) = f.guard_pwa.as_constant() {
                    // Static guard: the branch is decided -- keep the taken arm
                    // wholesale (no select, no axis coupling).
                    let take_then = if f.negated { c == 0 } else { c != 0 };
                    if take_then { then_s } else { else_s }
                } else {
                    // Dynamic guard (axis `Var(i)`): merge each slot via pwa_select.
                    // Unchanged slots are kept as-is (structural equality), which is
                    // essential: an untouched value on a DIFFERENT axis must not be
                    // forced through a cross-axis select and wrongly abstain.
                    let mut merged = Vec::with_capacity(then_s.len());
                    for (t, e) in then_s.into_iter().zip(else_s) {
                        if t == e {
                            merged.push(t);
                            continue;
                        }
                        let (t_pwa, t_ax) = to_num_n(t)?;
                        let (e_pwa, e_ax) = to_num_n(e)?;
                        let axis = combine_axis(combine_axis(f.guard_axis, t_ax)?, e_ax)?;
                        // `pwa_select(cond, a, b)` = cond?a:b. For OP_IF the THEN arm
                        // runs when the guard is truthy; for OP_NOTIF when falsy.
                        let mp = if f.negated {
                            pwa_select(&f.guard_pwa, &e_pwa, &t_pwa)?
                        } else {
                            pwa_select(&f.guard_pwa, &t_pwa, &e_pwa)?
                        };
                        merged.push(SymValN::Num { pwa: mp, axis });
                    }
                    merged
                };
            }
            // --- stack ops (axis-agnostic; values move unchanged) ---
            0x75 => {
                stack.pop()?; // DROP
            }
            0x6d => {
                stack.pop()?;
                stack.pop()?; // 2DROP
            }
            0x76 => {
                let t = stack.last()?.clone(); // DUP
                stack.push(t);
            }
            0x77 => {
                let n = stack.len();
                if n < 2 {
                    return None;
                }
                stack.remove(n - 2); // NIP
            }
            0x78 => {
                let n = stack.len();
                if n < 2 {
                    return None;
                }
                stack.push(stack[n - 2].clone()); // OVER
            }
            0x7c => {
                let n = stack.len();
                if n < 2 {
                    return None;
                }
                stack.swap(n - 1, n - 2); // SWAP
            }
            0x7d => {
                let n = stack.len();
                if n < 2 {
                    return None;
                }
                let t = stack[n - 1].clone();
                stack.insert(n - 2, t); // TUCK
            }
            0x79 | 0x7a => {
                // PICK/ROLL with a CONSTANT depth (the only kind the compiler emits).
                let d = as_const_num_n(&stack.pop()?)?;
                if d < 0 || d as usize >= stack.len() {
                    return None;
                }
                let idx = stack.len() - 1 - d as usize;
                if op == 0x79 {
                    stack.push(stack[idx].clone()); // PICK: copy
                } else {
                    let v = stack.remove(idx); // ROLL: move
                    stack.push(v);
                }
            }
            // --- VERIFY: fold the condition into its axis's live ---
            0x69 => {
                if !frames.is_empty() {
                    return None; // conditional VERIFY (abort inside a branch): not modeled
                }
                let (c, axis) = to_num_n(stack.pop()?)?;
                let t = pwa_truthy_strict(&c)?;
                fold(&mut live, axis, &t)?;
            }
            // --- unary numeric (axis preserved) ---
            0x8b | 0x8c | 0x8f | 0x90 | 0x91 | 0x92 => {
                let (x, axis) = to_num_n(stack.pop()?)?;
                let r = match op {
                    0x8b => pwa_add_const(&x, 1),
                    0x8c => pwa_add_const(&x, -1),
                    0x8f => pwa_neg(&x),
                    0x90 => pwa_abs(&x)?,
                    0x91 => pwa_cmp_const(&x, CmpKind::EqZero)?,
                    _ => pwa_cmp_const(&x, CmpKind::NeZero)?, // 0x92
                };
                stack.push(SymValN::Num { pwa: r, axis });
            }
            // --- binary numeric (axes combined; cross-axis abstains) ---
            0x93 | 0x94 | 0x9a | 0x9b | 0x9c | 0x9e | 0x9f | 0xa0 | 0xa1 | 0xa2 | 0xa3 | 0xa4 => {
                let (b, ax_b) = to_num_n(stack.pop()?)?;
                let (a, ax_a) = to_num_n(stack.pop()?)?;
                let axis = combine_axis(ax_a, ax_b)?;
                let r = match op {
                    0x93 => pwa_add(&a, &b)?,
                    0x94 => pwa_sub(&a, &b)?,
                    0x9a => pwa_min(&pwa_truthy_strict(&a)?, &pwa_truthy_strict(&b)?)?, // BOOLAND
                    0x9b => pwa_max(&pwa_truthy_strict(&a)?, &pwa_truthy_strict(&b)?)?, // BOOLOR
                    0x9c => pwa_cmp(&a, CmpOp::Eq, &b)?,
                    0x9e => pwa_cmp(&a, CmpOp::Ne, &b)?,
                    0x9f => pwa_cmp(&a, CmpOp::Lt, &b)?,
                    0xa0 => pwa_cmp(&a, CmpOp::Gt, &b)?,
                    0xa1 => pwa_cmp(&a, CmpOp::Le, &b)?,
                    0xa2 => pwa_cmp(&a, CmpOp::Ge, &b)?,
                    0xa3 => pwa_min(&a, &b)?,
                    _ => pwa_max(&a, &b)?, // 0xa4 MAX
                };
                stack.push(SymValN::Num { pwa: r, axis });
            }
            0x9d => {
                // NUMEQUALVERIFY: fold the equality into its (combined) axis's live.
                if !frames.is_empty() {
                    return None; // conditional NUMEQUALVERIFY abort: not modeled
                }
                let (b, ax_b) = to_num_n(stack.pop()?)?;
                let (a, ax_a) = to_num_n(stack.pop()?)?;
                let axis = combine_axis(ax_a, ax_b)?;
                let eq = pwa_cmp(&a, CmpOp::Eq, &b)?;
                fold(&mut live, axis, &eq)?;
            }
            0xa5 => {
                // WITHIN: x in [lo, hi). All three operands must share one axis.
                let (hi, ax_hi) = to_num_n(stack.pop()?)?;
                let (lo, ax_lo) = to_num_n(stack.pop()?)?;
                let (x, ax_x) = to_num_n(stack.pop()?)?;
                let axis = combine_axis(combine_axis(ax_x, ax_lo)?, ax_hi)?;
                let ge = pwa_cmp(&x, CmpOp::Ge, &lo)?;
                let lt = pwa_cmp(&x, CmpOp::Lt, &hi)?;
                stack.push(SymValN::Num {
                    pwa: pwa_min(&ge, &lt)?,
                    axis,
                });
            }
            // CHECKSIG/CHECKSIGVERIFY: sig+key concrete in this slice -> Const.
            0xac | 0xad => {
                if op == 0xad && !frames.is_empty() {
                    return None; // conditional CHECKSIGVERIFY abort: not modeled
                }
                let pubkey = to_bytes_n(stack.pop()?)?;
                let sig = to_bytes_n(stack.pop()?)?;
                let ok = check_sig_const(&sig, &pubkey, ctx)?;
                if op == 0xac {
                    stack.push(SymValN::Num {
                        pwa: Pwa::constant(ok as i128),
                        axis: AxisN::Const,
                    });
                }
                // 0xad CHECKSIGVERIFY: a constant guard -- no cut to fold; whether
                // it passed is decided by re-execution at the grid points.
            }
            0xba => {
                // CHECKSIGADD: n + (1|0); axis of n preserved.
                let pubkey = to_bytes_n(stack.pop()?)?;
                let (n, axis) = to_num_n(stack.pop()?)?;
                let sig = to_bytes_n(stack.pop()?)?;
                let ok = check_sig_const(&sig, &pubkey, ctx)?;
                stack.push(SymValN::Num {
                    pwa: pwa_add_const(&n, ok as i128),
                    axis,
                });
            }
            // Everything else (EQUAL, SIZE, hashes, CLTV/CSV, ...) is outside the
            // engine's fragment: abstain.
            _ => return None,
        }
        if total_cuts_n(&stack, &live) > MAX_CUTS {
            return None;
        }
    }

    // Tail CLEANSTACK: balanced branches, exactly one element; fold `truthy(top)`.
    if !frames.is_empty() || stack.len() != 1 {
        return None;
    }
    let (top, axis) = to_num_n(stack.pop()?)?;
    if let AxisN::Var(_) = axis {
        let t = pwa_truthy_strict(&top)?;
        fold(&mut live, axis, &t)?;
    }
    Some(live)
}

/// Build the symbolic initial stack for a slice (each int-var slot is the
/// identity function of its axis; every other slot is its concrete bytes) and
/// symbolically execute `leaf`, inserting its per-axis breakpoints into
/// `cuts[i]`. `names[i]` is the witness name of variable `i`. `None` (abstain) on
/// any construct outside the decoupled no-branch affine fragment.
#[allow(clippy::too_many_arguments)]
fn collect_script_breakpoints_n(
    leaf: &LoweredLeaf,
    sig: &SpendSig,
    env: &Env,
    names: &[String],
    fixed: &[(String, SatValue)],
    marker: &[u8],
    ctx: &Context,
    cuts: &mut [BTreeSet<i128>],
) -> Option<()> {
    let zeros = vec![0i128; names.len()];
    let dummy = full_plan_n(names, &zeros, fixed);
    let stack0 = build_witness(leaf, sig, env, &dummy, marker).ok()?;

    // Map each witness-stack slot to the var (if any) it carries.
    let mut axis_of: Vec<Option<u32>> = vec![None; stack0.len()];
    for (vi, nm) in names.iter().enumerate() {
        let pos = leaf.witness_order.iter().position(|n| n == nm)?;
        if pos >= stack0.len() {
            return None;
        }
        axis_of[pos] = Some(vi as u32);
    }

    let init: Vec<SymValN> = stack0
        .iter()
        .enumerate()
        .map(|(i, b)| match axis_of[i] {
            Some(vi) => SymValN::Num {
                pwa: Pwa::identity(),
                axis: AxisN::Var(vi),
            },
            None => SymValN::Bytes(b.clone()),
        })
        .collect();

    let live = sym_accept_n(&leaf.script, init, ctx, names.len())?;
    for (i, lv) in live.iter().enumerate() {
        for &c in &lv.cuts {
            cuts[i].insert(c);
        }
    }
    Some(())
}

/// The full witness plan for a slice: each var `names[i]` set to `vals[i]`, the
/// others to their fixed slice values.
fn full_plan_n(
    names: &[String],
    vals: &[i128],
    fixed: &[(String, SatValue)],
) -> Vec<(String, SatValue)> {
    let mut plan = Vec::with_capacity(fixed.len() + names.len());
    for (nm, &v) in names.iter().zip(vals) {
        plan.push((nm.clone(), SatValue::Int(v as i64)));
    }
    plan.extend(fixed.iter().cloned());
    plan
}

/// Abstain unless NONE of the variables `names` appears anywhere in `e`.
fn guard_no_vars(e: &Expr, names: &[String]) -> Option<()> {
    if names.iter().any(|nm| mentions(e, nm)) {
        None
    } else {
        Some(())
    }
}

/// Collect a superset of the source predicate's per-axis breakpoints, mirroring
/// `collect_pred_breakpoints` but axis-tagged. Each require item is evaluated to
/// an axis-tagged `Pwa`; a `Var(i)` item's cuts go to `cuts[i]`, a `Const` item's
/// nowhere. `None` (abstain) on a coupling atom or any construct outside the
/// modeled fragment.
fn collect_pred_breakpoints_n(
    body: &[Stmt],
    env: &Env,
    names: &[String],
    cuts: &mut [BTreeSet<i128>],
) -> Option<()> {
    let mut scope: Vec<(String, (Pwa, AxisN))> = Vec::new();
    for stmt in body {
        match stmt {
            Stmt::Let { name, value, .. } => {
                let v = pred_axis_n(value, &scope, env, names)?;
                scope.push((name.text.clone(), v));
            }
            Stmt::Require(req) => {
                for item in &req.items {
                    if is_call(item, "after") {
                        guard_no_vars(item, names)?;
                        continue;
                    }
                    let (p, ax) = pred_axis_n(item, &scope, env, names)?;
                    if let AxisN::Var(v) = ax {
                        for &c in &p.cuts {
                            cuts[v as usize].insert(c);
                        }
                    }
                    // Bound the accumulated cut set, mirroring the script side's
                    // MAX_CUTS guard, so a pathological predicate cannot grow it
                    // without limit (real predicates have far fewer cuts).
                    if cuts.iter().map(|c| c.len()).sum::<usize>() > MAX_CUTS {
                        return None;
                    }
                }
            }
        }
    }
    Some(())
}

/// Evaluate a predicate expression to an axis-tagged piecewise-affine function of
/// the variables `names`. Mirrors `pred_pwa`, threading the axis through every
/// combinator and abstaining (`None`) on any cross-axis coupling. Opaque booleans
/// (`k.check`) are the constant `1` on axis `Const`, exactly as the 1-D side.
fn pred_axis_n(
    e: &Expr,
    scope: &[(String, (Pwa, AxisN))],
    env: &Env,
    names: &[String],
) -> Option<(Pwa, AxisN)> {
    match e {
        Expr::Int { text, .. } => Some((Pwa::constant(parse_int(text)?), AxisN::Const)),
        Expr::Bool { value, .. } => Some((Pwa::constant(*value as i128), AxisN::Const)),
        Expr::Name(id) if names.iter().any(|nm| nm == &id.text) => {
            let vi = names.iter().position(|nm| nm == &id.text).unwrap();
            Some((Pwa::identity(), AxisN::Var(vi as u32)))
        }
        Expr::Name(id) => {
            if let Some((_, v)) = scope.iter().rev().find(|(n, _)| *n == id.text) {
                return Some(v.clone());
            }
            match env.get(&id.text) {
                Some(ConstValue::Int(n)) => Some((Pwa::constant(*n), AxisN::Const)),
                Some(ConstValue::Bool(b)) => Some((Pwa::constant(*b as i128), AxisN::Const)),
                _ => None,
            }
        }
        Expr::Unary {
            op: UnaryOp::Neg,
            operand,
            ..
        } => {
            let (p, ax) = pred_axis_n(operand, scope, env, names)?;
            Some((pwa_neg(&p), ax))
        }
        Expr::Unary {
            op: UnaryOp::Not,
            operand,
            ..
        } => {
            let (p, ax) = pred_axis_n(operand, scope, env, names)?;
            Some((pwa_cmp(&p, CmpOp::Eq, &Pwa::constant(0))?, ax))
        }
        Expr::Binary { op, lhs, rhs, .. } => {
            let (a, ax_a) = pred_axis_n(lhs, scope, env, names)?;
            let (b, ax_b) = pred_axis_n(rhs, scope, env, names)?;
            let axis = combine_axis(ax_a, ax_b)?;
            let r = match op {
                BinaryOp::Add => pwa_add(&a, &b)?,
                BinaryOp::Sub => pwa_sub(&a, &b)?,
            };
            Some((r, axis))
        }
        Expr::Compare { first, rest, .. } => {
            let mut acc = Pwa::constant(1);
            let mut acc_axis = AxisN::Const;
            let (mut pv, mut pax) = pred_axis_n(first, scope, env, names)?;
            for (op, next) in rest {
                let (nv, nax) = pred_axis_n(next, scope, env, names)?;
                let cmp_axis = combine_axis(pax, nax)?;
                let c = pwa_cmp(&pv, *op, &nv)?;
                acc_axis = combine_axis(acc_axis, cmp_axis)?;
                acc = pwa_min(&acc, &c)?;
                pv = nv;
                pax = nax;
            }
            Some((acc, acc_axis))
        }
        Expr::In {
            value,
            lo,
            hi,
            inclusive,
            ..
        } => {
            let (v, ax_v) = pred_axis_n(value, scope, env, names)?;
            let (lo_p, ax_lo) = pred_axis_n(lo, scope, env, names)?;
            let (hi_p, ax_hi) = pred_axis_n(hi, scope, env, names)?;
            let axis = combine_axis(combine_axis(ax_v, ax_lo)?, ax_hi)?;
            let ge = pwa_cmp(&v, CmpOp::Ge, &lo_p)?;
            let up = if *inclusive { CmpOp::Le } else { CmpOp::Lt };
            let hic = pwa_cmp(&v, up, &hi_p)?;
            Some((pwa_min(&ge, &hic)?, axis))
        }
        Expr::Call { callee, args, .. } => {
            if let Expr::Member { member, .. } = callee.as_ref() {
                if member.text == "check" {
                    for a in args {
                        guard_no_vars(&a.value, names)?;
                    }
                    return Some((Pwa::constant(1), AxisN::Const));
                }
                guard_no_vars(e, names)?;
                return Some((Pwa::constant(1), AxisN::Const));
            }
            let Expr::Name(f) = callee.as_ref() else {
                guard_no_vars(e, names)?;
                return None;
            };
            match (f.text.as_str(), args.len()) {
                ("min", 2) => {
                    let (x, ax) = pred_axis_n(&args[0].value, scope, env, names)?;
                    let (y, ay) = pred_axis_n(&args[1].value, scope, env, names)?;
                    Some((pwa_min(&x, &y)?, combine_axis(ax, ay)?))
                }
                ("max", 2) => {
                    let (x, ax) = pred_axis_n(&args[0].value, scope, env, names)?;
                    let (y, ay) = pred_axis_n(&args[1].value, scope, env, names)?;
                    Some((pwa_max(&x, &y)?, combine_axis(ax, ay)?))
                }
                ("abs", 1) => {
                    let (x, ax) = pred_axis_n(&args[0].value, scope, env, names)?;
                    Some((pwa_abs(&x)?, ax))
                }
                ("int", 1) => pred_axis_n(&args[0].value, scope, env, names),
                ("select", 3) => {
                    let (cc, ac) = pred_axis_n(&args[0].value, scope, env, names)?;
                    let (tt, at) = pred_axis_n(&args[1].value, scope, env, names)?;
                    let (ff, af) = pred_axis_n(&args[2].value, scope, env, names)?;
                    // Static guard (e.g. a fixed Bool slice value): the result is
                    // exactly one branch, on its own axis -- no cross-axis coupling.
                    // Mirrors the script side's static branch pick at ENDIF.
                    if let Some(c) = cc.as_constant() {
                        return Some(if c != 0 { (tt, at) } else { (ff, af) });
                    }
                    let axis = combine_axis(combine_axis(ac, at)?, af)?;
                    Some((pwa_select(&cc, &tt, &ff)?, axis))
                }
                _ => {
                    guard_no_vars(e, names)?;
                    None
                }
            }
        }
        other => {
            guard_no_vars(other, names)?;
            None
        }
    }
}

/// Attempt a full-domain proof of a leaf with `n >= 2` scalar `Int` witness
/// parameters whose atoms are decoupled (each axis-aligned). The decoupled grid
/// (see the section banner): per slice of the other finite params, collect each
/// axis's breakpoints from naive, opt, AND the predicate; form the Cartesian
/// product cover; and re-execute all three at every grid point (with per-axis
/// out-of-`M` sentinels). The product is bounded by a cell cap (abstain over it).
/// Returns `Some(FullInt)` only on genuine agreement everywhere; `None` (abstain)
/// on any coupling, an unmodeled construct, or a cap overflow.
#[allow(clippy::too_many_arguments)]
fn engine_an(
    body: &[Stmt],
    sig: &SpendSig,
    env: &Env,
    naive: &LoweredLeaf,
    opt: &LoweredLeaf,
    marker: &[u8],
    ctx: &Context,
) -> Option<ProvenKind> {
    // n >= 2 scalar Int parameters (n == 1 is Engine A, n == 0 is Engine B), and
    // no Int hidden inside an array (that is a multi-variable-per-slot problem).
    let names: Vec<String> = sig
        .params
        .iter()
        .filter(|p| matches!(p.ty, Ty::Int))
        .map(|p| p.name.clone())
        .collect();
    let n = names.len();
    if !(2..=MAX_INT_VARS).contains(&n) {
        return None;
    }
    if sig.params.iter().any(|p| ty_has_array_int(&p.ty)) {
        return None;
    }

    // Finite domains for every OTHER parameter (each slice fixes them, leaving the
    // leaf a function of the n Int vars alone). Abstain if any is not finite.
    let mut other: Vec<(String, Vec<SatValue>)> = Vec::new();
    let mut slices: u128 = 1;
    for p in &sig.params {
        if names.iter().any(|nm| nm == &p.name) {
            continue;
        }
        let d = finite_domain(&p.ty, env)?;
        slices = slices.checked_mul(d.len() as u128)?;
        if slices > MAX_SLICES {
            return None;
        }
        other.push((p.name.clone(), d));
    }

    let mut cells_proven: usize = 0;
    let mut total_grid: u128 = 0;
    for s in 0..slices {
        // Decode `s` (mixed radix) into one concrete value per other parameter.
        let mut c = s;
        let mut fixed: Vec<(String, SatValue)> = Vec::with_capacity(other.len());
        for (name, dom) in &other {
            let idx = (c % dom.len() as u128) as usize;
            c /= dom.len() as u128;
            fixed.push((name.clone(), dom[idx].clone()));
        }

        // Per-axis breakpoint supersets from BOTH scripts AND the predicate, so
        // the grid common-refines all three: within each cell every program is
        // constant, so re-execution at one grid point per cell decides it.
        let mut cuts: Vec<BTreeSet<i128>> = vec![BTreeSet::new(); n];
        collect_script_breakpoints_n(naive, sig, env, &names, &fixed, marker, ctx, &mut cuts)?;
        collect_script_breakpoints_n(opt, sig, env, &names, &fixed, marker, ctx, &mut cuts)?;
        // The predicate side needs this slice's fixed scalar params (a Bool used
        // as a `select` guard, say) as consts -- the script side already bakes
        // them into the witness. Extend the env with them for this slice so
        // `pred_axis_n` can fold them, instead of abstaining on an unknown name.
        let mut slice_env = env.clone();
        for (name, sv) in &fixed {
            match sv {
                SatValue::Bool(b) => {
                    slice_env.insert(name.clone(), ConstValue::Bool(*b));
                }
                SatValue::Int(v) => {
                    slice_env.insert(name.clone(), ConstValue::Int(*v as i128));
                }
                _ => {} // Sig (only used in `check`) / Bytes / Array: not foldable
            }
        }
        collect_pred_breakpoints_n(body, &slice_env, &names, &mut cuts)?;

        // Per-axis 1-D covers; the grid is their Cartesian product. Cap the size.
        let covers: Vec<Vec<i128>> = cuts.iter().map(covering_points).collect();
        let mut grid: usize = 1;
        for cov in &covers {
            grid = grid.checked_mul(cov.len())?;
            if grid > MAX_GRID_N {
                return None;
            }
        }
        total_grid = total_grid.checked_add(grid as u128)?;
        if total_grid > MAX_TOTAL_GRID_N {
            return None;
        }
        cells_proven = cells_proven.saturating_add(grid);

        // Enumerate the n-D grid in mixed radix over the per-axis covers.
        let radix: Vec<usize> = covers.iter().map(|c| c.len()).collect();
        for g in 0..grid {
            let mut gg = g;
            let mut vals: Vec<i128> = Vec::with_capacity(n);
            let mut all_in_m = true;
            for (axis, cov) in covers.iter().enumerate() {
                let idx = gg % radix[axis];
                gg /= radix[axis];
                let v = cov[idx];
                if !(-MACHINE_MAX..=MACHINE_MAX).contains(&v) {
                    all_in_m = false;
                }
                vals.push(v);
            }
            let plan = full_plan_n(&names, &vals, &fixed);
            let naive_ok = run(naive, sig, env, &plan, marker, ctx)?;
            let opt_ok = run(opt, sig, env, &plan, marker, ctx)?;
            // T2: optimizer must match the naive lowering at every grid point.
            if naive_ok != opt_ok {
                return None;
            }
            if !all_in_m {
                // Out of the 4-byte CScriptNum domain on at least one axis: an
                // over-long operand is rejected by `num(v,4)` on the first numeric
                // op that consumes it, so BOTH scripts MUST reject. An acceptance
                // here breaks the model -> abstain.
                if naive_ok {
                    return None;
                }
                continue;
            }
            // T1: the independent predicate must match the naive script.
            match eval_predicate(body, &plan, env, ctx.verify_sig, marker, None) {
                Some(pred) if pred == naive_ok => {}
                _ => return None,
            }
        }
    }

    Some(ProvenKind::FullInt {
        var: names.join(","),
        breakpoints: cells_proven,
    })
}

// =============================================================================
// Engine B: structural symbolic equality for leaves with NO Int witness var.
//
// Decodes each script's bytes into a symbolic accept-function over OPAQUE atoms
// (one per witness slot -- a Bool pixel, a signature, ... -- treated as a FREE
// variable), then proves T2 (optimized == naive) by STRUCTURAL EQUALITY:
//
//   * equal expression DAGs over FREE atoms denote the same function under
//     EVERY assignment -- the free-algebra soundness, needing no enumeration
//     (so it covers cat_bounty's 2^784 assignments at once);
//   * PICK (copy) vs ROLL (move) -- the transform the optimizer performs on
//     cat_bounty -- is invisible in the symbolic value left on the stack, so
//     both decode to the SAME DAG;
//   * the MINIMALIF abort domain is preserved: every OP_IF/OP_NOTIF condition is
//     recorded in a `minimalif` list and equality requires those to match, so an
//     IF-removal (which changes which non-minimal bytes abort) is a structural
//     DIFFERENCE, never a false Proven.
//
// Values are HASH-CONSED into a shared arena and referenced by id, so a shared
// subexpression (e.g. the running accumulator, which appears in both arms of
// each `IF <w> ADD ENDIF`) is ONE node, not a duplicated subtree -- the DAG is
// O(script length), and equality is id comparison. Folding only collapses
// Const-only nodes; it never drops an atom, a Check, or a Select (an abort
// trace), so it cannot make two behaviourally-different scripts look equal.
//
// Soundness is "equal DAGs => equal behaviour"; completeness is "we only prove
// it when they match" (no canonicalization beyond constant folding). Anything
// outside the modelled opcode set, an Int witness param, or a guard inside a
// branch -> abstain (None), and the caller keeps its existing verdict.

use std::collections::HashMap;

/// An interned symbolic node; children are arena ids (`u32`).
#[derive(Clone, PartialEq, Eq, Hash)]
enum Node {
    Const(i128),
    Bytes(Vec<u8>),
    Atom(u32),
    Add(u32, u32),
    Sub(u32, u32),
    Neg(u32),
    Abs(u32),
    Min(u32, u32),
    Max(u32, u32),
    Within(u32, u32, u32),
    /// Numeric comparison (op byte) -> 0/1.
    Cmp(u8, u32, u32),
    And(u32, u32),
    Or(u32, u32),
    /// `truthy(cond) ? then : else` -- the merge of an OP_IF.
    Select(u32, u32, u32),
    // (logical NOT / 0NOTEQUAL lower to `Cmp` against 0, so no dedicated node.)
    /// CHECKSIG(sig, pubkey) -> 0/1 (opaque).
    Check(u32, u32),
    /// cast_to_bool.
    Truthy(u32),
    /// A hash op (op byte: SHA256/HASH160/...) as an UNINTERPRETED function of
    /// its input. Sound for any interpretation, incl. the real hash: equal
    /// `Hash` nodes => the same hash of the same input, which is all T1/T2 need.
    Hash(u8, u32),
    /// `OP_SIZE`: the byte length of a value (numeric, opaque for an atom).
    Size(u32),
    /// BYTEWISE `OP_EQUAL` -> 0/1 (distinct from numeric `Cmp`: it compares the
    /// encodings, the right relation for Bytes/Hash values).
    Eq(u32, u32),
}

/// Hash-consing arena: identical nodes share one id, so structural equality is
/// id equality and shared subexpressions are not duplicated.
struct Arena {
    nodes: Vec<Node>,
    dedup: HashMap<Node, u32>,
}
impl Arena {
    fn new() -> Arena {
        Arena {
            nodes: Vec::new(),
            dedup: HashMap::new(),
        }
    }
    fn intern(&mut self, n: Node) -> u32 {
        // Normalize so equal-by-algebra nodes share an id (sound integer
        // identities; they only improve structural matching):
        //  - commutative `Add` operand order (`a + b` == `b + a`), so the
        //    predicate's AST-order `bias + sum` matches the script's fold-first
        //    `sum + bias`;
        //  - a constant subtrahend `x - c` becomes `x + (-c)`, so OP_1SUB
        //    (`Sub(x, 1)`) matches `<-1> ADD` (`Add(x, -1)`).
        let n = match n {
            Node::Sub(a, b) => {
                let neg = match self.nodes[b as usize] {
                    Node::Const(c) => Some(-c),
                    _ => None,
                };
                match neg {
                    Some(nc) => {
                        let nid = self.intern(Node::Const(nc));
                        if a > nid {
                            Node::Add(nid, a)
                        } else {
                            Node::Add(a, nid)
                        }
                    }
                    None => Node::Sub(a, b),
                }
            }
            Node::Add(a, b) if a > b => Node::Add(b, a),
            other => other,
        };
        if let Some(&id) = self.dedup.get(&n) {
            return id;
        }
        let id = self.nodes.len() as u32;
        self.nodes.push(n.clone());
        self.dedup.insert(n, id);
        id
    }
    fn as_const(&self, id: u32) -> Option<i128> {
        match self.nodes[id as usize] {
            Node::Const(c) => Some(c),
            _ => None,
        }
    }
    /// Intern a node, constant-folding the arithmetic/comparison cases whose
    /// operands are all constants (never touching atom-bearing subtrees).
    fn mk(&mut self, n: Node) -> u32 {
        // Algebraic: fold a constant addend across a comparison --
        // `(x + c) op k  ==  x op (k - c)` -- so the optimizer's
        // bias-into-threshold peephole (script: `<c> ADD <k> CMP` -> `<k-c> CMP`)
        // matches the predicate Engine B builds from the unfolded source.
        if let Node::Cmp(op, lhs, rhs) = &n {
            let (op, lhs, rhs) = (*op, *lhs, *rhs);
            let k = self.as_const(rhs);
            let add_ops = match &self.nodes[lhs as usize] {
                Node::Add(p, q) => Some((*p, *q)),
                _ => None,
            };
            if let (Some(k), Some((p, q))) = (k, add_ops) {
                let folded = if let Some(c) = self.as_const(p) {
                    Some((q, k - c))
                } else {
                    self.as_const(q).map(|c| (p, k - c))
                };
                if let Some((x, nk)) = folded {
                    let kid = self.intern(Node::Const(nk));
                    return self.mk(Node::Cmp(op, x, kid));
                }
            }
        }
        let folded = match &n {
            Node::Add(a, b) => self.fold2(*a, *b, |x, y| x.checked_add(y)),
            Node::Sub(a, b) => self.fold2(*a, *b, |x, y| x.checked_sub(y)),
            Node::Cmp(op, a, b) => match (self.as_const(*a), self.as_const(*b)) {
                (Some(x), Some(y)) => Some(cmp_val(x, cmp_op(*op), y)),
                _ => None,
            },
            _ => None,
        };
        match folded {
            Some(v) => self.intern(Node::Const(v)),
            None => self.intern(n),
        }
    }
    fn fold2(&self, a: u32, b: u32, f: impl Fn(i128, i128) -> Option<i128>) -> Option<i128> {
        match (self.as_const(a), self.as_const(b)) {
            (Some(x), Some(y)) => f(x, y),
            _ => None,
        }
    }
}

/// A decoded script: its accept-function id and the ordered list of
/// OP_IF/OP_NOTIF condition ids (the MINIMALIF abort witnesses).
struct Decoded {
    accept: u32,
    minimalif: Vec<u32>,
}

struct IfFrame {
    cond: u32,
    negated: bool,
    saved: Vec<u32>,
    then_done: Option<Vec<u32>>,
}

/// Whether the predicate confines EVERY scalar `Int` witness param to a constant
/// range `x in lo..hi` with `-M <= lo` and `hi <= M+1` (so `x in [-M, M]`).
///
/// This is the precondition that makes Engine B SOUND for Int atoms.
/// Engine B models a witness atom as an
/// UNBOUNDED integer; the real script `num`s every Int operand and rejects any
/// out-of-`M` (5-byte) or non-minimal encoding. Those two views agree on the
/// 4-byte witness domain EXCEPT that the predicate-as-math would "accept"
/// out-of-`M` values the script rejects -- e.g. `a < b` is true at `a=-2^40`,
/// which the script rejects. With this guard the predicate ITSELF rejects
/// out-of-`M` (the range check `x in lo..hi` is false there), so script and
/// predicate agree over the whole domain and the structural equality is sound.
/// Unbounded Int leaves stay with Engine A/A_n (which handle out-of-`M` via
/// explicit `±(M+1)` sentinels) or remain `Unbounded`.
fn all_ints_bounded(body: &[Stmt], sig: &SpendSig, env: &Env) -> bool {
    let m = MACHINE_MAX;
    sig.params
        .iter()
        .filter(|p| matches!(p.ty, Ty::Int))
        .all(|p| {
            body.iter().any(|stmt| match stmt {
                Stmt::Require(req) => req.items.iter().any(|item| match item {
                    // `x in lo..hi` with constant bounds confining x to [-M, M].
                    Expr::In { value, lo, hi, .. } => {
                        matches!(value.as_ref(), Expr::Name(id) if id.text == p.name)
                            && matches!(pconst_int(lo, env), Some(l) if l >= -m)
                            && matches!(pconst_int(hi, env), Some(h) if h <= m + 1)
                    }
                    _ => false,
                }),
                _ => false,
            })
        })
}

fn engine_b(
    body: &[Stmt],
    sig: &SpendSig,
    env: &Env,
    naive: &LoweredLeaf,
    opt: &LoweredLeaf,
) -> Option<ProvenKind> {
    // Int atoms are admitted ONLY when the predicate bounds each to a constant
    // range (so out-of-M is rejected by both the script and the predicate -- see
    // all_ints_bounded). An Int hidden in an array is still out of scope. Pure
    // unbounded Int leaves are Engine A/A_n's job (or stay Unbounded).
    if sig.params.iter().any(|p| ty_has_array_int(&p.ty)) {
        return None;
    }
    if !all_ints_bounded(body, sig, env) {
        return None;
    }
    if naive.witness_order != opt.witness_order || naive.witness_order.is_empty() {
        return None;
    }
    let n = naive.witness_order.len();
    // ONE shared arena so equal expressions across the two scripts AND the
    // predicate share ids (structural equality is then id equality).
    let mut a = Arena::new();
    let dn = decode_to_sym(&mut a, &naive.script, n)?;
    let dop = decode_to_sym(&mut a, &opt.script, n)?;
    // T2: the optimized script is equivalent to the naive lowering.
    if canon_accept(&a, dn.accept) != canon_accept(&a, dop.accept) || dn.minimalif != dop.minimalif
    {
        return None;
    }
    // T1: the naive lowering implements the source predicate. We build the
    // predicate's accept-function from its DEFINITIONAL semantics (a
    // comprehension is its fold) into the SAME arena, independent of lowering;
    // if it matches the decoded naive script, both T1 and T2 hold (FullSymbolic).
    // If the predicate is outside the modelled fragment, T1 stays differential.
    let pred = pred_to_sym(body, sig, env, &naive.witness_order, &mut a);
    match pred {
        Some(pred) if canon_accept(&a, pred) == canon_accept(&a, dn.accept) => {
            Some(ProvenKind::FullSymbolic { atoms: n })
        }
        _ => Some(ProvenKind::T2OnlySymbolic {
            atoms: n,
            t1_reason: "predicate not in the symbolic fragment; T2 proven, T1 differential".into(),
        }),
    }
}

// --- Engine B, T1: the source predicate's symbolic accept-function ---
//
// Built from the predicate's DEFINITIONAL semantics into the same arena, over
// the same opaque witness atoms (atom id = position in `witness_order`), so a
// structural match with the decoded naive script proves the lowering implements
// the predicate (T1). A comprehension IS its fold, so `sum(... where g => b)`
// becomes `acc = Select(g, acc + b, acc)` -- exactly the IfAdd chain the
// lowering emits -- and they match WITHOUT any rewrite. This is an independent
// oracle: it evaluates the AST's meaning, never the lowering's code, so a
// lowering bug (wrong weight, order, or guard) makes the two diverge.
//
// `None` = abstain (a construct outside the modelled fragment, or an `after`
// timelock); the leaf then stays T2-only, never falsely FullSymbolic.

fn pred_to_sym(
    body: &[Stmt],
    sig: &SpendSig,
    env: &Env,
    atoms: &[String],
    a: &mut Arena,
) -> Option<u32> {
    let mut scope: Vec<(String, u32)> = Vec::new();
    let mut accept = a.intern(Node::Const(1));
    // The fixed-length airlocks the lowering emits for sized witness data
    // (`OP_SIZE <N> EQUALVERIFY` for `Bytes<N>`, decoded as a numeric length
    // check -- see decode_to_sym's 0x88 case) are part of the typed
    // predicate's domain: a `Bytes<N>` value IS N bytes. Encode that so the
    // accept-function matches the script over the full witness domain (both
    // reject a wrong-length witness), not just the typed sub-domain.
    for p in &sig.params {
        if let Ty::Bytes(Len::Lit(nbytes)) = &p.ty
            && let Some(i) = atom_id(atoms, &p.name)
        {
            let atom = a.intern(Node::Atom(i));
            let sz = a.intern(Node::Size(atom));
            let want = a.intern(Node::Const(*nbytes as i128));
            let g = a.mk(Node::Cmp(0x9c, sz, want)); // SIZE == N
            accept = a.intern(Node::And(accept, g));
        }
    }
    for stmt in body {
        match stmt {
            Stmt::Let { name, value, .. } => {
                let v = pev(value, &scope, env, atoms, a)?;
                scope.push((name.text.clone(), v));
            }
            Stmt::Require(req) => {
                for item in &req.items {
                    if is_call(item, "after") {
                        return None; // a timelock is not in the value fragment
                    }
                    let p = pev(item, &scope, env, atoms, a)?;
                    let t = a.intern(Node::Truthy(p));
                    accept = a.intern(Node::And(accept, t));
                }
            }
        }
    }
    Some(accept)
}

fn atom_id(atoms: &[String], slot: &str) -> Option<u32> {
    atoms.iter().position(|n| n == slot).map(|i| i as u32)
}

fn cv_node(a: &mut Arena, v: &ConstValue) -> Option<u32> {
    match v {
        ConstValue::Int(n) => Some(a.intern(Node::Const(*n))),
        ConstValue::Bool(b) => Some(a.intern(Node::Const(*b as i128))),
        ConstValue::Bytes(b) => Some(a.intern(Node::Bytes(b.clone()))),
        _ => None,
    }
}

fn cmp_byte(op: CmpOp) -> u8 {
    match op {
        CmpOp::Eq => 0x9c,
        CmpOp::Ne => 0x9e,
        CmpOp::Lt => 0x9f,
        CmpOp::Gt => 0xa0,
        CmpOp::Le => 0xa1,
        CmpOp::Ge => 0xa2,
    }
}

/// Evaluate a predicate expression to an arena Sym (opaque atoms for witness
/// values). `None` to abstain.
fn pev(
    e: &Expr,
    scope: &[(String, u32)],
    env: &Env,
    atoms: &[String],
    a: &mut Arena,
) -> Option<u32> {
    match e {
        Expr::Int { text, .. } => Some(a.intern(Node::Const(parse_int(text)?))),
        Expr::Bool { value, .. } => Some(a.intern(Node::Const(*value as i128))),
        Expr::Name(id) => {
            if let Some((_, v)) = scope.iter().rev().find(|(n, _)| *n == id.text) {
                return Some(*v);
            }
            match env.get(&id.text) {
                Some(cv @ (ConstValue::Int(_) | ConstValue::Bool(_) | ConstValue::Bytes(_))) => {
                    cv_node(a, cv)
                }
                _ => atom_id(atoms, &id.text).map(|i| a.intern(Node::Atom(i))),
            }
        }
        Expr::Unary {
            op: UnaryOp::Neg,
            operand,
            ..
        } => {
            let x = pev(operand, scope, env, atoms, a)?;
            Some(a.intern(Node::Neg(x)))
        }
        Expr::Unary {
            op: UnaryOp::Not,
            operand,
            ..
        } => {
            let x = pev(operand, scope, env, atoms, a)?;
            let z = a.intern(Node::Const(0));
            Some(a.mk(Node::Cmp(0x9c, x, z))) // !x == (x == 0)
        }
        Expr::Binary { op, lhs, rhs, .. } => {
            let l = pev(lhs, scope, env, atoms, a)?;
            let r = pev(rhs, scope, env, atoms, a)?;
            Some(match op {
                BinaryOp::Add => a.mk(Node::Add(l, r)),
                BinaryOp::Sub => a.mk(Node::Sub(l, r)),
            })
        }
        Expr::Compare { first, rest, .. } => {
            // Conjoin the chain's pairwise comparisons, but a single comparison
            // is RAW (no `And(1, ..)`), matching the script's bare op. Equality
            // on Bytes/Hash values is BYTEWISE (`Node::Eq`, the script's
            // OP_EQUAL), distinct from numeric `Cmp`.
            let mut acc: Option<u32> = None;
            let mut prev = pev(first, scope, env, atoms, a)?;
            for (op, next) in rest {
                let nv = pev(next, scope, env, atoms, a)?;
                let c = if *op == CmpOp::Eq && (is_bytesy(a, prev) || is_bytesy(a, nv)) {
                    a.intern(Node::Eq(prev, nv))
                } else if *op == CmpOp::Ne && (is_bytesy(a, prev) || is_bytesy(a, nv)) {
                    return None; // bytewise != not modelled here
                } else {
                    a.mk(Node::Cmp(cmp_byte(*op), prev, nv))
                };
                acc = Some(match acc {
                    None => c,
                    Some(p) => a.intern(Node::And(p, c)),
                });
                prev = nv;
            }
            acc
        }
        Expr::In {
            value,
            lo,
            hi,
            inclusive,
            ..
        } => {
            let v = pev(value, scope, env, atoms, a)?;
            let lo = pev(lo, scope, env, atoms, a)?;
            let hi = pev(hi, scope, env, atoms, a)?;
            // The lowering emits OP_WITHIN (half-open `lo <= v < hi`), so build the
            // matching `Within` node so T1 structurally matches the script. An
            // inclusive bound bumps the exclusive upper bound by one when it is a
            // constant (exactly as the lowering does); otherwise fall back to the
            // comparison conjunction (which won't match WITHIN, leaving T1
            // differential -- sound, just T2-only).
            let hi_excl = if *inclusive {
                match a.as_const(hi) {
                    Some(h) => a.intern(Node::Const(h + 1)),
                    None => {
                        let ge = a.mk(Node::Cmp(0xa2, v, lo)); // v >= lo
                        let le = a.mk(Node::Cmp(0xa1, v, hi)); // v <= hi
                        return Some(a.intern(Node::And(ge, le)));
                    }
                }
            } else {
                hi
            };
            Some(a.intern(Node::Within(v, lo, hi_excl)))
        }
        Expr::Index { base, index, .. } => {
            let Expr::Name(arr) = base.as_ref() else {
                return None;
            };
            let k = pconst_int(index, env)?;
            if k < 0 {
                return None;
            }
            let slot = format!("{}[{}]", arr.text, k);
            if let Some(i) = atom_id(atoms, &slot) {
                return Some(a.intern(Node::Atom(i)));
            }
            match env.get(&arr.text) {
                Some(ConstValue::Array(items)) if (k as usize) < items.len() => {
                    cv_node(a, &items[k as usize])
                }
                _ => None,
            }
        }
        Expr::Call { callee, args, .. } => pev_call(callee, args, scope, env, atoms, a),
        Expr::Comprehension {
            callee,
            binders,
            where_clauses,
            body,
            ..
        } => pev_sum(
            &callee.text,
            binders,
            where_clauses,
            body,
            scope,
            env,
            atoms,
            a,
        ),
        _ => None,
    }
}

fn pev_call(
    callee: &Expr,
    args: &[crate::syntax::ast::Arg],
    scope: &[(String, u32)],
    env: &Env,
    atoms: &[String],
    a: &mut Arena,
) -> Option<u32> {
    // `key.check(sig)` -> Check(sig_atom, key_bytes): an opaque 0/1, the same
    // Check node the script decodes (same sig atom, same key bytes).
    if let Expr::Member { base, member, .. } = callee
        && member.text == "check"
        && args.len() == 1
    {
        let key = pev(base, scope, env, atoms, a)?; // a Bytes node (const pubkey)
        let sig = pev(&args[0].value, scope, env, atoms, a)?;
        return Some(a.intern(Node::Check(sig, key)));
    }
    let Expr::Name(f) = callee else { return None };
    let arg = |i: usize, a: &mut Arena| pev(&args[i].value, scope, env, atoms, a);
    match (f.text.as_str(), args.len()) {
        ("min", 2) => {
            let x = arg(0, a)?;
            let y = arg(1, a)?;
            Some(a.intern(Node::Min(x, y)))
        }
        ("max", 2) => {
            let x = arg(0, a)?;
            let y = arg(1, a)?;
            Some(a.intern(Node::Max(x, y)))
        }
        ("abs", 1) => {
            let x = arg(0, a)?;
            Some(a.intern(Node::Abs(x)))
        }
        ("int", 1) => arg(0, a),
        // Hash intrinsics: the same uninterpreted Hash node the script decodes.
        ("sha256", 1) => {
            let x = arg(0, a)?;
            Some(a.intern(Node::Hash(0xa8, x)))
        }
        ("hash256", 1) => {
            let x = arg(0, a)?;
            Some(a.intern(Node::Hash(0xaa, x)))
        }
        ("hash160", 1) => {
            let x = arg(0, a)?;
            Some(a.intern(Node::Hash(0xa9, x)))
        }
        ("ripemd160", 1) => {
            let x = arg(0, a)?;
            Some(a.intern(Node::Hash(0xa6, x)))
        }
        ("sha1", 1) => {
            let x = arg(0, a)?;
            Some(a.intern(Node::Hash(0xa7, x)))
        }
        _ => None,
    }
}

/// A value whose equality is BYTEWISE (an opaque hash output or a byte literal),
/// so `==` lowers to `OP_EQUAL` rather than numeric `OP_NUMEQUAL`.
fn is_bytesy(a: &Arena, id: u32) -> bool {
    matches!(a.nodes[id as usize], Node::Hash(..) | Node::Bytes(_))
}

/// `sum(b in seq, ... where g => body)` as its fold:
/// `acc = Select(g, acc + body, acc)`, identity 0 -- the IfAdd chain.
#[allow(clippy::too_many_arguments)]
fn pev_sum(
    agg: &str,
    binders: &[crate::syntax::ast::Binder],
    where_clauses: &[Expr],
    body: &Expr,
    scope: &[(String, u32)],
    env: &Env,
    atoms: &[String],
    a: &mut Arena,
) -> Option<u32> {
    if agg != "sum" && agg != "count" {
        return None; // all/any/fold not modelled here
    }
    // The DECLARED element count. Witness binders under-report after
    // dead-witness elimination (their dropped slots are gone from `atoms`), so
    // take the max across binders -- a const co-binder reports the true zip
    // length. Dead-eligible folds always have such a const binder (the body must
    // fold to the identity, which needs a const operand).
    let n = binders
        .iter()
        .filter_map(|b| binder_count(&b.seq, env, atoms))
        .max()?;
    let mut acc = a.intern(Node::Const(0));
    for i in 0..n {
        // Skip exactly the elements the lowering dropped as provably dead: a
        // witness binder whose element-`i` slot is absent from `atoms`. Since
        // `atoms` IS the leaf's reduced witness_order, this matches the script's
        // omission element-for-element -- the reduced predicate vs reduced script.
        let eliminated = binders.iter().any(|b| {
            matches!(&b.seq, crate::syntax::ast::Seq::Expr(Expr::Name(arr))
                if !matches!(env.get(&arr.text), Some(ConstValue::Array(_)))
                    && atom_id(atoms, &format!("{}[{}]", arr.text, i)).is_none())
        });
        if eliminated {
            continue;
        }
        let mut inner = scope.to_vec();
        for b in binders {
            inner.push((b.name.text.clone(), binder_elem(&b.seq, i, env, atoms, a)?));
        }
        // The guard is the conjunction of the where-clauses; with a single
        // clause it is that clause RAW (no `And(1, ..)` wrapper), matching the
        // script's `OP_IF <cond>` exactly. No where-clause => always taken.
        let mut guard: Option<u32> = None;
        for w in where_clauses {
            let g = pev(w, &inner, env, atoms, a)?;
            guard = Some(match guard {
                None => g,
                Some(acc) => a.intern(Node::And(acc, g)),
            });
        }
        let guard = guard.unwrap_or_else(|| a.intern(Node::Const(1)));
        // The element's contribution to the accumulator, mirroring the lowering
        // exactly so the predicate's DAG matches the decoded script (T1):
        //  - sum: `acc + body`.
        //  - count: increments by one when the body holds. A const-true body
        //    always increments (`<where> IF ADD1 ENDIF`); a const-false body
        //    contributes nothing (`<where> IF ENDIF` -> acc unchanged); a dynamic
        //    body nests (`<where> IF <body> IF ADD1 ENDIF ENDIF`) ->
        //    `body ? acc+1 : acc`.
        let added = match agg {
            "sum" => {
                let contrib = pev(body, &inner, env, atoms, a)?;
                a.mk(Node::Add(acc, contrib))
            }
            _ => {
                // count
                let b = pev(body, &inner, env, atoms, a)?;
                let one = a.intern(Node::Const(1));
                match a.as_const(b) {
                    Some(c) if c != 0 => a.mk(Node::Add(acc, one)),
                    Some(_) => continue, // const-false body: this element adds nothing
                    None => {
                        let plus = a.mk(Node::Add(acc, one));
                        a.intern(Node::Select(b, plus, acc))
                    }
                }
            }
        };
        acc = a.intern(Node::Select(guard, added, acc));
    }
    Some(acc)
}

/// The element at index `i` of a binder sequence: a witness-array element is its
/// atom, a const-array element its value, a range element a constant.
fn binder_elem(
    seq: &crate::syntax::ast::Seq,
    i: usize,
    env: &Env,
    atoms: &[String],
    a: &mut Arena,
) -> Option<u32> {
    use crate::syntax::ast::Seq;
    match seq {
        Seq::Expr(Expr::Name(arr)) => {
            let slot = format!("{}[{}]", arr.text, i);
            if let Some(id) = atom_id(atoms, &slot) {
                return Some(a.intern(Node::Atom(id)));
            }
            match env.get(&arr.text) {
                Some(ConstValue::Array(items)) if i < items.len() => cv_node(a, &items[i]),
                _ => None,
            }
        }
        Seq::Range { lo, .. } => {
            let l = pconst_int(lo, env)?;
            Some(a.intern(Node::Const(l + i as i128)))
        }
        _ => None,
    }
}

/// The element count of a binder sequence (witness/const array length, or range
/// size), needed to unroll the fold. Bounded by the limits pass elsewhere.
fn binder_count(seq: &crate::syntax::ast::Seq, env: &Env, atoms: &[String]) -> Option<usize> {
    use crate::syntax::ast::Seq;
    match seq {
        Seq::Expr(Expr::Name(arr)) => {
            let prefix = format!("{}[", arr.text);
            let witness = atoms.iter().filter(|n| n.starts_with(&prefix)).count();
            if witness > 0 {
                return Some(witness);
            }
            match env.get(&arr.text) {
                Some(ConstValue::Array(items)) => Some(items.len()),
                _ => None,
            }
        }
        Seq::Range {
            lo, hi, inclusive, ..
        } => {
            let l = pconst_int(lo, env)?;
            let h = pconst_int(hi, env)?;
            let end = if *inclusive { h + 1 } else { h };
            usize::try_from((end - l).max(0)).ok()
        }
        _ => None,
    }
}

/// Evaluate an expression to a concrete integer (for array indices / range
/// bounds): a literal or an env Int const.
fn pconst_int(e: &Expr, env: &Env) -> Option<i128> {
    match e {
        Expr::Int { text, .. } => parse_int(text),
        Expr::Name(id) => match env.get(&id.text) {
            Some(ConstValue::Int(n)) => Some(*n),
            _ => None,
        },
        _ => None,
    }
}

/// Symbolically execute a script over `n` opaque witness atoms into the arena,
/// returning its accept-function id and IF-condition list. `None` (abstain) on
/// any opcode outside the modelled set, an unbalanced/over-deep branch, a guard
/// inside a branch, or a stack/shape error.
fn decode_to_sym(a: &mut Arena, script: &[u8], n: usize) -> Option<Decoded> {
    let mut stack: Vec<u32> = (0..n as u32).map(|i| a.intern(Node::Atom(i))).collect();
    let mut guard = a.intern(Node::Const(1)); // AND of top-level VERIFY conditions
    let mut minimalif: Vec<u32> = Vec::new();
    let mut frames: Vec<IfFrame> = Vec::new();
    let mut i = 0usize;

    while i < script.len() {
        let op = script[i];
        i += 1;

        if op == 0x4e {
            return None; // PUSHDATA4
        }
        if let Some(len) = push_len(op, script, &mut i)? {
            let end = i.checked_add(len)?;
            if end > script.len() {
                return None;
            }
            let id = a.intern(Node::Bytes(script[i..end].to_vec()));
            stack.push(id);
            i = end;
            continue;
        }
        if let Some(v) = small_push(op) {
            // OP_0 / OP_1NEGATE / OP_1..16 are NUMERIC pushes: intern as a
            // Const so a value reused in a non-numeric (e.g. Select else) path
            // matches the predicate's Const, not a raw `Bytes` (the empty-acc
            // `0` vs `Const(0)` mismatch). Data pushes (PUSHBYTES) stay Bytes.
            let n = decode_minimal(&v).ok()? as i128;
            let id = a.intern(Node::Const(n));
            stack.push(id);
            continue;
        }

        // Conditionals.
        match op {
            0x63 | 0x64 => {
                let cond = stack.pop()?;
                minimalif.push(cond);
                frames.push(IfFrame {
                    cond,
                    negated: op == 0x64,
                    saved: stack.clone(),
                    then_done: None,
                });
                continue;
            }
            0x67 => {
                let f = frames.last_mut()?;
                if f.then_done.is_some() {
                    return None;
                }
                f.then_done = Some(std::mem::take(&mut stack));
                stack = f.saved.clone();
                continue;
            }
            0x68 => {
                let f = frames.pop()?;
                let (then_s, else_s) = match f.then_done {
                    Some(t) => (t, stack),
                    None => (stack, f.saved),
                };
                if then_s.len() != else_s.len() {
                    return None;
                }
                let mut merged = Vec::with_capacity(then_s.len());
                for (t, e) in then_s.into_iter().zip(else_s) {
                    if t == e {
                        merged.push(t); // unchanged slot (cond still in `minimalif`)
                    } else if f.negated {
                        merged.push(a.intern(Node::Select(f.cond, e, t)));
                    } else {
                        merged.push(a.intern(Node::Select(f.cond, t, e)));
                    }
                }
                stack = merged;
                continue;
            }
            _ => {}
        }

        let in_branch = !frames.is_empty();

        match op {
            0x75 => {
                stack.pop()?;
            }
            0x6d => {
                stack.pop()?;
                stack.pop()?;
            }
            0x76 => {
                let t = *stack.last()?;
                stack.push(t);
            }
            0x77 => {
                let l = stack.len();
                if l < 2 {
                    return None;
                }
                stack.remove(l - 2);
            }
            0x78 => {
                let l = stack.len();
                if l < 2 {
                    return None;
                }
                stack.push(stack[l - 2]);
            }
            0x7c => {
                let l = stack.len();
                if l < 2 {
                    return None;
                }
                stack.swap(l - 1, l - 2);
            }
            0x7d => {
                let l = stack.len();
                if l < 2 {
                    return None;
                }
                let t = stack[l - 1];
                stack.insert(l - 2, t);
            }
            0x79 | 0x7a => {
                let d = sym_const(a, stack.pop()?)?;
                if d < 0 || d as usize >= stack.len() {
                    return None;
                }
                let idx = stack.len() - 1 - d as usize;
                if op == 0x79 {
                    stack.push(stack[idx]); // PICK copies
                } else {
                    let v = stack.remove(idx); // ROLL moves
                    stack.push(v);
                }
            }
            0x69 => {
                if in_branch {
                    return None;
                }
                let c = stack.pop()?;
                let t = a.intern(Node::Truthy(c));
                guard = a.intern(Node::And(guard, t));
            }
            0x8b | 0x8c | 0x8f | 0x90 | 0x91 | 0x92 => {
                let x = sym_num(a, stack.pop()?)?;
                let r = match op {
                    0x8b => {
                        let one = a.intern(Node::Const(1));
                        Node::Add(x, one)
                    }
                    0x8c => {
                        let one = a.intern(Node::Const(1));
                        Node::Sub(x, one)
                    }
                    0x8f => Node::Neg(x),
                    0x90 => Node::Abs(x),
                    0x91 => {
                        let z = a.intern(Node::Const(0));
                        Node::Cmp(0x9c, x, z) // NOT == (x == 0)
                    }
                    _ => {
                        let z = a.intern(Node::Const(0));
                        Node::Cmp(0x9e, x, z) // 0NOTEQUAL == (x != 0)
                    }
                };
                let id = a.mk(r);
                stack.push(id);
            }
            0x93 | 0x94 | 0x9a | 0x9b | 0x9c | 0x9e | 0x9f | 0xa0 | 0xa1 | 0xa2 | 0xa3 | 0xa4 => {
                let b = sym_num(a, stack.pop()?)?;
                let a0 = sym_num(a, stack.pop()?)?;
                let r = match op {
                    0x93 => Node::Add(a0, b),
                    0x94 => Node::Sub(a0, b),
                    0x9a => {
                        let ta = a.intern(Node::Truthy(a0));
                        let tb = a.intern(Node::Truthy(b));
                        Node::And(ta, tb)
                    }
                    0x9b => {
                        let ta = a.intern(Node::Truthy(a0));
                        let tb = a.intern(Node::Truthy(b));
                        Node::Or(ta, tb)
                    }
                    0xa3 => Node::Min(a0, b),
                    0xa4 => Node::Max(a0, b),
                    other => Node::Cmp(other, a0, b),
                };
                let id = a.mk(r);
                stack.push(id);
            }
            0x9d => {
                if in_branch {
                    return None;
                }
                let b = sym_num(a, stack.pop()?)?;
                let a0 = sym_num(a, stack.pop()?)?;
                let eq = a.mk(Node::Cmp(0x9c, a0, b));
                guard = a.intern(Node::And(guard, eq));
            }
            0xa5 => {
                let hi = sym_num(a, stack.pop()?)?;
                let lo = sym_num(a, stack.pop()?)?;
                let x = sym_num(a, stack.pop()?)?;
                let id = a.mk(Node::Within(x, lo, hi));
                stack.push(id);
            }
            0xac | 0xad => {
                if in_branch {
                    return None;
                }
                let pubkey = stack.pop()?;
                let s = stack.pop()?;
                let chk = a.intern(Node::Check(s, pubkey));
                if op == 0xad {
                    guard = a.intern(Node::And(guard, chk));
                } else {
                    stack.push(chk);
                }
            }
            0xba => {
                let pubkey = stack.pop()?;
                let nval = sym_num(a, stack.pop()?)?;
                let s = stack.pop()?;
                let chk = a.intern(Node::Check(s, pubkey));
                let id = a.mk(Node::Add(nval, chk));
                stack.push(id);
            }
            0x82 => {
                // OP_SIZE: pushes the top's byte length WITHOUT popping.
                let top = *stack.last()?;
                let sz = a.intern(Node::Size(top));
                stack.push(sz);
            }
            0xa6..=0xaa => {
                // RIPEMD160 / SHA1 / SHA256 / HASH160 / HASH256: hash the top.
                let v = stack.pop()?;
                stack.push(a.intern(Node::Hash(op, v)));
            }
            0x87 | 0x88 => {
                // OP_EQUAL / OP_EQUALVERIFY: BYTEWISE equality -- EXCEPT the
                // fixed-length airlock `SIZE <N> EQUALVERIFY`, whose left operand
                // is a `Size` node. That is a numeric length check: OP_SIZE and a
                // minimal `<N>` push share an encoding, so it is identical to the
                // predicate side's `Cmp(0x9c, Size, Const)` (pred_to_sym). Decode
                // it as that same numeric node so the airlock unifies with the
                // typed domain; every other EQUAL(VERIFY) stays bytewise.
                let b = stack.pop()?;
                let av = stack.pop()?;
                let eq = if matches!(a.nodes[av as usize], Node::Size(_)) {
                    // Fold the pushed length to a Const (as the 0x9d case does),
                    // so the node matches pred_to_sym's `Cmp(0x9c, Size, Const)`
                    // exactly -- a raw Bytes push would never unify.
                    let bn = sym_num(a, b)?;
                    a.mk(Node::Cmp(0x9c, av, bn))
                } else {
                    a.intern(Node::Eq(av, b))
                };
                if op == 0x88 {
                    if in_branch {
                        return None; // a conditional abort is not modelled
                    }
                    guard = a.intern(Node::And(guard, eq));
                } else {
                    stack.push(eq);
                }
            }
            _ => return None, // CLTV/CSV/unmodelled ops: abstain
        }
    }

    if !frames.is_empty() || stack.len() != 1 {
        return None;
    }
    let top = stack.pop()?;
    let t = a.intern(Node::Truthy(top));
    let accept = a.intern(Node::And(guard, t));
    Some(Decoded { accept, minimalif })
}

/// A concrete integer from a value id (only when constant), for PICK/ROLL depth.
fn sym_const(a: &Arena, id: u32) -> Option<i64> {
    match &a.nodes[id as usize] {
        Node::Const(c) => i64::try_from(*c).ok(),
        Node::Bytes(b) if b.len() <= 4 => decode_minimal(b).ok(),
        _ => None,
    }
}

/// Coerce a value id to a numeric one (decoding a concrete byte push as a
/// CScriptNum). `None` if the bytes are not a valid <=4-byte number.
fn sym_num(a: &mut Arena, id: u32) -> Option<u32> {
    match &a.nodes[id as usize] {
        Node::Bytes(b) => {
            if b.len() > 4 {
                return None;
            }
            let v = decode_minimal(b).ok()? as i128;
            Some(a.intern(Node::Const(v)))
        }
        _ => Some(id), // already numeric (Atom/Add/Cmp/Check/...)
    }
}

/// Canonicalize a top-level accept boolean into the SORTED, DEDUPED set of its
/// conjuncts, each represented by the id that "must be truthy". This applies
/// only sound boolean identities -- `And` is associative/commutative/idempotent;
/// `And(x, true)=x`; `Truthy(Truthy(x))=Truthy(x)`; `Truthy(const)` is decided --
/// so two accepts with equal canonical sets are semantically equal. It bridges
/// the harmless structural differences a value-preserving optimizer introduces
/// (e.g. a trailing `CHECKSIG` left on the stack vs a `CHECKSIGVERIFY` guard plus
/// a pushed `1`, with the consumed pixels `2DROP`ped). It does NOT reorder or
/// merge across `Or`/`Select`/arithmetic, so it cannot equate genuinely
/// different functions.
///
/// A conjunct id `u32::MAX` is the FALSE marker (a `Truthy(0)`/`Const(0)`
/// conjunct makes the whole conjunction false); present in the set iff the
/// accept is unconditionally false.
fn canon_accept(a: &Arena, id: u32) -> Vec<u32> {
    let mut cs = Vec::new();
    gather_conjuncts(a, id, &mut cs);
    cs.sort_unstable();
    cs.dedup();
    cs
}

/// Collect the conjuncts of `id` (interpreting each pushed id as "this must be
/// truthy"). A statically-true conjunct is dropped; a statically-false one
/// pushes `u32::MAX`.
fn gather_conjuncts(a: &Arena, id: u32, out: &mut Vec<u32>) {
    match &a.nodes[id as usize] {
        Node::And(x, y) => {
            let (x, y) = (*x, *y);
            gather_conjuncts(a, x, out);
            gather_conjuncts(a, y, out);
        }
        // `Truthy(inner)` as a conjunct == "inner must be truthy".
        Node::Truthy(inner) => push_conjunct(a, *inner, out),
        // Any other node as a conjunct == "this must be truthy".
        _ => push_conjunct(a, id, out),
    }
}

/// Push id as a "must be truthy" conjunct, deciding it when its truth is static.
fn push_conjunct(a: &Arena, id: u32, out: &mut Vec<u32>) {
    match const_truth(&a.nodes[id as usize]) {
        Some(true) => {}                   // a true conjunct: drop
        Some(false) => out.push(u32::MAX), // a false conjunct: whole accept false
        None => out.push(id),
    }
}

/// The static truth of a node, if it is a concrete value (`Const`/`Bytes`).
fn const_truth(n: &Node) -> Option<bool> {
    match n {
        Node::Const(c) => Some(*c != 0),
        Node::Bytes(b) => Some(cast_to_bool_bytes(b)),
        _ => None,
    }
}

/// `CastToBool` on raw bytes (mirrors interp.rs): true unless every byte is zero
/// except possibly a trailing 0x80 (negative zero).
fn cast_to_bool_bytes(v: &[u8]) -> bool {
    for (i, &b) in v.iter().enumerate() {
        if b != 0 {
            return !(i == v.len() - 1 && b == 0x80);
        }
    }
    false
}

/// Map a comparison op byte to the shared `CmpOp` used by `cmp_val`.
fn cmp_op(op: u8) -> CmpOp {
    match op {
        0x9c => CmpOp::Eq,
        0x9e => CmpOp::Ne,
        0x9f => CmpOp::Lt,
        0xa0 => CmpOp::Gt,
        0xa1 => CmpOp::Le,
        _ => CmpOp::Ge, // 0xa2
    }
}

/// Machine-checked soundness lemmas for the decision procedure (run via
/// `cargo kani`; `#[cfg(kani)]` keeps them out of every normal build so the
/// compiler stays zero-dependency). These prove SYMBOLICALLY -- over the whole
/// bounded-coefficient domain, not by enumeration -- the two SCALAR lemmas the
/// engines rest on. The STRUCTURAL parts (the `Pwa`/arena algebra over Vecs and
/// DAGs, decode faithfulness) are exhaustively VALIDATED by `exhaustive_gate` +
/// `certify_fuzz` + the Core differential, the project standard of proving
/// mechanically or exhaustively, since a proof-assistant TCB is excluded by the
/// zero-dependency rule.
#[cfg(kani)]
mod kani_proofs {
    /// Engine A / A_n COVERING-COMPLETENESS core. `bracket_crossing` brackets an
    /// affine atom's zero-crossing by inserting the cuts {q-1, q, q+1, q+2} with
    /// `q = (-c0).div_euclid(c1)`. Soundness requires the real root `x* = -c0/c1`
    /// to lie strictly inside `(q-1, q+1)` -- so the crossing is bracketed by
    /// inserted cuts and NO constant-sign cell straddles it. The integer-clean
    /// statement: `f(q-1)` and `f(q+1)` have strictly opposite signs, where
    /// `f(x) = c0 + c1*x`. Proven over the whole bounded domain (the interval
    /// engine bounds every magnitude to `M = 2^31 - 1`).
    #[kani::proof]
    fn bracket_crossing_brackets_the_root() {
        let c0: i128 = kani::any();
        let c1: i128 = kani::any();
        kani::assume(c1 != 0);
        let m: i128 = 1 << 31; // covers M = 2^31 - 1
        kani::assume(c0 >= -m && c0 <= m);
        kani::assume(c1 >= -m && c1 <= m);
        // `bracket_crossing` uses `q = (-c0).div_euclid(c1)`, so by the Euclidean
        // identity `-c0 = q*c1 + r` with `r = (-c0).rem_euclid(c1)`, the affine
        // `f(x) = c0 + c1*x` evaluates at the bracket's outer cuts to
        //   f(q-1) = c0 + c1*(q-1) = -r - c1,   f(q+1) = c0 + c1*(q+1) = c1 - r.
        // Computing `r` (one Euclidean division) and using these closed forms keeps
        // the proof free of the wide multiplication CBMC cannot bit-blast, while
        // staying faithful to the exact `q` the collector inserts.
        let r = (-c0).rem_euclid(c1); // 0 <= r < |c1|
        let f_qm1 = -r - c1; // f(q-1)
        let f_qp1 = c1 - r; // f(q+1)
        // A sign change strictly between the two inserted cuts (both nonzero,
        // opposite signs) -- the crossing cannot escape the bracket.
        assert!((f_qm1 < 0) != (f_qp1 < 0));
    }

    /// Phase 4 BOUNDED-ATOM soundness. A constant range `x in lo..hi` with
    /// `-M <= lo` and `hi <= M+1` rejects EVERY out-of-`M` witness, exactly as the
    /// script's `num` rejects a 5-byte operand. So Engine B's structural equality
    /// (which models an atom as an unbounded integer) is sound on the full 4-byte
    /// domain for a bounded Int: out-of-`M` is rejected by BOTH the predicate's
    /// range check and the script. This is the crux that lets `all_ints_bounded`
    /// admit Int atoms into Engine B.
    #[kani::proof]
    fn bounded_range_rejects_out_of_m() {
        let m: i128 = (1 << 31) - 1; // M, the 4-byte CScriptNum magnitude
        let x: i128 = kani::any();
        let lo: i128 = kani::any();
        let hi: i128 = kani::any();
        kani::assume(lo >= -m && lo <= m);
        kani::assume(hi >= -m && hi <= m + 1);
        kani::assume(x < -m || x > m); // out of the 4-byte domain (script `num` rejects)
        // `x in lo..hi` (half-open, OP_WITHIN) is false for every out-of-`M` x.
        assert!(!(lo <= x && x < hi));
    }
}

#[cfg(test)]
mod engine_b_tests {
    use super::*;
    use crate::analysis::sema::{ParamSig, SpendSig, Ty};
    use crate::codegen::lower::LoweredLeaf;

    fn leaf(script: Vec<u8>, wit: &[&str]) -> LoweredLeaf {
        LoweredLeaf {
            name: "f".into(),
            ops: vec![],
            script,
            witness_order: wit.iter().map(|s| s.to_string()).collect(),
            removable: vec![],
            cse_subjects: vec![],
        }
    }
    fn sig_of(params: &[&str]) -> SpendSig {
        SpendSig {
            name: "f".into(),
            open: false,
            params: params
                .iter()
                .map(|n| ParamSig {
                    name: n.to_string(),
                    ty: Ty::Bool,
                    relaxed: true,
                })
                .collect(),
        }
    }

    // OP_IF=0x63 OP_ELSE=0x67 OP_ENDIF=0x68 OP_1=0x51 OP_DROP=0x75
    const IF: u8 = 0x63;
    const ELSE: u8 = 0x67;
    const ENDIF: u8 = 0x68;
    const ONE: u8 = 0x51;
    const DROP: u8 = 0x75;

    // These exercise the T2 (opt == naive) decision directly with crafted
    // scripts; an empty body/env means T1 simply isn't proven (so a positive
    // result is T2OnlySymbolic), which is all `is_some()` requires.
    fn empty_env() -> crate::analysis::consteval::Env {
        crate::analysis::consteval::Env::new()
    }

    #[test]
    fn identical_scripts_are_proven() {
        let s = leaf(vec![IF, ONE, ELSE, ONE, ENDIF], &["a"]);
        let s2 = s.clone();
        assert!(engine_b(&[], &sig_of(&["a"]), &empty_env(), &s, &s2).is_some());
    }

    /// The abort-domain guard: two scripts with the SAME accept VALUE (always
    /// true) but DIFFERENT MINIMALIF structure must NOT be proven equal. The
    /// `IF` version aborts on a non-minimal byte for `a`; the `DROP` version does
    /// not -- so they diverge on non-minimal witness bytes, and a sound prover
    /// must refuse. (This is the case a naive `Select(c,a,a)->a` collapse would
    /// wrongly prove.)
    #[test]
    fn same_value_different_minimalif_is_not_proven() {
        let with_if = leaf(vec![IF, ONE, ELSE, ONE, ENDIF], &["a"]); // IF on a, value always 1
        let no_if = leaf(vec![DROP, ONE], &["a"]); // drop a, value always 1
        // Both accept unconditionally on minimal a, but only `with_if` aborts on
        // a non-minimal `a` byte.
        assert!(
            engine_b(&[], &sig_of(&["a"]), &empty_env(), &with_if, &no_if).is_none(),
            "differing abort domains must not be proven equal"
        );
    }

    /// Different witness layouts cannot be compared (atom indices would not
    /// align) -> abstain.
    #[test]
    fn mismatched_witness_order_abstains() {
        let a = leaf(vec![DROP, ONE], &["a", "b"]);
        let b = leaf(vec![DROP, ONE], &["b", "a"]);
        assert!(engine_b(&[], &sig_of(&["a", "b"]), &empty_env(), &a, &b).is_none());
    }
}

/// The reduced-domain exhaustive backstop:
/// the GATE every Int engine must pass before it ships. `try_prove` claims
/// equivalence over the COMPLETE domain; a box `[-M', M']ⁿ` is a subset of it,
/// so a genuine proof MUST hold on the box. We therefore enumerate the box
/// exhaustively and assert: if `try_prove` returns Proven, naive == opt ==
/// predicate at EVERY box point. A disagreement under a Proven verdict is a
/// FALSE PROOF -- the one failure that loses money. Generalized over any number
/// of Int params, so it validates the future n-D engine unchanged.
#[cfg(test)]
mod exhaustive_gate {
    use super::*;
    use crate::analysis::consteval::{bind_args, instantiate};
    use crate::analysis::intervals;
    use crate::analysis::paths;
    use crate::analysis::sema;
    use crate::analysis::sema::ContractInfo;
    use crate::codegen::lower::lower;
    use crate::codegen::optimize::optimize;
    use crate::diagnostics::Severity;
    use crate::json;
    use crate::syntax::ast::{Contract, Item};
    use crate::syntax::parser;

    const MARKER: [u8; 64] = [0xAA; 64];

    fn build(
        src: &str,
        args: &str,
    ) -> (
        Contract,
        ContractInfo,
        Env,
        Vec<LoweredLeaf>,
        Vec<LoweredLeaf>,
    ) {
        let (contract, pd) = parser::parse_source(src);
        assert!(pd.is_empty(), "parse: {pd:#?}");
        let c = contract.expect("contract");
        let (sd, info) = sema::analyze(&c);
        assert!(sd.is_empty(), "sema: {sd:#?}");
        let mut env = bind_args(&info, &json::parse(args).expect("json")).expect("bind");
        let id = instantiate(&c, &mut env);
        assert!(
            id.iter().all(|d| d.severity != Severity::Error),
            "instantiate: {id:#?}"
        );
        let (b, report) = intervals::analyze(&c, &env);
        assert!(b.is_empty(), "bounds: {b:#?}");
        let (pd2, _) = paths::analyze(&c, &info, &env);
        assert!(
            pd2.iter().all(|d| d.severity != Severity::Error),
            "paths: {pd2:#?}"
        );
        let (ld, naive) = lower(&c, &info, &env, &report);
        assert!(
            ld.iter().all(|d| d.severity != Severity::Error),
            "lower: {ld:#?}"
        );
        let opt: Vec<LoweredLeaf> = naive.iter().map(optimize).collect();
        (c, info, env, naive, opt)
    }

    fn read_example(name: &str, ext: &str) -> String {
        std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join(format!("tests/corpus/{name}.{ext}")),
        )
        .unwrap()
    }

    fn test_ctx<'a>(oracle: &'a dyn Fn(&[u8], &[u8]) -> bool) -> Context<'a> {
        Context {
            locktime: 0,
            sequence: 0xffff_fffe,
            tx_version: 2,
            verify_sig: oracle,
        }
    }

    /// Per-parameter box domains: every `Int` over `[-m, m]`, every finite param
    /// over its full domain. `None` if a non-Int param is not finitely
    /// enumerable (then the leaf is out of this gate's scope).
    fn box_domains(sig: &SpendSig, env: &Env, m: i64) -> Option<Vec<Vec<SatValue>>> {
        sig.params
            .iter()
            .map(|p| {
                if matches!(p.ty, Ty::Int) {
                    Some((-m..=m).map(SatValue::Int).collect())
                } else {
                    finite_domain(&p.ty, env)
                }
            })
            .collect()
    }

    /// True iff naive == opt (T2) and predicate == naive (T1, where it speaks) at
    /// EVERY point of the box. The exhaustive truth `try_prove` must not contradict.
    fn box_agrees(
        body: &[crate::syntax::ast::Stmt],
        sig: &SpendSig,
        env: &Env,
        naive: &LoweredLeaf,
        opt: &LoweredLeaf,
        ctx: &Context,
        m: i64,
    ) -> bool {
        let Some(doms) = box_domains(sig, env, m) else {
            return true;
        };
        let total: u128 = doms.iter().map(|d| d.len() as u128).product();
        for combo in 0..total {
            let mut c = combo;
            let mut plan: Vec<(String, SatValue)> = Vec::with_capacity(doms.len());
            for (p, d) in sig.params.iter().zip(&doms) {
                let idx = (c % d.len() as u128) as usize;
                c /= d.len() as u128;
                plan.push((p.name.clone(), d[idx].clone()));
            }
            let (Some(nok), Some(ook)) = (
                run(naive, sig, env, &plan, &MARKER, ctx),
                run(opt, sig, env, &plan, &MARKER, ctx),
            ) else {
                continue;
            };
            if nok != ook {
                return false; // T2 divergence inside the box
            }
            if let Some(pred) = eval_predicate(body, &plan, env, ctx.verify_sig, &MARKER, None)
                && pred != nok
            {
                return false; // T1 divergence inside the box
            }
        }
        true
    }

    /// For every leaf the engine PROVES, assert the box agrees -- i.e. no false
    /// proof manifests within `[-m, m]ⁿ`.
    fn assert_no_false_proof(src: &str, args: &str, m: i64) {
        let (c, info, env, naive, opt) = build(src, args);
        let oracle = |_pk: &[u8], s: &[u8]| s == MARKER.as_slice();
        let ctx = test_ctx(&oracle);
        let mut proven_any = false;
        for item in &c.items {
            let Item::Spend(s) = item else { continue };
            let Some(sig) = info.spends.iter().find(|x| x.name == s.name.text) else {
                continue;
            };
            let (Some(nl), Some(ol)) = (
                naive.iter().find(|l| l.name == s.name.text),
                opt.iter().find(|l| l.name == s.name.text),
            ) else {
                continue;
            };
            if try_prove(&s.body, sig, &env, nl, ol, &MARKER, &ctx).is_some() {
                proven_any = true;
                assert!(
                    box_agrees(&s.body, sig, &env, nl, ol, &ctx, m),
                    "FALSE PROOF: leaf `{}` is Proven by try_prove, but naive/opt/predicate \
                     disagree somewhere in [-{m}, {m}]",
                    s.name.text
                );
            }
        }
        assert!(proven_any, "no leaf was proven -- the gate ran on nothing");
    }

    const KEY: &str = "0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c";

    /// A genuine Engine-A proof (mirage, single Int) agrees with brute force over
    /// a box far wider than any enumeration window -- the gate confirms the proof
    /// is real, not vacuous.
    #[test]
    fn gate_confirms_mirage_proof() {
        assert_no_false_proof(
            &read_example("mirage", "sl"),
            &read_example("mirage", "args.json"),
            3000,
        );
    }

    /// Teeth: pair one contract's predicate+naive with a DIFFERENT contract's
    /// optimized leaf (a planted single-Int divergence at the differing bound).
    /// The engine MUST refuse (return None) -- and the box would have caught it.
    #[test]
    fn engine_refuses_a_planted_int_divergence() {
        let mk = |hi: i64| {
            format!(
                "contract T {{ extern const k: PublicKey;
                    spend f(relaxed x: Int, s: Signature) {{
                        require {{ x >= 0, x < {hi}, k.check(s) }}
                    }} keypath None; }}"
            )
        };
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        let (_ca, ia, ea, na, _) = build(&mk(1000), &args);
        let (_cb, _ib, _eb, nb, _) = build(&mk(1001), &args);
        let opt_b: Vec<LoweredLeaf> = nb.iter().map(optimize).collect(); // the x<1001 leaf
        let sig = ia.spends.iter().find(|s| s.name == "f").unwrap();
        let body = {
            let (c, _, _, _, _) = build(&mk(1000), &args);
            c.items
                .iter()
                .find_map(|it| match it {
                    Item::Spend(s) if s.name.text == "f" => Some(s.body.clone()),
                    _ => None,
                })
                .unwrap()
        };
        let nl = na.iter().find(|l| l.name == "f").unwrap();
        let ol = opt_b.iter().find(|l| l.name == "f").unwrap(); // mismatched: x<1001
        let oracle = |_pk: &[u8], s: &[u8]| s == MARKER.as_slice();
        let ctx = test_ctx(&oracle);
        assert!(
            try_prove(&body, sig, &ea, nl, ol, &MARKER, &ctx).is_none(),
            "engine wrongly proved a planted x<1000 vs x<1001 divergence"
        );
        // And the gate's box check independently sees the divergence at x = 1000.
        assert!(
            !box_agrees(&body, sig, &ea, nl, ol, &ctx, 1100),
            "box_agrees failed to detect the planted divergence"
        );
    }

    /// The engine must ABSTAIN (never falsely prove) on shapes it does not yet
    /// handle -- two Int witnesses. This pins fail-safe behaviour and is the
    /// placeholder the future 2-D engine must keep green (proving, not abstaining,
    /// while still passing `assert_no_false_proof`).
    #[test]
    fn engine_abstains_on_two_ints_no_false_proof() {
        let src = "contract U { extern const k: PublicKey;
            spend f(relaxed a: Int, relaxed b: Int, s: Signature) {
                require { a < b, k.check(s) }
            } keypath None; }";
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        let (c, info, env, naive, opt) = build(src, &args);
        let oracle = |_pk: &[u8], s: &[u8]| s == MARKER.as_slice();
        let ctx = test_ctx(&oracle);
        let s = c
            .items
            .iter()
            .find_map(|it| match it {
                Item::Spend(s) if s.name.text == "f" => Some(s),
                _ => None,
            })
            .unwrap();
        let sig = info.spends.iter().find(|x| x.name == "f").unwrap();
        let nl = naive.iter().find(|l| l.name == "f").unwrap();
        let ol = opt.iter().find(|l| l.name == "f").unwrap();
        assert!(
            try_prove(&s.body, sig, &env, nl, ol, &MARKER, &ctx).is_none(),
            "engine must abstain on two Int witnesses, not (yet) prove them"
        );
    }

    // --- Engine A2: the decoupled grid (two Int vars) ---

    /// The decoupled grid PROVES two independent Int ranges, and the box confirms
    /// naive == opt == predicate over the full `[-m, m]^2` -- a genuine 2-D proof,
    /// not vacuous. `a in 0..N` and `b in 0..N` never share a cross-axis atom.
    #[test]
    fn gate_confirms_decoupled_two_int_proof() {
        let src = "contract D { extern const k: PublicKey;
            spend f(relaxed a: Int, relaxed b: Int, s: Signature) {
                require { a in 0..60, b in 0..60, k.check(s) }
            } keypath None; }";
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        assert_no_false_proof(src, &args, 100);
    }

    /// A second decoupled shape: independent COMPARISON atoms per axis (not `in`),
    /// asymmetric bounds, both directions. Still a grid -> still proven.
    #[test]
    fn gate_confirms_decoupled_two_int_comparisons() {
        let src = "contract D2 { extern const k: PublicKey;
            spend f(relaxed a: Int, relaxed b: Int, s: Signature) {
                require { a >= 10, a < 40, b > 20, b <= 70, k.check(s) }
            } keypath None; }";
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        assert_no_false_proof(src, &args, 100);
    }

    /// The decoupled engine actually returns a 2-var `FullInt` proof (the comma in
    /// `var` marks the two-axis verdict), where the coupled `a < b` shape
    /// (`engine_abstains_on_two_ints_no_false_proof`) must abstain. Pins the
    /// upgrade: proving, not abstaining.
    #[test]
    fn engine_proves_two_decoupled_ints() {
        let src = "contract D { extern const k: PublicKey;
            spend f(relaxed a: Int, relaxed b: Int, s: Signature) {
                require { a in 0..100, b in 0..100, k.check(s) }
            } keypath None; }";
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        let (c, info, env, naive, opt) = build(src, &args);
        let oracle = |_pk: &[u8], s: &[u8]| s == MARKER.as_slice();
        let ctx = test_ctx(&oracle);
        let s = c
            .items
            .iter()
            .find_map(|it| match it {
                Item::Spend(s) if s.name.text == "f" => Some(s),
                _ => None,
            })
            .unwrap();
        let sig = info.spends.iter().find(|x| x.name == "f").unwrap();
        let nl = naive.iter().find(|l| l.name == "f").unwrap();
        let ol = opt.iter().find(|l| l.name == "f").unwrap();
        match try_prove(&s.body, sig, &env, nl, ol, &MARKER, &ctx) {
            Some(ProvenKind::FullInt { var, .. }) => {
                assert!(
                    var.contains(','),
                    "expected a two-var FullInt proof, got var={var}"
                )
            }
            other => panic!("expected FullInt over two decoupled ints, got {other:?}"),
        }
    }

    /// Teeth for the 2-D engine: pair a decoupled contract's predicate+naive with
    /// a DIFFERENT contract's optimized leaf whose `a` bound is off by one (a
    /// planted divergence at `a = 50`, on the p-axis only). The engine MUST refuse,
    /// and the box independently sees the divergence.
    #[test]
    fn engine_refuses_a_planted_cross_axis_divergence() {
        let mk = |ahi: i64| {
            format!(
                "contract T {{ extern const k: PublicKey;
                    spend f(relaxed a: Int, relaxed b: Int, s: Signature) {{
                        require {{ a >= 0, a < {ahi}, b >= 0, b < 60, k.check(s) }}
                    }} keypath None; }}"
            )
        };
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        let (_ca, ia, ea, na, _) = build(&mk(50), &args);
        let (_cb, _ib, _eb, nb, _) = build(&mk(51), &args);
        let opt_b: Vec<LoweredLeaf> = nb.iter().map(optimize).collect(); // the a<51 leaf
        let sig = ia.spends.iter().find(|s| s.name == "f").unwrap();
        let body = {
            let (c, _, _, _, _) = build(&mk(50), &args);
            c.items
                .iter()
                .find_map(|it| match it {
                    Item::Spend(s) if s.name.text == "f" => Some(s.body.clone()),
                    _ => None,
                })
                .unwrap()
        };
        let nl = na.iter().find(|l| l.name == "f").unwrap();
        let ol = opt_b.iter().find(|l| l.name == "f").unwrap(); // mismatched: a<51
        let oracle = |_pk: &[u8], s: &[u8]| s == MARKER.as_slice();
        let ctx = test_ctx(&oracle);
        assert!(
            try_prove(&body, sig, &ea, nl, ol, &MARKER, &ctx).is_none(),
            "engine wrongly proved a planted a<50 vs a<51 cross-axis divergence"
        );
        assert!(
            !box_agrees(&body, sig, &ea, nl, ol, &ctx, 80),
            "box_agrees failed to detect the planted cross-axis divergence"
        );
    }

    /// Adversarial coupling sweep: EVERY shape whose atoms couple the two axes
    /// (`a < b`, `a == b`, `a + b < k`, `a - b ...`, and a `let`-hidden sum) MUST
    /// abstain -- the `P (x) Q` guard is what licenses the grid decomposition, so a
    /// single coupled shape slipping through to `Proven` would be a thin-band
    /// false proof (the failure mode the decoupled phase exists to avoid). These
    /// are cheap (no box) and pin the guard on every reachable path.
    #[test]
    fn engine_abstains_on_every_coupling_shape() {
        // Compilable coupling atoms (comparison / min / max). Arithmetic
        // couplings like `a + b` overflow the 4-byte CScriptNum domain on two
        // machine-range witnesses, so the bounds pass rejects them before the
        // certifier -- the language itself never produces an arithmetic-coupled
        // 2-Int leaf. These comparison-style couplings DO compile, and each must
        // abstain: a single one slipping to `Proven` would be a thin-band false
        // proof (the failure mode the decoupled phase exists to avoid).
        let coupled = [
            "a < b",
            "a <= b",
            "a == b",
            "a > b",
            "min(a, b) >= 100",
            "max(a, b) <= 900",
        ];
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        let oracle = |_pk: &[u8], s: &[u8]| s == MARKER.as_slice();
        let ctx = test_ctx(&oracle);
        for item in coupled {
            let src = format!(
                "contract C {{ extern const k: PublicKey;
                    spend f(relaxed a: Int, relaxed b: Int, s: Signature) {{
                        require {{ {item}, k.check(s) }}
                    }} keypath None; }}"
            );
            let (c, info, env, naive, opt) = build(&src, &args);
            let s = c
                .items
                .iter()
                .find_map(|it| match it {
                    Item::Spend(s) if s.name.text == "f" => Some(s),
                    _ => None,
                })
                .unwrap();
            let sig = info.spends.iter().find(|x| x.name == "f").unwrap();
            let nl = naive.iter().find(|l| l.name == "f").unwrap();
            let ol = opt.iter().find(|l| l.name == "f").unwrap();
            assert!(
                try_prove(&s.body, sig, &env, nl, ol, &MARKER, &ctx).is_none(),
                "coupled shape `{item}` must abstain (P(x)Q), but the engine proved it"
            );
        }

        // A coupling hidden behind a `let` must also abstain (both the script and
        // the predicate paths see the cross-axis value through the binding and
        // decline). `min(a, b)` fits the machine domain, so this compiles.
        let src = "contract CL { extern const k: PublicKey;
            spend f(relaxed a: Int, relaxed b: Int, s: Signature) {
                let m = min(a, b);
                require { m >= 100, k.check(s) }
            } keypath None; }";
        let (c, info, env, naive, opt) = build(src, &args);
        let s = c
            .items
            .iter()
            .find_map(|it| match it {
                Item::Spend(s) if s.name.text == "f" => Some(s),
                _ => None,
            })
            .unwrap();
        let sig = info.spends.iter().find(|x| x.name == "f").unwrap();
        let nl = naive.iter().find(|l| l.name == "f").unwrap();
        let ol = opt.iter().find(|l| l.name == "f").unwrap();
        assert!(
            try_prove(&s.body, sig, &env, nl, ol, &MARKER, &ctx).is_none(),
            "a let-hidden coupling `a + b` must abstain, but the engine proved it"
        );
    }

    // --- Engine A_n: n > 2 decoupled vars + cell cap (Phase 2) ---

    /// Find spend `f`, returning everything `try_prove` needs.
    fn prep<'a>(
        c: &'a Contract,
        info: &'a ContractInfo,
        naive: &'a [LoweredLeaf],
        opt: &'a [LoweredLeaf],
    ) -> (
        &'a [crate::syntax::ast::Stmt],
        &'a SpendSig,
        &'a LoweredLeaf,
        &'a LoweredLeaf,
    ) {
        let s = c
            .items
            .iter()
            .find_map(|it| match it {
                Item::Spend(s) if s.name.text == "f" => Some(s),
                _ => None,
            })
            .unwrap();
        let sig = info.spends.iter().find(|x| x.name == "f").unwrap();
        let nl = naive.iter().find(|l| l.name == "f").unwrap();
        let ol = opt.iter().find(|l| l.name == "f").unwrap();
        (&s.body, sig, nl, ol)
    }

    /// The decoupled grid generalizes to THREE vars: three independent ranges
    /// prove, and the box confirms naive == opt == predicate over the full
    /// `[-m, m]^3` -- a genuine 3-D proof.
    #[test]
    fn gate_confirms_decoupled_three_int_proof() {
        let src = "contract D3 { extern const k: PublicKey;
            spend f(relaxed a: Int, relaxed b: Int, relaxed c: Int, s: Signature) {
                require { a in 0..10, b in 0..10, c in 0..10, k.check(s) }
            } keypath None; }";
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        assert_no_false_proof(src, &args, 15);
    }

    /// A genuine three-var `FullInt` verdict (two commas in `var`).
    #[test]
    fn engine_proves_three_decoupled_ints() {
        let src = "contract D3 { extern const k: PublicKey;
            spend f(relaxed a: Int, relaxed b: Int, relaxed c: Int, s: Signature) {
                require { a in 0..50, b in 0..50, c in 0..50, k.check(s) }
            } keypath None; }";
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        let (c, info, env, naive, opt) = build(src, &args);
        let oracle = |_pk: &[u8], s: &[u8]| s == MARKER.as_slice();
        let ctx = test_ctx(&oracle);
        let (body, sig, nl, ol) = prep(&c, &info, &naive, &opt);
        match try_prove(body, sig, &env, nl, ol, &MARKER, &ctx) {
            Some(ProvenKind::FullInt { var, .. }) => {
                assert_eq!(
                    var.matches(',').count(),
                    2,
                    "expected a three-var FullInt, got var={var}"
                )
            }
            other => panic!("expected FullInt over three decoupled ints, got {other:?}"),
        }
    }

    /// A bounded COUPLED leaf (`b < c`, every Int range-bounded) is now PROVEN by
    /// Engine B's structural equality (Phase 4): the decoupled grid can't handle a
    /// diagonal atom, but EXACT symbolic equality of naive/opt/predicate proves it,
    /// and the const ranges make out-of-M sound (the predicate rejects it too).
    /// The box confirms naive == opt == predicate over the whole `[-m, m]^3` -- the
    /// soundness teeth for the coupled case (the gate CAN enumerate pure-Int).
    #[test]
    fn gate_proves_bounded_coupled_three_ints() {
        let src = "contract C3 { extern const k: PublicKey;
            spend f(relaxed a: Int, relaxed b: Int, relaxed c: Int, s: Signature) {
                require { a in 0..8, b in 0..8, c in 0..8, b < c, k.check(s) }
            } keypath None; }";
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        assert_no_false_proof(src, &args, 12);
    }

    /// `engine_an`'s graceful degradation (§3.6) is now an INTERNAL property: five
    /// decoupled axes blow its per-slice cell cap, so it returns a clean `None`
    /// (no crash/OOM). `try_prove` then proves the leaf via Engine B's LINEAR
    /// structural equality, which has no grid blowup -- the cap protects the grid
    /// engine, and the structural engine is the high-dimension fallback.
    #[test]
    fn engine_an_cap_degrades_to_none() {
        let src = "contract Cap { extern const k: PublicKey;
            spend f(relaxed a: Int, relaxed b: Int, relaxed c: Int, relaxed d: Int, relaxed e: Int, s: Signature) {
                require { a in 0..900, b in 0..900, c in 0..900, d in 0..900, e in 0..900, k.check(s) }
            } keypath None; }";
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        let (c, info, env, naive, opt) = build(src, &args);
        let oracle = |_pk: &[u8], s: &[u8]| s == MARKER.as_slice();
        let ctx = test_ctx(&oracle);
        let (body, sig, nl, ol) = prep(&c, &info, &naive, &opt);
        assert!(
            engine_an(body, sig, &env, nl, ol, &MARKER, &ctx).is_none(),
            "engine_an must hit the cell cap and return None on five ranges"
        );
        assert!(
            try_prove(body, sig, &env, nl, ol, &MARKER, &ctx).is_some(),
            "try_prove should fall through to Engine B and prove the bounded decoupled leaf"
        );
    }

    // --- Engine A_n: branching over Int (Phase 3, OP_IF/ELSE/ENDIF) ---

    /// A `select` whose guard is a comparison on an Int axis (a DYNAMIC branch:
    /// `OP_IF` forks on `b > 10`). The decoupled grid proves it -- the branch is
    /// another cutting hyperplane on axis `b` -- and the box confirms naive == opt
    /// == predicate over the full `[-m, m]^2`.
    #[test]
    fn gate_confirms_decoupled_select_int_proof() {
        let src = "contract S { extern const k: PublicKey;
            spend f(relaxed a: Int, relaxed b: Int, s: Signature) {
                require { a in 0..20, b in 0..30, select(b > 10, then: b, else: 5) >= 8, k.check(s) }
            } keypath None; }";
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        assert_no_false_proof(src, &args, 40);
    }

    /// A `select` guarded by a BOOL witness (a STATIC branch per slice -- the
    /// guard is fixed bytes once the Bool is enumerated, so `OP_IF` picks one arm).
    /// Two Int branches on distinct axes still prove because each slice collapses
    /// to a single axis.
    #[test]
    fn gate_confirms_bool_guarded_select_proof() {
        let src = "contract SB { extern const k: PublicKey;
            spend f(relaxed flag: Bool, relaxed a: Int, relaxed b: Int, s: Signature) {
                require { a in 0..40, b in 0..40, select(flag, then: a, else: b) >= 20, k.check(s) }
            } keypath None; }";
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        assert_no_false_proof(src, &args, 50);
    }

    /// A bounded CROSS-AXIS branch (`select(a>4, b, c)`, every Int range-bounded)
    /// is PROVEN by Engine B (Phase 4): the decoupled grid abstains (the select
    /// couples three axes), but the OP_IF decodes to a `Select` node that matches
    /// the predicate's `Select` structurally, and the ranges make it sound. The box
    /// validates over `[-m, m]^3`. (Engine A_n's `sym_accept_n` still abstains on
    /// this cross-axis merge -- that path is unchanged; Engine B is the fallback.)
    #[test]
    fn gate_proves_bounded_cross_branch_select() {
        let src = "contract SX { extern const k: PublicKey;
            spend f(relaxed a: Int, relaxed b: Int, relaxed c: Int, s: Signature) {
                require { a in 0..8, b in 0..8, c in 0..8, select(a > 4, then: b, else: c) >= 2, k.check(s) }
            } keypath None; }";
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        assert_no_false_proof(src, &args, 12);
    }

    /// Teeth: a planted divergence INSIDE a branch -- pair a select contract's
    /// predicate+naive with a twin whose `else` constant differs (5 vs 6), so the
    /// optimized leaf accepts a `b` the naive rejects. The engine must refuse, and
    /// the box independently sees the divergence.
    #[test]
    fn engine_refuses_a_planted_in_branch_divergence() {
        let mk = |els: i64| {
            format!(
                "contract S {{ extern const k: PublicKey;
                    spend f(relaxed a: Int, relaxed b: Int, s: Signature) {{
                        require {{ a in 0..20, b in 0..30, select(b > 10, then: 0, else: {els}) >= 3, k.check(s) }}
                    }} keypath None; }}"
            )
        };
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        let (_ca, ia, ea, na, _) = build(&mk(0), &args); // else=0 -> never >=3 for b<=10
        let (_cb, _ib, _eb, nb, _) = build(&mk(5), &args); // else=5 ->     >=3 for b<=10
        let opt_b: Vec<LoweredLeaf> = nb.iter().map(optimize).collect();
        let sig = ia.spends.iter().find(|s| s.name == "f").unwrap();
        let body = {
            let (c, _, _, _, _) = build(&mk(0), &args);
            c.items
                .iter()
                .find_map(|it| match it {
                    Item::Spend(s) if s.name.text == "f" => Some(s.body.clone()),
                    _ => None,
                })
                .unwrap()
        };
        let nl = na.iter().find(|l| l.name == "f").unwrap();
        let ol = opt_b.iter().find(|l| l.name == "f").unwrap();
        let oracle = |_pk: &[u8], s: &[u8]| s == MARKER.as_slice();
        let ctx = test_ctx(&oracle);
        assert!(
            try_prove(&body, sig, &ea, nl, ol, &MARKER, &ctx).is_none(),
            "engine wrongly proved a planted in-branch divergence (else 0 vs 5)"
        );
        assert!(
            !box_agrees(&body, sig, &ea, nl, ol, &ctx, 40),
            "box_agrees failed to detect the planted in-branch divergence"
        );
    }
}
