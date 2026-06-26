//! Per-compile certification: T1 (lowering) and T2 (optimizer) of the
//! verification program.
//!
//! This module is an INDEPENDENT oracle. It shares no code with `lower` or
//! `optimize`: it evaluates a spend's `require` block directly over a concrete
//! witness assignment (the denotational meaning of the predicate) and compares
//! that against what the naive and optimized scripts actually do under the
//! interpreter. Three-way agreement
//!
//! ```text
//! eval_predicate(W)  ==  exec(naive, W)  ==  exec(optimized, W)
//! ```
//!
//! over the COMPLETE witness domain (when finite) is an exhaustive proof, for
//! that leaf, that the optimizer preserved behavior (T2) AND that the naive
//! lowering implements the predicate (T1) -- no sampling.
//!
//! Soundness over completeness, by design (the money axis): the evaluator
//! ABSTAINS (returns None) on any construct, value type, or arithmetic it
//! cannot model EXACTLY -- an unmodeled call, a mixed-type comparison, an
//! integer overflow -- and the certifier reports the leaf as Differential
//! rather than guessing. This is the soundness backstop: anything the
//! evaluator cannot compute faithfully turns into "T1 not asserted here," never
//! a wrong agreement. An abstained leaf is never claimed certified; it still
//! receives the naive-vs-optimized differential (T2) over its finite domain.
//! The evaluator must be VALIDATED against the known-good corpus (its agreement
//! there corroborates the oracle) before a disagreement elsewhere is read as a
//! real T1 defect.
//!
//! Scope of "finite" today: Bool, Signature (as valid/declined), and arrays of
//! them -- the voting/threshold/classifier class. Their canonical encodings
//! ({}, 0x01, marker/empty) are behaviorally complete for accept/reject. Int,
//! Bytes/Hash/PublicKey, and timelocks (`after`) make the domain unbounded or
//! the evaluator abstain; those route to SMT/differential in later phases.

use crate::analysis::consteval::{ConstValue, Env, LockAbs, LockRel, MACHINE_MAX, eval_in_env};
use crate::analysis::sema::{ContractInfo, Len, SpendSig, Ty};
use crate::codegen::lower::LoweredLeaf;
use crate::syntax::ast::*;
use crate::verify::interp::{Context, execute, timelock_ok};
use crate::verify::satisfy::{SatValue, build_witness};

/// The independent value model. Deliberately separate from `ConstValue` and
/// from anything in lowering, so a shared bug cannot mask a divergence.
#[derive(Clone, Debug)]
enum Val {
    Int(i128),
    Bool(bool),
    Bytes(Vec<u8>),
    /// A signature witness: present (a valid marker) or declined.
    Sig(bool),
    Array(Vec<Val>),
}

fn as_int(v: &Val) -> Option<i128> {
    match v {
        Val::Int(n) => Some(*n),
        Val::Bool(b) => Some(*b as i128), // check()/bool in arithmetic is 0/1
        _ => None,
    }
}

fn truthy(v: &Val) -> Option<bool> {
    match v {
        Val::Bool(b) => Some(*b),
        Val::Int(n) => Some(*n != 0),
        _ => None,
    }
}

fn parse_int(text: &str) -> Option<i128> {
    let t: String = text.chars().filter(|c| *c != '_').collect();
    if let Some(hex) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        i128::from_str_radix(hex, 16).ok()
    } else {
        t.parse::<i128>().ok()
    }
}

fn parse_hex(text: &str) -> Option<Vec<u8>> {
    let t = text
        .strip_prefix("0x")
        .or_else(|| text.strip_prefix("0X"))
        .unwrap_or(text);
    if !t.len().is_multiple_of(2) {
        return None;
    }
    (0..t.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&t[i..i + 2], 16).ok())
        .collect()
}

fn cv_to_val(c: &ConstValue) -> Option<Val> {
    Some(match c {
        ConstValue::Int(n) => Val::Int(*n),
        ConstValue::Bool(b) => Val::Bool(*b),
        ConstValue::Bytes(b) => Val::Bytes(b.clone()),
        ConstValue::Array(items) => Val::Array(items.iter().map(cv_to_val).collect::<Option<_>>()?),
        // Timelock values are only consumed by `after`, handled (abstained) at
        // the require-item level; they never appear as evaluable values here.
        ConstValue::LockAbs(_) | ConstValue::LockRel(_) => return None,
    })
}

/// Evaluator state. `scope` is the lexical stack of lets, comprehension
/// binders, and fold accumulators (innermost last); it shadows witness params,
/// which shadow contract consts.
struct Ev<'a> {
    env: &'a Env,
    witness: &'a [(String, Val)],
    verify_sig: &'a dyn Fn(&[u8], &[u8]) -> bool,
    marker: &'a [u8],
}

impl Ev<'_> {
    fn lookup(&self, name: &str, scope: &[(String, Val)]) -> Option<Val> {
        if let Some((_, v)) = scope.iter().rev().find(|(n, _)| n == name) {
            return Some(v.clone());
        }
        if let Some((_, v)) = self.witness.iter().find(|(n, _)| n == name) {
            return Some(v.clone());
        }
        self.env.get(name).and_then(cv_to_val)
    }

    fn eval(&self, e: &Expr, scope: &[(String, Val)]) -> Option<Val> {
        match e {
            Expr::Int { text, .. } => Some(Val::Int(parse_int(text)?)),
            Expr::Bool { value, .. } => Some(Val::Bool(*value)),
            Expr::Str { text, .. } => Some(Val::Bytes(parse_hex(text)?)),
            Expr::Name(id) => self.lookup(&id.text, scope),
            Expr::Index { base, index, .. } => {
                let Val::Array(items) = self.eval(base, scope)? else {
                    return None;
                };
                let i = as_int(&self.eval(index, scope)?)?;
                if i < 0 || i as usize >= items.len() {
                    return None;
                }
                Some(items[i as usize].clone())
            }
            Expr::Unary { op, operand, .. } => {
                let v = self.eval(operand, scope)?;
                match op {
                    UnaryOp::Not => Some(Val::Bool(!truthy(&v)?)),
                    // Checked: abstain (None) rather than wrap/panic on
                    // overflow, so any arithmetic the evaluator cannot model
                    // exactly becomes a sound Differential, never a false
                    // agreement. (Unreachable on the finite certified domain,
                    // where consts are bounded to +/-2^31 and witnesses tiny.)
                    UnaryOp::Neg => Some(Val::Int(as_int(&v)?.checked_neg()?)),
                }
            }
            Expr::Binary { op, lhs, rhs, .. } => {
                let a = as_int(&self.eval(lhs, scope)?)?;
                let b = as_int(&self.eval(rhs, scope)?)?;
                let r = match op {
                    BinaryOp::Add => a.checked_add(b),
                    BinaryOp::Sub => a.checked_sub(b),
                };
                Some(Val::Int(r?)) // overflow -> abstain
            }
            Expr::Compare { first, rest, .. } => {
                let mut prev = self.eval(first, scope)?;
                let mut acc = true;
                for (op, next) in rest {
                    let nv = self.eval(next, scope)?;
                    acc = acc && self.cmp(op, &prev, &nv)?;
                    prev = nv;
                }
                Some(Val::Bool(acc))
            }
            Expr::In {
                value,
                lo,
                hi,
                inclusive,
                ..
            } => {
                let v = as_int(&self.eval(value, scope)?)?;
                let lo = as_int(&self.eval(lo, scope)?)?;
                let hi = as_int(&self.eval(hi, scope)?)?;
                Some(Val::Bool(
                    lo <= v && if *inclusive { v <= hi } else { v < hi },
                ))
            }
            Expr::ArrayLit { elems, .. } => Some(Val::Array(
                elems
                    .iter()
                    .map(|e| self.eval(e, scope))
                    .collect::<Option<_>>()?,
            )),
            Expr::TypedCtor { args, .. } => {
                // Bytes<N>("0x..") / Hash<Alg>("0x..") -- a byte literal.
                let [a] = args.as_slice() else { return None };
                self.eval(&a.value, scope)
            }
            Expr::Call { callee, args, .. } => self.eval_call(callee, args, scope),
            Expr::Comprehension {
                callee,
                acc,
                binders,
                where_clauses,
                body,
                ..
            } => self.eval_comprehension(
                &callee.text,
                acc.as_ref(),
                binders,
                where_clauses,
                body,
                scope,
            ),
            // Member appears only as the callee of `k.check(..)` (handled in
            // eval_call) or in type/lock paths; standalone is not a value.
            Expr::Member { .. } | Expr::Duration { .. } => None,
        }
    }

    fn cmp(&self, op: &CmpOp, a: &Val, b: &Val) -> Option<bool> {
        // Equality is byte-wise when either side is bytes, else numeric;
        // ordering and `!=` are numeric (mirroring the lowering's opcode pick).
        if let (CmpOp::Eq, Val::Bytes(x), Val::Bytes(y)) = (op, a, b) {
            return Some(x == y);
        }
        let (x, y) = (as_int(a)?, as_int(b)?);
        Some(match op {
            CmpOp::Lt => x < y,
            CmpOp::Le => x <= y,
            CmpOp::Gt => x > y,
            CmpOp::Ge => x >= y,
            CmpOp::Eq => x == y,
            CmpOp::Ne => x != y,
        })
    }

    fn eval_call(&self, callee: &Expr, args: &[Arg], scope: &[(String, Val)]) -> Option<Val> {
        // key.check(sig): independent boolean from the SHARED signature oracle
        // (the same primitive the interpreter calls; crypto correctness is T5).
        if let Expr::Member { base, member, .. } = callee
            && member.text == "check"
            && args.len() == 1
        {
            let Val::Bytes(key) = self.eval(base, scope)? else {
                return None;
            };
            let Val::Sig(present) = self.eval(&args[0].value, scope)? else {
                return None;
            };
            let sig_bytes: Vec<u8> = if present {
                self.marker.to_vec()
            } else {
                Vec::new()
            };
            return Some(Val::Bool((self.verify_sig)(&key, &sig_bytes)));
        }
        let Expr::Name(f) = callee else { return None };
        let arg = |i: usize| self.eval(&args[i].value, scope);
        match f.text.as_str() {
            "min" if args.len() == 2 => Some(Val::Int(as_int(&arg(0)?)?.min(as_int(&arg(1)?)?))),
            "max" if args.len() == 2 => Some(Val::Int(as_int(&arg(0)?)?.max(as_int(&arg(1)?)?))),
            "abs" if args.len() == 1 => Some(Val::Int(as_int(&arg(0)?)?.checked_abs()?)),
            "int" if args.len() == 1 => arg(0),
            "select" if args.len() == 3 => {
                if truthy(&arg(0)?)? {
                    arg(1)
                } else {
                    arg(2)
                }
            }
            // Hashes and `after` route through Bytes/timelock domains, which
            // the certifier does not enumerate; abstain so the leaf is not
            // falsely certified.
            _ => None,
        }
    }

    fn eval_comprehension(
        &self,
        agg: &str,
        acc: Option<&AccClause>,
        binders: &[Binder],
        where_clauses: &[Expr],
        body: &Expr,
        scope: &[(String, Val)],
    ) -> Option<Val> {
        // Materialize each binder's element list; parallel binders zip.
        let mut lists: Vec<(String, Vec<Val>)> = Vec::new();
        let mut n: Option<usize> = None;
        for b in binders {
            let vals = self.binder_elements(b, scope)?;
            match n {
                None => n = Some(vals.len()),
                Some(m) if m == vals.len() => {}
                _ => return None, // zip mismatch (should be caught by sema)
            }
            lists.push((b.name.text.clone(), vals));
        }
        let n = n.unwrap_or(0);

        let mut acc_val = match agg {
            "sum" | "count" => Val::Int(0),
            "all" => Val::Bool(true),
            "any" => Val::Bool(false),
            "fold" => self.eval(&acc?.init, scope)?,
            _ => return None,
        };

        for i in 0..n {
            let mut inner = scope.to_vec();
            for (name, vals) in &lists {
                inner.push((name.clone(), vals[i].clone()));
            }
            // where-guards conjoin; an element passing none of them is skipped.
            let mut pass = true;
            for w in where_clauses {
                pass = pass && truthy(&self.eval(w, &inner)?)?;
            }
            if !pass {
                continue;
            }
            match agg {
                "count" => {
                    if truthy(&self.eval(body, &inner)?)? {
                        acc_val = Val::Int(as_int(&acc_val)?.checked_add(1)?);
                    }
                }
                "sum" => {
                    acc_val =
                        Val::Int(as_int(&acc_val)?.checked_add(as_int(&self.eval(body, &inner)?)?)?)
                }
                "all" => {
                    acc_val = Val::Bool(truthy(&acc_val)? && truthy(&self.eval(body, &inner)?)?)
                }
                "any" => {
                    acc_val = Val::Bool(truthy(&acc_val)? || truthy(&self.eval(body, &inner)?)?)
                }
                "fold" => {
                    let name = &acc?.name.text;
                    inner.push((name.clone(), acc_val.clone()));
                    acc_val = self.eval(body, &inner)?;
                }
                _ => return None,
            }
        }
        Some(acc_val)
    }

    fn binder_elements(&self, b: &Binder, scope: &[(String, Val)]) -> Option<Vec<Val>> {
        match &b.seq {
            Seq::Range {
                lo, hi, inclusive, ..
            } => {
                let lo = as_int(&self.eval(lo, scope)?)?;
                let hi = as_int(&self.eval(hi, scope)?)?;
                let end = if *inclusive { hi.checked_add(1)? } else { hi };
                if end < lo {
                    return Some(Vec::new());
                }
                Some((lo..end).map(Val::Int).collect())
            }
            Seq::Expr(e) => match self.eval(e, scope)? {
                Val::Array(items) => Some(items),
                _ => None,
            },
        }
    }

    /// Evaluate a whole spend's predicate over the witness: AND of every
    /// `require` item, with `let`s bound left to right. None = abstain (an
    /// unmodeled construct, or an `after` timelock with no context to model it).
    ///
    /// `timelock_ctx` is the spend context an `after(..)` item is evaluated
    /// against (by the same BIP65/BIP112 rules the script uses). `None` means
    /// abstain on any timelock -- the symbolic path, and any leaf whose locks
    /// the caller could not pin to a consistent context.
    fn eval_spend(&self, body: &[Stmt], timelock_ctx: Option<&Context>) -> Option<bool> {
        let mut scope: Vec<(String, Val)> = Vec::new();
        let mut result = true;
        for stmt in body {
            match stmt {
                Stmt::Let { name, value, .. } => {
                    let v = self.eval(value, &scope)?;
                    scope.push((name.text.clone(), v));
                }
                Stmt::Require(req) => {
                    for item in &req.items {
                        // `after(lock)` is a context timelock, not a witness
                        // predicate. Model it against the context if we have
                        // one; otherwise abstain (sound -> Differential).
                        if let Expr::Call { callee, args, .. } = item
                            && matches!(callee.as_ref(), Expr::Name(f) if f.text == "after")
                            && args.len() == 1
                        {
                            let ctx = timelock_ctx?;
                            let (operand, is_rel) = timelock_operand(&args[0].value, self.env)?;
                            result = result && timelock_ok(operand, is_rel, ctx);
                            continue;
                        }
                        result = result && truthy(&self.eval(item, &scope)?)?;
                    }
                }
            }
        }
        Some(result)
    }
}

/// Evaluate a spend's predicate (the independent oracle `⟦·⟧`) at one concrete
/// witness, given as the same `(name, SatValue)` plan that drives
/// `build_witness`. `Some(b)` is the predicate's truth; `None` is an abstain
/// (an unmodeled construct or an `after` timelock). Exposed for `crate::verify::decide`
/// so the full-domain prover reuses the ONE evaluator definition rather than
/// cloning it. `verify_sig`/`marker` must be the same oracle the interpreter
/// uses, so `check` results line up.
pub(crate) fn eval_predicate(
    body: &[Stmt],
    plan: &[(String, SatValue)],
    env: &Env,
    verify_sig: &dyn Fn(&[u8], &[u8]) -> bool,
    marker: &[u8],
    timelock_ctx: Option<&Context>,
) -> Option<bool> {
    let witness: Vec<(String, Val)> = plan
        .iter()
        .map(|(n, s)| (n.clone(), sat_to_val(s)))
        .collect();
    let ev = Ev {
        env,
        witness: &witness,
        verify_sig,
        marker,
    };
    ev.eval_spend(body, timelock_ctx)
}

/// The evaluator's view of a satisfier value. Mirrors `build_witness`'s
/// encoding choices at the value level (a present signature is `Sig(true)`; an
/// `Int` is its number; a `Bool` is a boolean), so the predicate sees exactly
/// the witness the script is run on.
fn sat_to_val(s: &SatValue) -> Val {
    match s {
        SatValue::Int(n) => Val::Int(*n as i128),
        SatValue::Bool(b) => Val::Bool(*b),
        SatValue::Bytes(b) => Val::Bytes(b.clone()),
        SatValue::Sig(p) => Val::Sig(*p),
        SatValue::Array(items) => Val::Array(items.iter().map(sat_to_val).collect()),
    }
}

// --- bounded-Int support ---

/// Visit every sub-expression of `e` (pre-order), for constant collection.
fn walk_exprs(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    match e {
        Expr::Member { base, .. } => walk_exprs(base, f),
        Expr::Index { base, index, .. } => {
            walk_exprs(base, f);
            walk_exprs(index, f);
        }
        Expr::Unary { operand, .. } => walk_exprs(operand, f),
        Expr::Binary { lhs, rhs, .. } => {
            walk_exprs(lhs, f);
            walk_exprs(rhs, f);
        }
        Expr::Compare { first, rest, .. } => {
            walk_exprs(first, f);
            for (_, e) in rest {
                walk_exprs(e, f);
            }
        }
        Expr::In { value, lo, hi, .. } => {
            walk_exprs(value, f);
            walk_exprs(lo, f);
            walk_exprs(hi, f);
        }
        Expr::Call { callee, args, .. } => {
            walk_exprs(callee, f);
            for a in args {
                walk_exprs(&a.value, f);
            }
        }
        Expr::TypedCtor { args, .. } => {
            for a in args {
                walk_exprs(&a.value, f);
            }
        }
        Expr::ArrayLit { elems, .. } => {
            for e in elems {
                walk_exprs(e, f);
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
                walk_exprs(&a.init, f);
            }
            for b in binders {
                match &b.seq {
                    Seq::Expr(e) => walk_exprs(e, f),
                    Seq::Range { lo, hi, .. } => {
                        walk_exprs(lo, f);
                        walk_exprs(hi, f);
                    }
                }
            }
            for w in where_clauses {
                walk_exprs(w, f);
            }
            walk_exprs(body, f);
        }
        Expr::Int { .. }
        | Expr::Str { .. }
        | Expr::Bool { .. }
        | Expr::Duration { .. }
        | Expr::Name(_) => {}
    }
}

/// The enumeration window for an Int parameter: a symmetric range covering
/// every integer constant in the spend. Every comparison breakpoint of an
/// affine / min / max / abs predicate has magnitude at most that of the
/// constants it combines, so `[-span, span]` with `span = 2*max|const| + 4`
/// contains them all; values beyond it only ever sit in a constant-truth tail.
/// None when the spend names no constant (nothing to bound) or the window is
/// degenerate.
fn int_window(
    body: &[Stmt],
    env: &Env,
    verify_sig: &dyn Fn(&[u8], &[u8]) -> bool,
    marker: &[u8],
) -> Option<(i128, i128)> {
    let mut max_abs: u128 = 0;
    {
        let ev = Ev {
            env,
            witness: &[],
            verify_sig,
            marker,
        };
        let mut visit = |e: &Expr| {
            if let Some(Val::Int(n)) = ev.eval(e, &[]) {
                max_abs = max_abs.max(n.unsigned_abs());
            }
        };
        for stmt in body {
            match stmt {
                Stmt::Let { value, .. } => walk_exprs(value, &mut visit),
                Stmt::Require(req) => {
                    for item in &req.items {
                        walk_exprs(item, &mut visit);
                    }
                }
            }
        }
    }
    if max_abs == 0 {
        return None;
    }
    let span = (2 * max_abs as i128 + 4).min(MACHINE_MAX);
    Some((-span, span))
}

fn ty_has_int(ty: &Ty) -> bool {
    match ty {
        Ty::Int => true,
        Ty::Array(elem, _) => ty_has_int(elem),
        _ => false,
    }
}

// --- timelocks ---

/// BIP68 relative-lock type flag (bit 22): 512-second units vs blocks.
const TL_TYPE_FLAG: i64 = 1 << 22;
/// BIP65 height/time split: below is a block height, at/above a unix time.
const TL_LOCKTIME_THRESHOLD: i64 = 500_000_000;

/// The operand and CSV/CLTV selector an `after(<arg>)` lowers to, computed
/// EXACTLY as `lower::lower_after` emits it so the certifier's boundary contexts
/// line up with the script's real operand. `(operand, is_rel)`; `None` if the
/// argument does not const-evaluate to a lock.
fn timelock_operand(arg: &Expr, env: &Env) -> Option<(i64, bool)> {
    match eval_in_env(arg, env).0? {
        ConstValue::LockAbs(LockAbs::Height(h)) => Some((i64::from(h), false)),
        ConstValue::LockAbs(LockAbs::Time(t)) => Some((i64::from(t), false)),
        ConstValue::LockRel(LockRel::Blocks(b)) => Some((i64::from(b), true)),
        ConstValue::LockRel(LockRel::Units(u)) => Some((i64::from(u) | TL_TYPE_FLAG, true)),
        _ => None,
    }
}

/// Every `after(..)` timelock in a leaf, as `(operand, is_rel)`. `Some(vec)`
/// (empty if there are none); `None` if any timelock arg is not a const lock,
/// so the leaf must not be modelled (the caller falls back to abstaining).
fn leaf_timelocks(body: &[Stmt], env: &Env) -> Option<Vec<(i64, bool)>> {
    let mut locks = Vec::new();
    for stmt in body {
        let Stmt::Require(req) = stmt else { continue };
        for item in &req.items {
            let Expr::Call { callee, args, .. } = item else {
                continue;
            };
            if matches!(callee.as_ref(), Expr::Name(f) if f.text == "after") && args.len() == 1 {
                locks.push(timelock_operand(&args[0].value, env)?);
            }
        }
    }
    Some(locks)
}

/// Construct a spend context with the given lock fields, reusing the base
/// context's signature oracle and a CSV-eligible tx version.
fn ctx_with<'a>(base: &Context<'a>, locktime: u32, sequence: u32) -> Context<'a> {
    Context {
        locktime,
        sequence,
        tx_version: 2,
        verify_sig: base.verify_sig,
    }
}

/// The contexts to certify a timelocked leaf over: one that JUST-SATISFIES every
/// timelock, plus, per lock field, one that JUST-VIOLATES it (so the gate is
/// proven enforced, not merely the accept path). Timelocks are monotone
/// thresholds, so the boundary pair characterizes the whole gate.
///
/// Returns `None` when a single context cannot satisfy every lock -- two
/// relative locks of different units (blocks vs 512s), or two absolute locks
/// straddling the height/time split -- so the caller abstains rather than prove
/// the leaf over an inconsistent context. An empty `locks` yields the base
/// context unchanged (no timelock to model).
fn boundary_contexts<'a>(locks: &[(i64, bool)], base: &Context<'a>) -> Option<Vec<Context<'a>>> {
    if locks.is_empty() {
        return Some(vec![ctx_with(base, base.locktime, base.sequence)]);
    }
    // CLTV (absolute) operands drive nLockTime; CSV (relative) drive nSequence.
    // Each field admits a single type, or one context cannot satisfy all of it.
    let cltv: Vec<i64> = locks.iter().filter(|(_, r)| !r).map(|(o, _)| *o).collect();
    let csv: Vec<i64> = locks.iter().filter(|(_, r)| *r).map(|(o, _)| *o).collect();
    if cltv.iter().chain(&csv).any(|o| *o < 0) {
        return None;
    }
    let cltv_max = match cltv.split_first() {
        None => None,
        Some((&h, rest)) => {
            let is_time = h >= TL_LOCKTIME_THRESHOLD;
            if rest
                .iter()
                .any(|o| (*o >= TL_LOCKTIME_THRESHOLD) != is_time)
            {
                return None; // height and time absolute locks cannot coexist
            }
            Some(cltv.iter().copied().max().unwrap())
        }
    };
    let csv_max = match csv.split_first() {
        None => None,
        Some((&first, rest)) => {
            let ty = first & TL_TYPE_FLAG;
            if rest.iter().any(|o| (*o & TL_TYPE_FLAG) != ty) {
                return None; // block-relative and time-relative locks cannot coexist
            }
            Some(csv.iter().copied().max().unwrap())
        }
    };

    // Satisfying context. No CSV -> a sequence that keeps CLTV enabled
    // (!= 0xffffffff) without engaging any relative lock.
    let sat_lt = cltv_max.unwrap_or(0) as u32;
    let sat_seq = csv_max.map_or(0xffff_fffe, |m| m as u32);
    let mut out = vec![ctx_with(base, sat_lt, sat_seq)];

    // Just-violating contexts: drop the effective threshold of one field by one.
    if let Some(m) = cltv_max
        && m >= 1
    {
        out.push(ctx_with(base, (m - 1) as u32, sat_seq));
    }
    if let Some(m) = csv_max
        && (m & !TL_TYPE_FLAG) >= 1
    {
        out.push(ctx_with(base, sat_lt, (m - 1) as u32));
    }
    Some(out)
}

// --- the certifier ---

/// The verification verdict for one spend leaf.
#[derive(Debug, Clone)]
pub enum CertStatus {
    /// Exhaustive three-way agreement over the complete finite witness domain:
    /// the optimizer preserved behavior AND the naive lowering implements the
    /// predicate, for every witness. `checked` is the domain size.
    Certified { checked: u64 },
    /// The optimizer's behavior was checked against the naive lowering over the
    /// finite domain (T2 held), but the predicate evaluator abstained on a
    /// construct, so T1 is not asserted here. Honest, not a failure.
    Differential { checked: u64, reason: String },
    /// Three-way agreement held over every witness with the Int parameter(s)
    /// enumerated across `[lo, hi]` -- a window covering every integer constant
    /// in the spend (so every comparison breakpoint). Strictly weaker than
    /// Certified: it does not assert agreement for Int values outside the
    /// window (a full all-Int proof needs SMT, Phase 3 proper). Never a claim
    /// of exhaustiveness over the unbounded domain.
    BoundedChecked { checked: u64, lo: i128, hi: i128 },
    /// The witness domain is unbounded or larger than the cap; no exhaustive
    /// check was run. Routes to SMT / sampled differential in a later phase.
    Unbounded { reason: String },
    /// A FULL-DOMAIN proof by the symbolic decision procedure (`crate::verify::decide`),
    /// for leaves whose domain is too large to enumerate: equivalence is
    /// established over the COMPLETE domain (not a window, not a sample), so this
    /// is strictly stronger than BoundedChecked and closes the leaf for Phase 3.
    /// `kind` says which engine proved it and exactly what was proven.
    Proven { kind: ProvenKind },
    /// A real divergence: report and refuse. `detail` pinpoints the witness.
    Failed { detail: String },
}

/// What a symbolic `Proven` verdict actually established (see `crate::verify::decide`).
#[derive(Debug, Clone)]
pub enum ProvenKind {
    /// Engine A (single Int witness var): T1 (naive ⟺ predicate) AND T2 (opt ⟺
    /// naive) over EVERY CScriptNum value of the Int param, by breakpoint-cell
    /// decomposition of the machine domain. `breakpoints` is the cell count.
    FullInt { var: String, breakpoints: usize },
    /// Engine B (no Int var): T1 AND T2 over the full opaque-witness domain --
    /// EVERY assignment of the `atoms` free witness symbols (for boolean atoms
    /// that is `2^atoms`; for byte/hash atoms it is the whole value space) -- by
    /// structural equality of the symbolic stack functions decoded from the
    /// actual script bytes.
    FullSymbolic { atoms: usize },
    /// Engine B, partial: T2 (opt ⟺ naive) proven over the full domain -- the
    /// optimizer is certified out of the TCB for this leaf -- but the predicate
    /// evaluator could not be symbolically matched, so T1 stays differential.
    T2OnlySymbolic { atoms: usize, t1_reason: String },
}

#[derive(Debug, Clone)]
pub struct LeafReport {
    pub name: String,
    pub status: CertStatus,
}

impl LeafReport {
    pub fn is_failure(&self) -> bool {
        matches!(self.status, CertStatus::Failed { .. })
    }
}

/// The funding-safety tier of a verdict. The driver refuses to emit a fundable
/// artifact (an address, a lockfile, a verify) unless every leaf is `Proven`,
/// or the operator explicitly accepts the `Unproven` leaves with
/// `--allow-unproven`. A `Divergence` is never fundable -- not even with the
/// override -- because the compile is known to be wrong.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Assurance {
    /// T1 (lowering implements the predicate) AND T2 (optimizer preserves the
    /// naive behaviour) were both established over the COMPLETE witness domain.
    Proven,
    /// Honestly not fully proven: a differential-only T1 (the predicate
    /// evaluator abstained on a construct), an Int check over a window only, an
    /// optimizer-only symbolic proof, or an unbounded domain. Note the optimizer
    /// (T2) is still proven for the differential / T2-only cases -- it is the
    /// independent predicate proof (T1) that is incomplete.
    Unproven,
    /// A concrete witness was found where the optimized script, the naive
    /// script, and/or the predicate disagree. The compile is known-wrong.
    Divergence,
}

impl CertStatus {
    /// Classify this verdict into its funding-safety tier.
    pub fn assurance(&self) -> Assurance {
        use ProvenKind::{FullInt, FullSymbolic, T2OnlySymbolic};
        match self {
            CertStatus::Failed { .. } => Assurance::Divergence,
            CertStatus::Certified { .. } => Assurance::Proven,
            CertStatus::Proven {
                kind: FullInt { .. } | FullSymbolic { .. },
            } => Assurance::Proven,
            CertStatus::Proven {
                kind: T2OnlySymbolic { .. },
            }
            | CertStatus::Differential { .. }
            | CertStatus::BoundedChecked { .. }
            | CertStatus::Unbounded { .. } => Assurance::Unproven,
        }
    }
}

const DEFAULT_DOMAIN_CAP: u128 = 1 << 20;

fn resolve_len(len: &Len, env: &Env) -> Option<usize> {
    match len {
        Len::Lit(n) => Some(*n as usize),
        Len::Named(name) => match env.get(name) {
            Some(ConstValue::Int(v)) if *v >= 0 => Some(*v as usize),
            _ => None,
        },
    }
}

/// The finite choices for one parameter as (witness encoding, evaluator value)
/// pairs, or None if the parameter's domain is not finitely enumerable.
/// `int_win`, when present, bounds Int parameters to an enumerable window
/// (a bounded-checked, not exhaustive, treatment of the Int domain).
fn param_domain(ty: &Ty, env: &Env, int_win: Option<(i128, i128)>) -> Option<Vec<(SatValue, Val)>> {
    match ty {
        Ty::Bool => Some(vec![
            (SatValue::Bool(false), Val::Bool(false)),
            (SatValue::Bool(true), Val::Bool(true)),
        ]),
        Ty::Signature => Some(vec![
            (SatValue::Sig(false), Val::Sig(false)),
            (SatValue::Sig(true), Val::Sig(true)),
        ]),
        Ty::Int => {
            let (lo, hi) = int_win?;
            let count = (hi - lo).checked_add(1)?;
            if count <= 0 || count as u128 > DEFAULT_DOMAIN_CAP {
                return None;
            }
            Some(
                (lo..=hi)
                    .map(|v| (SatValue::Int(v as i64), Val::Int(v)))
                    .collect(),
            )
        }
        Ty::Array(elem, len) => {
            let n = resolve_len(len, env)?;
            let base = param_domain(elem, env, int_win)?; // element choices
            if n > 24 {
                return None; // 2^24 element-combos guard before the cap check
            }
            let total = base.len().checked_pow(n as u32)?;
            if total as u128 > DEFAULT_DOMAIN_CAP {
                return None;
            }
            // Enumerate every length-n combination of element choices.
            let mut out: Vec<(SatValue, Val)> = Vec::with_capacity(total);
            for combo in 0..total {
                let mut c = combo;
                let mut sats = Vec::with_capacity(n);
                let mut vals = Vec::with_capacity(n);
                for _ in 0..n {
                    let (s, v) = &base[c % base.len()];
                    c /= base.len();
                    sats.push(s.clone());
                    vals.push(v.clone());
                }
                out.push((SatValue::Array(sats), Val::Array(vals)));
            }
            Some(out)
        }
        // Int (unbounded CScriptNum domain), Bytes/Hash/PublicKey: not finitely
        // enumerable for an exhaustive proof here.
        _ => None,
    }
}

/// Certify one spend leaf: enumerate its finite witness domain and require the
/// independent predicate, the naive script, and the optimized script to agree
/// on every witness. The verdict distinguishes a real failure from an honest
/// abstain (evaluator) and from an unbounded domain. The evaluator and the
/// interpreter share one signature oracle, `ctx.verify_sig`, so a `check`
/// result is consistent between them by construction.
fn certify_leaf(
    body: &[Stmt],
    sig: &SpendSig,
    env: &Env,
    naive: &LoweredLeaf,
    opt: &LoweredLeaf,
    marker: &[u8],
    ctx: &Context,
) -> CertStatus {
    // Strictly-additive full-domain upgrade: the symbolic decision procedure
    // (`crate::verify::decide`) can PROVE a leaf over its complete domain where
    // enumeration only windows it (BoundedChecked) or gives up (Unbounded). It
    // returns Some only on a real proof, operating on the actual opt bytes, so
    // the worst case of any bug there is reverting to the verdict below. Never
    // invoked on a leaf that already Failed (those return earlier).
    let upgrade = || {
        crate::verify::decide::try_prove(body, sig, env, naive, opt, marker, ctx)
            .map(|kind| CertStatus::Proven { kind })
    };

    // An Int window (covering every constant the spend names) lets Int params
    // be bounded-checked; without constants to bound them, they stay unbounded.
    let win = int_window(body, env, ctx.verify_sig, marker);
    let has_int = sig.params.iter().any(|p| ty_has_int(&p.ty));

    // Per-parameter finite domains; bail to Unbounded if any is not finite.
    let mut domains: Vec<Vec<(SatValue, Val)>> = Vec::new();
    for p in &sig.params {
        match param_domain(&p.ty, env, win) {
            Some(d) => domains.push(d),
            None => {
                let why = if ty_has_int(&p.ty) {
                    format!(
                        "Int parameter `{}` is unbounded (no constants to window, or window over cap); needs SMT",
                        p.name
                    )
                } else {
                    format!("parameter `{}` has a non-finite witness domain", p.name)
                };
                // The domain is not finitely enumerable -- but the symbolic
                // procedure may still prove it over the full domain (Engine B
                // on an all-Bool/Sig/opaque leaf, e.g. cat_bounty's 2^784).
                return upgrade().unwrap_or(CertStatus::Unbounded { reason: why });
            }
        }
    }
    let mut total: u128 = 1;
    for d in &domains {
        total = match total.checked_mul(d.len() as u128) {
            Some(t) if t <= DEFAULT_DOMAIN_CAP => t,
            _ => {
                let reason = format!("witness domain exceeds the cap of {DEFAULT_DOMAIN_CAP}");
                return upgrade().unwrap_or(CertStatus::Unbounded { reason });
            }
        };
    }

    let mut eval_abstained: Option<String> = None;

    // Timelock leaves are certified over BOUNDARY contexts: one that just
    // satisfies every `after(..)`, plus one that just violates each lock field
    // -- so the gate is proven ENFORCED (an omitted or short lock diverges at
    // the violating context), not merely that the accept path is correct. A
    // leaf with no timelock, or whose locks cannot pin a single consistent
    // context, certifies over the base context alone with `after` abstaining.
    let (contexts, model_tl) = match leaf_timelocks(body, env) {
        Some(locks) if !locks.is_empty() => match boundary_contexts(&locks, ctx) {
            Some(cs) => (cs, true),
            None => (vec![ctx_with(ctx, ctx.locktime, ctx.sequence)], false),
        },
        _ => (vec![ctx_with(ctx, ctx.locktime, ctx.sequence)], false),
    };

    for (ci, ctx_c) in contexts.iter().enumerate() {
        for combo in 0..total {
            // Mixed-radix decode of `combo` into one choice per parameter.
            let mut c = combo;
            let mut plan: Vec<(String, SatValue)> = Vec::with_capacity(sig.params.len());
            let mut witness: Vec<(String, Val)> = Vec::with_capacity(sig.params.len());
            for (p, dom) in sig.params.iter().zip(&domains) {
                let idx = (c % dom.len() as u128) as usize;
                c /= dom.len() as u128;
                let (s, v) = &dom[idx];
                plan.push((p.name.clone(), s.clone()));
                witness.push((p.name.clone(), v.clone()));
            }

            // Same witness stack drives both scripts (the optimizer preserves
            // witness order; if it ever did not, build_witness would differ).
            let naive_stack = match build_witness(naive, sig, env, &plan, marker) {
                Ok(s) => s,
                Err(e) => {
                    return CertStatus::Failed {
                        detail: format!("naive witness: {e}"),
                    };
                }
            };
            let opt_stack = match build_witness(opt, sig, env, &plan, marker) {
                Ok(s) => s,
                Err(e) => {
                    return CertStatus::Failed {
                        detail: format!("opt witness: {e}"),
                    };
                }
            };
            if naive_stack != opt_stack {
                return CertStatus::Failed {
                    detail: format!("witness order diverged at combo {combo}"),
                };
            }

            let naive_ok = execute(&naive.script, &naive_stack, ctx_c).is_ok();
            let opt_ok = execute(&opt.script, &opt_stack, ctx_c).is_ok();
            if naive_ok != opt_ok {
                return CertStatus::Failed {
                    detail: format!(
                        "T2 (optimizer) divergence: naive={naive_ok} opt={opt_ok} at combo {combo}, context {ci}"
                    ),
                };
            }

            // T1: the independent predicate must match the naive script, where
            // the evaluator can speak (modelling `after` against this context).
            // If it abstains, keep checking T2 to the end.
            let ev = Ev {
                env,
                witness: &witness,
                verify_sig: ctx_c.verify_sig,
                marker,
            };
            match ev.eval_spend(body, model_tl.then_some(ctx_c)) {
                Some(pred) => {
                    if pred != naive_ok {
                        return CertStatus::Failed {
                            detail: format!(
                                "T1 (lowering) divergence: predicate={pred} script={naive_ok} at combo {combo}, context {ci}"
                            ),
                        };
                    }
                }
                None => {
                    if eval_abstained.is_none() {
                        eval_abstained =
                            Some("predicate evaluator abstained on a construct".into());
                    }
                }
            }
        }
    }

    // `checked` is the WITNESS-domain size (the boundary contexts are a proof
    // mechanism for the timelock gate, not extra witnesses), so the count stays
    // comparable to non-timelock leaves and to the fuzzer's domain enumeration.
    let base = match (eval_abstained, has_int, win) {
        (Some(reason), _, _) => CertStatus::Differential {
            checked: total as u64,
            reason,
        },
        // An Int param was enumerated over a window, not its whole domain:
        // strictly weaker than exhaustive, reported honestly.
        (None, true, Some((lo, hi))) => CertStatus::BoundedChecked {
            checked: total as u64,
            lo,
            hi,
        },
        (None, _, _) => CertStatus::Certified {
            checked: total as u64,
        },
    };
    // A windowed (BoundedChecked) or evaluator-abstained (Differential) leaf may
    // be upgradable to a full-domain proof; a Certified leaf is already
    // exhaustive and a Failed already returned. The upgrade is sound-or-nothing.
    if matches!(
        base,
        CertStatus::BoundedChecked { .. } | CertStatus::Differential { .. }
    ) && let Some(proven) = upgrade()
    {
        return proven;
    }
    base
}

/// Certify every spend of a contract. `naive` are the lowering outputs;
/// `optimized` the post-optimize leaves; both keyed by spend name. `marker` is
/// the present-signature sentinel; `ctx` carries the spend context, including
/// `ctx.verify_sig` -- the one signature oracle shared by the evaluator and
/// the interpreter.
pub fn certify(
    contract: &Contract,
    info: &ContractInfo,
    env: &Env,
    naive: &[LoweredLeaf],
    optimized: &[LoweredLeaf],
    marker: &[u8],
    ctx: &Context,
) -> Vec<LeafReport> {
    let mut reports = Vec::new();
    for item in &contract.items {
        let Item::Spend(s) = item else { continue };
        let Some(sig) = info.spends.iter().find(|x| x.name == s.name.text) else {
            continue;
        };
        let (Some(nl), Some(ol)) = (
            naive.iter().find(|l| l.name == s.name.text),
            optimized.iter().find(|l| l.name == s.name.text),
        ) else {
            continue;
        };
        let status = certify_leaf(&s.body, sig, env, nl, ol, marker, ctx);
        reports.push(LeafReport {
            name: s.name.text.clone(),
            status,
        });
    }
    reports
}
