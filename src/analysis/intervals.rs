//! The interval engine: bounds checking. If it compiles, it cannot overflow.
//!
//! Forward abstract interpretation over spend bodies, run at instantiation
//! (extern values bound, so const data carries exact intervals).
//!
//! # The runtime-node rule
//!
//! Every value carries an interval and an exactness bit. Const data is
//! exact (`[v, v]`); exactness propagates through all-exact operations. A node
//! with at least one non-exact operand is a runtime node: its operands are
//! pushed on-chain, so operands must fit the machine domain M = +/-(2^31 - 1),
//! and its result must fit M (5-byte values are unrepresentable in well-typed
//! programs). All-exact nodes fold away (constant folding is always-on), so
//! their intermediates may exceed M.
//!
//! # Narrowing
//!
//! `require` items narrow named facts forward, in order: comparisons, chains,
//! and `in`-ranges intersect a name's interval; `select` arms apply the
//! condition (and its negation); `where` guards narrow comprehension bodies.
//! An empty intersection is an infeasibility error. Narrowed facts are
//! conditional on the checks holding, which is precisely the guarantee made:
//! honest-satisfier executions satisfy every check, so no overflow occurs;
//! dishonest witnesses are consensus-rejected regardless of failure mode.
//!
//! # Comprehensions
//!
//! Analyzed per element: binders over instantiated const arrays carry each
//! element's exact value (the classifier's score interval folds exactly from
//! the real weights) and every partial aggregate is checked against M (each
//! on-chain `OP_ADD` must fit, not just the total). Guards with unknown truth
//! contribute `hull(body, identity)`.

use std::collections::BTreeMap;

use crate::analysis::consteval::{ConstValue, Env, MACHINE_MAX};
use crate::analysis::sema::parse_int_text;
use crate::diagnostics::Diagnostic;
use crate::syntax::ast::*;
use crate::syntax::span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interval {
    pub lo: i128,
    pub hi: i128,
}

impl Interval {
    pub fn exact(v: i128) -> Interval {
        Interval { lo: v, hi: v }
    }
    /// The machine domain M.
    pub fn machine() -> Interval {
        Interval {
            lo: -MACHINE_MAX,
            hi: MACHINE_MAX,
        }
    }
    pub fn fits_machine(self) -> bool {
        self.lo >= -MACHINE_MAX && self.hi <= MACHINE_MAX
    }
    fn hull(self, other: Interval) -> Interval {
        Interval {
            lo: self.lo.min(other.lo),
            hi: self.hi.max(other.hi),
        }
    }
    fn intersect(self, other: Interval) -> Option<Interval> {
        let lo = self.lo.max(other.lo);
        let hi = self.hi.min(other.hi);
        (lo <= hi).then_some(Interval { lo, hi })
    }
}

/// Abstract value: interval + exactness for Ints; minimal facts otherwise.
#[derive(Debug, Clone)]
enum Abs {
    Int {
        iv: Interval,
        exact: bool,
    },
    /// `value` is Some when statically known (literals, folded comparisons).
    Bool {
        value: Option<bool>,
    },
    /// Bytes, hashes, keys, signatures: no numeric facts.
    Bytes,
    Lock,
    Check,
    Array {
        elems: Elems,
    },
    /// A binding whose value already failed analysis. Propagates silently:
    /// one mistake, one message; downstream uses never cascade.
    Poison,
}

#[derive(Debug, Clone)]
enum Elems {
    /// Instantiated const arrays: one abstract value per element (exact).
    Exact(Vec<Abs>),
    /// Witness arrays: a uniform element abstraction + static length.
    Uniform(usize, Box<Abs>),
}

impl Elems {
    fn len(&self) -> usize {
        match self {
            Elems::Exact(v) => v.len(),
            Elems::Uniform(n, _) => *n,
        }
    }
    fn get(&self, i: usize) -> Abs {
        match self {
            Elems::Exact(v) => v[i].clone(),
            Elems::Uniform(_, a) => (**a).clone(),
        }
    }
}

/// The truth of `l op r` given the operand intervals: `Some(true)` if it
/// holds for every value in range, `Some(false)` if it never holds, `None`
/// if it depends on the witness. Equality is left undecided here.
fn cmp_truth(l: Interval, op: CmpOp, r: Interval) -> Option<bool> {
    match op {
        CmpOp::Lt => {
            if l.hi < r.lo {
                Some(true)
            } else if l.lo >= r.hi {
                Some(false)
            } else {
                None
            }
        }
        CmpOp::Le => {
            if l.hi <= r.lo {
                Some(true)
            } else if l.lo > r.hi {
                Some(false)
            } else {
                None
            }
        }
        CmpOp::Gt => {
            if l.lo > r.hi {
                Some(true)
            } else if l.hi <= r.lo {
                Some(false)
            } else {
                None
            }
        }
        CmpOp::Ge => {
            if l.lo >= r.hi {
                Some(true)
            } else if l.hi < r.lo {
                Some(false)
            } else {
                None
            }
        }
        CmpOp::Eq | CmpOp::Ne => None,
    }
}

/// Per-`let` proven intervals, for the report (and eventually the funding
/// report) and the lowering.
#[derive(Debug, Clone, Default)]
pub struct Report {
    /// (spend, let name, interval)
    pub lets: Vec<(String, String, Interval)>,
    /// Spans of `require` items proven always-true under the narrowed domains,
    /// so the optimizer can drop the dead check. Recorded at the point each
    /// item is evaluated, after earlier items in the spend have narrowed.
    pub dead_requires: Vec<Span>,
}

/// Run the engine over every spend. Requires the instantiated `env`.
pub fn analyze(contract: &Contract, env: &Env) -> (Vec<Diagnostic>, Report) {
    let mut eng = Engine {
        env,
        named_lens: collect_named_lens(env),
        diags: Vec::new(),
        report: Report::default(),
        scope: Vec::new(),
        spend: String::new(),
    };
    for item in &contract.items {
        if let Item::Spend(s) = item {
            eng.spend(s);
        }
    }
    (eng.diags, eng.report)
}

fn collect_named_lens(env: &Env) -> BTreeMap<String, usize> {
    let mut m = BTreeMap::new();
    for (k, v) in env {
        if let ConstValue::Int(n) = v
            && *n >= 0
        {
            m.insert(k.clone(), *n as usize);
        }
    }
    m
}

struct Engine<'a> {
    env: &'a Env,
    /// Int consts usable as array lengths (`[T; N]`).
    named_lens: BTreeMap<String, usize>,
    diags: Vec<Diagnostic>,
    report: Report,
    scope: Vec<(String, Abs)>,
    spend: String,
}

impl<'a> Engine<'a> {
    fn error(&mut self, code: &'static str, msg: impl Into<String>, span: Span) {
        self.diags.push(Diagnostic::error(code, msg, span));
    }

    // --- walking ---

    fn spend(&mut self, s: &Spend) {
        self.scope.clear();
        self.spend = s.name.text.clone();
        for p in &s.params {
            let abs = self.param_default(&p.ty);
            self.scope.push((p.name.text.clone(), abs));
        }
        for stmt in &s.body {
            match stmt {
                Stmt::Let { name, value, .. } => {
                    // On failure the name still binds (poisoned) so later
                    // statements don't cascade with "no fact" noise.
                    let abs = self.expr(value).unwrap_or(Abs::Poison);
                    if let Abs::Int { iv, .. } = &abs {
                        self.report
                            .lets
                            .push((self.spend.clone(), name.text.clone(), *iv));
                    }
                    self.scope.push((name.text.clone(), abs));
                }
                Stmt::Require(req) => {
                    for item in &req.items {
                        if let Ok(abs) = self.expr(item) {
                            if matches!(abs, Abs::Bool { value: Some(true) }) {
                                self.report.dead_requires.push(item.span());
                            }
                            self.narrow(item, true);
                        }
                    }
                }
            }
        }
    }

    /// The witness-default abstraction for a parameter type: an `Int`
    /// parameter is the full machine domain until narrowed.
    fn param_default(&mut self, ty: &Type) -> Abs {
        match &ty.kind {
            TypeKind::Array { elem, len } => {
                let elem_abs = self.param_default(elem);
                let n = match len.as_ref() {
                    Expr::Int { text, .. } => parse_int_text(text).map(|v| v as usize).unwrap_or(0),
                    Expr::Name(n) => self.named_lens.get(&n.text).copied().unwrap_or(0),
                    _ => 0,
                };
                Abs::Array {
                    elems: Elems::Uniform(n, Box::new(elem_abs)),
                }
            }
            TypeKind::Path { segments, .. } => match segments[0].text.as_str() {
                "Int" => Abs::Int {
                    iv: Interval::machine(),
                    exact: false,
                },
                "Bool" => Abs::Bool { value: None },
                _ => Abs::Bytes, // Bytes, Hash, PublicKey, Signature
            },
        }
    }

    fn lookup(&self, name: &str) -> Option<Abs> {
        if let Some((_, a)) = self.scope.iter().rev().find(|(n, _)| n == name) {
            return Some(a.clone());
        }
        self.env.get(name).map(const_to_abs)
    }

    fn set_fact(&mut self, name: &str, abs: Abs) {
        if let Some((_, slot)) = self.scope.iter_mut().rev().find(|(n, _)| n == name) {
            *slot = abs;
        }
    }

    // --- abstract evaluation ---

    /// Evaluate an arithmetic operand: Int interval, with Bool widened to
    /// [0,1]. Returns (interval, exact, span).
    fn as_iv(&mut self, e: &Expr) -> Result<(Interval, bool), ()> {
        match self.expr(e)? {
            Abs::Int { iv, exact } => Ok((iv, exact)),
            Abs::Bool { value: Some(b) } => Ok((Interval::exact(b as i128), true)),
            Abs::Bool { value: None } => Ok((Interval { lo: 0, hi: 1 }, false)),
            Abs::Poison => Err(()), // already diagnosed at its source
            other => {
                let (msg, span) = (
                    format!("expected an integer here, found {}", kind_name(&other)),
                    e.span(),
                );
                self.error("bounds/type", msg, span);
                Err(())
            }
        }
    }

    /// Enforce the runtime-node rule on one operand.
    fn operand_fits(&mut self, iv: Interval, span: Span) -> Result<(), ()> {
        if iv.fits_machine() {
            Ok(())
        } else {
            self.error(
                "bounds/operand",
                format!(
                    "this value is pushed on-chain but cannot fit the 4-byte CScriptNum \
                     domain ±{MACHINE_MAX}: proven range [{}, {}]",
                    iv.lo, iv.hi
                ),
                span,
            );
            Err(())
        }
    }

    /// Enforce result-fit on a runtime node, with the backward-solve
    /// suggestion for the canonical witness shapes.
    fn result_fits(&mut self, iv: Interval, node_span: Span, operands: &[&Expr]) -> Result<(), ()> {
        if iv.fits_machine() {
            return Ok(());
        }
        // Suggestion: if a full-domain witness name feeds this node, the
        // half-split bound is always sufficient for one add/sub level.
        let mut suggestion = String::new();
        for op in operands {
            if let Expr::Name(n) = op
                && let Some(Abs::Int { iv, exact: false }) = self.lookup(&n.text)
                && iv == Interval::machine()
            {
                suggestion = format!(
                    " - e.g. `require {0} in -(pow(2, 30) - 1)..=pow(2, 30) - 1` \
                             (or your real domain, which is better)",
                    n.text
                );
                break;
            }
        }
        self.diags.push(
            Diagnostic::error(
                "bounds/overflow",
                format!(
                    "this result can reach [{}, {}], outside the 4-byte CScriptNum domain ±{MACHINE_MAX}",
                    iv.lo, iv.hi
                ),
                node_span,
            )
            .with_help(format!("bound the witness inputs with `require`{suggestion}")),
        );
        Err(())
    }

    fn expr(&mut self, e: &Expr) -> Result<Abs, ()> {
        match e {
            Expr::Int { text, span } => match parse_int_text(text) {
                Some(v) if v <= i128::MAX as u128 => Ok(Abs::Int {
                    iv: Interval::exact(v as i128),
                    exact: true,
                }),
                _ => {
                    self.error(
                        "bounds/overflow",
                        "integer literal exceeds 128-bit precision",
                        *span,
                    );
                    Err(())
                }
            },
            Expr::Bool { value, .. } => Ok(Abs::Bool {
                value: Some(*value),
            }),
            Expr::Str { .. } | Expr::Duration { .. } => Ok(Abs::Bytes), // ctor args (sema-validated)
            Expr::Name(n) => self.lookup(&n.text).ok_or(()).map_err(|()| {
                // sema guarantees resolution; defensive.
                self.error(
                    "bounds/unresolved",
                    format!("`{}` has no fact", n.text),
                    n.span,
                );
            }),
            Expr::Unary { op, operand, span } => match op {
                UnaryOp::Not => {
                    let abs = self.expr(operand)?;
                    match abs {
                        Abs::Bool { value } => Ok(Abs::Bool {
                            value: value.map(|b| !b),
                        }),
                        _ => Ok(Abs::Bool { value: None }),
                    }
                }
                UnaryOp::Neg => {
                    let (iv, exact) = self.as_iv(operand)?;
                    let result = Interval {
                        lo: iv.hi.saturating_neg(),
                        hi: iv.lo.saturating_neg(),
                    };
                    if !exact {
                        self.operand_fits(iv, operand.span())?;
                        self.result_fits(result, *span, &[operand])?;
                    }
                    Ok(Abs::Int { iv: result, exact })
                }
            },
            Expr::Binary { op, lhs, rhs, span } => {
                let (l, le) = self.as_iv(lhs)?;
                let (r, re) = self.as_iv(rhs)?;
                let exact = le && re;
                let result = match op {
                    BinaryOp::Add => Interval {
                        lo: l.lo.checked_add(r.lo).ok_or_else(|| {
                            self.error(
                                "bounds/overflow",
                                "exceeds 128-bit analysis precision",
                                *span,
                            )
                        })?,
                        hi: l.hi.checked_add(r.hi).ok_or_else(|| {
                            self.error(
                                "bounds/overflow",
                                "exceeds 128-bit analysis precision",
                                *span,
                            )
                        })?,
                    },
                    BinaryOp::Sub => Interval {
                        lo: l.lo.checked_sub(r.hi).ok_or_else(|| {
                            self.error(
                                "bounds/overflow",
                                "exceeds 128-bit analysis precision",
                                *span,
                            )
                        })?,
                        hi: l.hi.checked_sub(r.lo).ok_or_else(|| {
                            self.error(
                                "bounds/overflow",
                                "exceeds 128-bit analysis precision",
                                *span,
                            )
                        })?,
                    },
                };
                if !exact {
                    self.operand_fits(l, lhs.span())?;
                    self.operand_fits(r, rhs.span())?;
                    self.result_fits(result, *span, &[lhs, rhs])?;
                }
                Ok(Abs::Int { iv: result, exact })
            }
            Expr::Compare { first, rest, span } => {
                // Equality may be non-numeric; ordering is numeric.
                if rest.len() == 1 && matches!(rest[0].0, CmpOp::Eq | CmpOp::Ne) {
                    let l = self.expr(first)?;
                    let r = self.expr(&rest[0].1)?;
                    if let (Abs::Int { iv: li, exact: le }, Abs::Int { iv: ri, exact: re }) =
                        (&l, &r)
                        && !(*le && *re)
                    {
                        self.operand_fits(*li, first.span())?;
                        self.operand_fits(*ri, rest[0].1.span())?;
                    }
                    let _ = span;
                    return Ok(Abs::Bool { value: None });
                }
                let (mut prev, mut all_exact) = self.as_iv(first)?;
                let mut prev_span = first.span();
                // A chain holds iff every pair holds; it fails iff any pair
                // fails; otherwise its truth depends on the witness.
                let mut any_false = false;
                let mut any_unknown = false;
                for (op, e) in rest {
                    let (next, ne) = self.as_iv(e)?;
                    if !(all_exact && ne) {
                        self.operand_fits(prev, prev_span)?;
                        self.operand_fits(next, e.span())?;
                    }
                    match cmp_truth(prev, *op, next) {
                        Some(false) => any_false = true,
                        None => any_unknown = true,
                        Some(true) => {}
                    }
                    all_exact &= ne;
                    prev = next;
                    prev_span = e.span();
                }
                let value = if any_false {
                    Some(false)
                } else if any_unknown {
                    None
                } else {
                    Some(true)
                };
                Ok(Abs::Bool { value })
            }
            Expr::In {
                value,
                lo,
                hi,
                inclusive,
                ..
            } => {
                let (v, ve) = self.as_iv(value)?;
                let (l, le) = self.as_iv(lo)?;
                let (h, he) = self.as_iv(hi)?;
                if !(ve && le && he) {
                    self.operand_fits(v, value.span())?;
                    self.operand_fits(l, lo.span())?;
                    self.operand_fits(h, hi.span())?;
                }
                // `v in lo..hi` (half-open) or `lo..=hi` (inclusive). Holds for
                // all witnesses iff v is wholly inside; never iff v is wholly
                // outside.
                let upper_in = if *inclusive {
                    v.hi <= h.lo
                } else {
                    v.hi < h.lo
                };
                let upper_out = if *inclusive {
                    v.lo > h.hi
                } else {
                    v.lo >= h.hi
                };
                let value = if v.lo >= l.hi && upper_in {
                    Some(true)
                } else if v.hi < l.lo || upper_out {
                    Some(false)
                } else {
                    None
                };
                Ok(Abs::Bool { value })
            }
            Expr::Index { base, index, .. } => {
                let arr = self.expr(base)?;
                let idx = self.expr(index)?;
                let Abs::Array { elems } = arr else {
                    return Ok(Abs::Bytes); // sema rejects; defensive
                };
                if let (Elems::Exact(items), Abs::Int { iv, exact: true }) = (&elems, &idx) {
                    let i = iv.lo;
                    if i >= 0 && (i as usize) < items.len() {
                        return Ok(items[i as usize].clone());
                    }
                }
                Ok(elems.get(0))
            }
            Expr::ArrayLit { elems, .. } => {
                let mut out = Vec::with_capacity(elems.len());
                for e in elems {
                    out.push(self.expr(e)?);
                }
                Ok(Abs::Array {
                    elems: Elems::Exact(out),
                })
            }
            Expr::TypedCtor { .. } => Ok(Abs::Bytes),
            Expr::Member { .. } => Ok(Abs::Bytes), // only as callee (sema)
            Expr::Call { callee, args, span } => self.call(callee, args, *span),
            Expr::Comprehension {
                callee,
                acc,
                binders,
                where_clauses,
                body,
                span,
            } => {
                let depth = self.scope.len();
                let r =
                    self.comprehension(callee, acc.as_ref(), binders, where_clauses, body, *span);
                self.scope.truncate(depth);
                r
            }
        }
    }

    fn call(&mut self, callee: &Expr, args: &[Arg], span: Span) -> Result<Abs, ()> {
        if let Expr::Member { base, member, .. } = callee {
            if let Expr::Name(t) = base.as_ref() {
                if t.text == "LockTime" {
                    return Ok(Abs::Lock);
                }
                if t.text == "PublicKey" {
                    return Ok(Abs::Bytes);
                }
            }
            if member.text == "check" {
                let _ = self.expr(base)?;
                return Ok(Abs::Bool { value: None });
            }
            return Ok(Abs::Bytes);
        }
        let Expr::Name(name) = callee else {
            return Ok(Abs::Bytes);
        };
        match name.text.as_str() {
            "after" => Ok(Abs::Check),
            "sha256" | "hash256" | "hash160" | "ripemd160" | "sha1" | "PublicKey" => {
                for a in args {
                    let _ = self.expr(&a.value)?;
                }
                Ok(Abs::Bytes)
            }
            "int" => {
                let (iv, exact) = self.as_iv(&args[0].value)?;
                Ok(Abs::Int { iv, exact })
            }
            "abs" => {
                let (iv, exact) = self.as_iv(&args[0].value)?;
                let result = if iv.lo >= 0 {
                    iv
                } else if iv.hi <= 0 {
                    Interval {
                        lo: iv.hi.saturating_neg(),
                        hi: iv.lo.saturating_neg(),
                    }
                } else {
                    Interval {
                        lo: 0,
                        hi: iv.lo.saturating_neg().max(iv.hi),
                    }
                };
                if !exact {
                    self.operand_fits(iv, args[0].value.span())?;
                }
                Ok(Abs::Int { iv: result, exact })
            }
            "min" | "max" => {
                let (l, le) = self.as_iv(&args[0].value)?;
                let (r, re) = self.as_iv(&args[1].value)?;
                let exact = le && re;
                let result = if name.text == "min" {
                    Interval {
                        lo: l.lo.min(r.lo),
                        hi: l.hi.min(r.hi),
                    }
                } else {
                    Interval {
                        lo: l.lo.max(r.lo),
                        hi: l.hi.max(r.hi),
                    }
                };
                if !exact {
                    self.operand_fits(l, args[0].value.span())?;
                    self.operand_fits(r, args[1].value.span())?;
                }
                Ok(Abs::Int { iv: result, exact })
            }
            "pow" => {
                // sema enforces const args; at instantiation they are exact.
                let (b, _) = self.as_iv(&args[0].value)?;
                let (e, _) = self.as_iv(&args[1].value)?;
                let v = b.lo.checked_pow(e.lo.clamp(0, 200) as u32).ok_or_else(|| {
                    self.error("bounds/overflow", "pow exceeds analysis precision", span)
                })?;
                Ok(Abs::Int {
                    iv: Interval::exact(v),
                    exact: true,
                })
            }
            "select" => self.select(args),
            _ => Ok(Abs::Bytes), // sema guarantees the call set; defensive
        }
    }

    fn select(&mut self, args: &[Arg]) -> Result<Abs, ()> {
        let cond = &args[0].value;
        let _ = self.expr(cond)?;

        // Condition-sensitive facts in each arm.
        let saved = self.scope.clone();
        self.narrow(cond, true);
        let t = self.expr(&args[1].value);
        self.scope = saved.clone();
        self.narrow(cond, false);
        let e = self.expr(&args[2].value);
        self.scope = saved;

        match (t?, e?) {
            (Abs::Int { iv: ti, exact: te }, Abs::Int { iv: ei, exact: ee }) => Ok(Abs::Int {
                iv: ti.hull(ei),
                exact: te && ee && ti == ei,
            }),
            (Abs::Bool { .. }, Abs::Bool { .. }) => Ok(Abs::Bool { value: None }),
            (a, _) => Ok(a),
        }
    }

    fn comprehension(
        &mut self,
        callee: &Ident,
        acc: Option<&AccClause>,
        binders: &[Binder],
        where_clauses: &[Expr],
        body: &Expr,
        span: Span,
    ) -> Result<Abs, ()> {
        // Materialize binder sequences abstractly.
        let mut seqs: Vec<Elems> = Vec::with_capacity(binders.len());
        for b in binders {
            let elems = match &b.seq {
                Seq::Expr(e) => match self.expr(e)? {
                    Abs::Array { elems } => elems,
                    Abs::Poison => return Err(()), // already diagnosed
                    other => {
                        let msg =
                            format!("a binder iterates an array, found {}", kind_name(&other));
                        self.error("bounds/type", msg, e.span());
                        return Err(());
                    }
                },
                Seq::Range {
                    lo, hi, inclusive, ..
                } => {
                    let (l, _) = self.as_iv(lo)?;
                    let (h, _) = self.as_iv(hi)?;
                    let end = if *inclusive {
                        h.lo.saturating_add(1)
                    } else {
                        h.lo
                    };
                    let items: Vec<Abs> = (l.lo..end)
                        .map(|v| Abs::Int {
                            iv: Interval::exact(v),
                            exact: true,
                        })
                        .collect();
                    Elems::Exact(items)
                }
            };
            seqs.push(elems);
        }
        let n = seqs.first().map(|s| s.len()).unwrap_or(0);

        let agg = callee.text.as_str();
        let mut sum_iv = Interval::exact(0);
        let mut count_iv = Interval::exact(0);
        let mut fold_abs: Option<Abs> = if let Some(a) = acc {
            Some(self.expr(&a.init)?)
        } else {
            None
        };
        let body_runtime = true; // conservative: aggregates are runtime values

        for i in 0..n {
            let depth = self.scope.len();
            for (b, seq) in binders.iter().zip(&seqs) {
                self.scope.push((b.name.text.clone(), seq.get(i)));
            }
            if let (Some(a), Some(v)) = (acc, &fold_abs) {
                self.scope.push((a.name.text.clone(), v.clone()));
            }
            // Guards narrow the body; unknown guards make contributions
            // optional (hull with the aggregator's identity).
            let mut guard_known_false = false;
            let mut guard_unknown = false;
            for w in where_clauses {
                match self.expr(w) {
                    Ok(Abs::Bool { value: Some(false) }) => guard_known_false = true,
                    Ok(Abs::Bool { value: Some(true) }) => {}
                    Ok(_) => guard_unknown = true,
                    Err(()) => {
                        self.scope.truncate(depth);
                        return Err(());
                    }
                }
                self.narrow(w, true);
            }
            if guard_known_false {
                self.scope.truncate(depth);
                continue;
            }

            let body_abs = match self.expr(body) {
                Ok(a) => a,
                Err(()) => {
                    self.scope.truncate(depth);
                    return Err(());
                }
            };

            match agg {
                "sum" => {
                    let contrib = match &body_abs {
                        Abs::Int { iv, .. } => *iv,
                        Abs::Bool { value: Some(b) } => Interval::exact(*b as i128),
                        Abs::Bool { value: None } => Interval { lo: 0, hi: 1 },
                        Abs::Poison => {
                            self.scope.truncate(depth);
                            return Err(()); // already diagnosed
                        }
                        other => {
                            let msg =
                                format!("`sum` body must be numeric, found {}", kind_name(other));
                            self.error("bounds/type", msg, body.span());
                            self.scope.truncate(depth);
                            return Err(());
                        }
                    };
                    let contrib = if guard_unknown {
                        contrib.hull(Interval::exact(0))
                    } else {
                        contrib
                    };
                    // Saturating, not wrapping: a bound can be an i128 sentinel
                    // (narrow_pair mints i128::MAX/MIN for half-open requires), so
                    // a plain `+` could in principle wrap a huge sum to a small
                    // in-range value that then slips past result_fits. Saturating
                    // clamps toward +/-inf, which is a SOUND over-approximation
                    // for interval analysis and forces result_fits to reject.
                    // (Unreachable today -- body_runtime is always true so the
                    // result_fits below clamps sum_iv to +/-MACHINE_MAX every
                    // iteration -- but this feeds dead_requires -> lowering, so
                    // keep it sound by construction, matching the checked_add the
                    // binary Add path already uses.)
                    sum_iv = Interval {
                        lo: sum_iv.lo.saturating_add(contrib.lo),
                        hi: sum_iv.hi.saturating_add(contrib.hi),
                    };
                    // Every PARTIAL sum is an on-chain ADD result.
                    if body_runtime {
                        self.result_fits(sum_iv, span, &[])?;
                    }
                }
                "count" => {
                    let contrib = match &body_abs {
                        Abs::Bool { value: Some(true) } => Interval::exact(1),
                        Abs::Bool { value: Some(false) } => Interval::exact(0),
                        _ => Interval { lo: 0, hi: 1 },
                    };
                    let contrib = if guard_unknown {
                        contrib.hull(Interval::exact(0))
                    } else {
                        contrib
                    };
                    count_iv = Interval {
                        lo: count_iv.lo.saturating_add(contrib.lo),
                        hi: count_iv.hi.saturating_add(contrib.hi),
                    };
                    // Every partial count is an on-chain ADD result too. Bound it
                    // locally like sum/fold instead of leaning on the distant
                    // MAX_WITNESS_ELEMENTS limit to keep it inside the 4-byte
                    // CScriptNum domain (defense in depth: today the limit makes
                    // this unreachable, but the bound should not depend on it).
                    if body_runtime {
                        self.result_fits(count_iv, span, &[])?;
                    }
                }
                "all" | "any" => {}
                "fold" => {
                    let next = match (&fold_abs, &body_abs) {
                        (Some(Abs::Int { iv: prev, .. }), Abs::Int { iv: new, exact }) => {
                            // The accumulator may keep its old value (guard
                            // unknown/skip) or take the new one.
                            let iv = if guard_unknown { new.hull(*prev) } else { *new };
                            if body_runtime {
                                self.result_fits(iv, span, &[])?;
                            }
                            Abs::Int {
                                iv,
                                exact: *exact && !guard_unknown,
                            }
                        }
                        _ => body_abs.clone(),
                    };
                    fold_abs = Some(next);
                }
                _ => {}
            }
            self.scope.truncate(depth);
        }

        Ok(match agg {
            "sum" => Abs::Int {
                iv: sum_iv,
                exact: false,
            },
            "count" => Abs::Int {
                iv: count_iv,
                exact: false,
            },
            "all" | "any" => Abs::Bool { value: None },
            "fold" => fold_abs.expect("fold has acc"),
            _ => Abs::Bool { value: None }, // sema rejects; defensive
        })
    }

    // --- narrowing ---

    /// Apply the facts implied by `cond` being `assume` (true for require
    /// items and where-guards and select-then; false for select-else).
    fn narrow(&mut self, cond: &Expr, assume: bool) {
        match cond {
            Expr::Compare { first, rest, .. } if assume => {
                let mut prev: &Expr = first;
                for (op, next) in rest {
                    self.narrow_pair(prev, *op, next);
                    prev = next;
                }
            }
            Expr::Compare { first, rest, .. } if rest.len() == 1 => {
                // Negation of a single comparison narrows too.
                let (op, rhs) = (&rest[0].0, &rest[0].1);
                if let Some(neg) = negate(*op) {
                    self.narrow_pair(first, neg, rhs);
                }
            }
            Expr::In {
                value,
                lo,
                hi,
                inclusive,
                ..
            } if assume => {
                if let Expr::Name(n) = value.as_ref() {
                    let (Ok((l, _)), Ok((h, _))) = (self.as_iv(lo), self.as_iv(hi)) else {
                        return;
                    };
                    let upper = if *inclusive {
                        h.hi
                    } else {
                        h.hi.saturating_sub(1)
                    };
                    self.narrow_name(
                        n,
                        Interval {
                            lo: l.lo,
                            hi: upper,
                        },
                    );
                }
            }
            _ => {}
        }
    }

    /// Narrow from `L op R` (held true): a `Name` on either side intersects
    /// with the bound implied by the other side's interval (weakest-sound).
    fn narrow_pair(&mut self, lhs: &Expr, op: CmpOp, rhs: &Expr) {
        let (Ok((l, _)), Ok((r, _))) = (self.as_iv_quiet(lhs), self.as_iv_quiet(rhs)) else {
            return;
        };
        if let Expr::Name(n) = lhs {
            let bound = match op {
                CmpOp::Lt => Interval {
                    lo: i128::MIN,
                    hi: r.hi.saturating_sub(1),
                },
                CmpOp::Le => Interval {
                    lo: i128::MIN,
                    hi: r.hi,
                },
                CmpOp::Gt => Interval {
                    lo: r.lo.saturating_add(1),
                    hi: i128::MAX,
                },
                CmpOp::Ge => Interval {
                    lo: r.lo,
                    hi: i128::MAX,
                },
                CmpOp::Eq => r,
                CmpOp::Ne => return,
            };
            self.narrow_name(n, bound);
        }
        if let Expr::Name(n) = rhs {
            let bound = match op {
                CmpOp::Lt => Interval {
                    lo: l.lo.saturating_add(1),
                    hi: i128::MAX,
                },
                CmpOp::Le => Interval {
                    lo: l.lo,
                    hi: i128::MAX,
                },
                CmpOp::Gt => Interval {
                    lo: i128::MIN,
                    hi: l.hi.saturating_sub(1),
                },
                CmpOp::Ge => Interval {
                    lo: i128::MIN,
                    hi: l.hi,
                },
                CmpOp::Eq => l,
                CmpOp::Ne => return,
            };
            self.narrow_name(n, bound);
        }
    }

    fn narrow_name(&mut self, name: &Ident, bound: Interval) {
        let Some(Abs::Int { iv, exact }) = self.lookup(&name.text) else {
            return;
        };
        match iv.intersect(bound) {
            Some(narrowed) => self.set_fact(
                &name.text,
                Abs::Int {
                    iv: narrowed,
                    exact,
                },
            ),
            None => self.error(
                "bounds/infeasible",
                format!(
                    "this constraint contradicts earlier facts: `{}` in [{}, {}] cannot \
                     meet [{}, {}]: the path can never be satisfied",
                    name.text,
                    iv.lo,
                    iv.hi,
                    bound.lo.max(-MACHINE_MAX * 2),
                    bound.hi.min(MACHINE_MAX * 2)
                ),
                name.span,
            ),
        }
    }

    /// `as_iv` without emitting diagnostics (narrowing is best-effort).
    fn as_iv_quiet(&mut self, e: &Expr) -> Result<(Interval, bool), ()> {
        let before = self.diags.len();
        let r = self.as_iv(e);
        self.diags.truncate(before);
        r
    }
}

fn negate(op: CmpOp) -> Option<CmpOp> {
    Some(match op {
        CmpOp::Lt => CmpOp::Ge,
        CmpOp::Le => CmpOp::Gt,
        CmpOp::Gt => CmpOp::Le,
        CmpOp::Ge => CmpOp::Lt,
        CmpOp::Eq => return None, // != narrows nothing representable
        CmpOp::Ne => return None,
    })
}

fn const_to_abs(v: &ConstValue) -> Abs {
    match v {
        ConstValue::Int(n) => Abs::Int {
            iv: Interval::exact(*n),
            exact: true,
        },
        ConstValue::Bool(b) => Abs::Bool { value: Some(*b) },
        ConstValue::Bytes(_) => Abs::Bytes,
        ConstValue::LockAbs(_) | ConstValue::LockRel(_) => Abs::Lock,
        ConstValue::Array(items) => Abs::Array {
            elems: Elems::Exact(items.iter().map(const_to_abs).collect()),
        },
    }
}

fn kind_name(a: &Abs) -> &'static str {
    match a {
        Abs::Int { .. } => "an integer",
        Abs::Bool { .. } => "a boolean",
        Abs::Bytes => "byte data",
        Abs::Lock => "a locktime",
        Abs::Check => "a timelock check",
        Abs::Array { .. } => "an array",
        Abs::Poison => "an earlier error",
    }
}
