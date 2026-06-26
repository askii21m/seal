//! Spend-path analyses: feasibility, authorization, non-malleability classes,
//! and witness templates, on instantiated contracts.
//!
//! # Paths in v1
//!
//! Every `spend` is its own tapleaf (the v1 planner never merges) plus the
//! keypath when declared, so enumeration is structural. The combinatorial
//! dimension is threshold families (`k`-of-`n`), recorded per path with the
//! instantiated `k`.
//!
//! # The validation budget is a theorem in v1, not a check
//!
//! Budget = `50 + witness_size >= 50 * sigops`, and every counted signature
//! check consumes a non-empty 64-byte signature, which is >= 65 witness bytes
//! (empty threshold slots do not count against budget, BIP342). The left side
//! grows strictly faster than the right; no v1 program can violate it. Nothing
//! to enforce; recorded here so the absence of code is a documented decision,
//! not an omission.
//!
//! # Recognition is canonical-shape-only (deliberately)
//!
//! Signatures are counted from three shapes: a direct `k.check(s)` require
//! item; an explicit check-sum threshold (`a.check(sa) + b.check(sb) >= k`);
//! the comprehension threshold (`sum(k in keys, s in sigs => k.check(s)) >=
//! m`). Pins are `hashfn(p) == <const>` and `p == <const>` items. Anything
//! fancier (checks under `select`, negated checks) does not count: the
//! conservative direction is sound, under-counting bindingness can only
//! produce false alarms, never false safety.

use std::collections::BTreeMap;

use crate::analysis::consteval::{ConstValue, Env, LockAbs, LockRel, eval_in_env};
use crate::analysis::sema::{ContractInfo, ParamSig, Ty};
use crate::diagnostics::Diagnostic;
use crate::syntax::ast::*;
use crate::syntax::span::Span;

/// How a witness element is bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Class {
    /// A signature consumed by a counted check.
    Signed,
    /// Uniquely implied by const commitments (hash pin, equality pin).
    Determined,
    /// Free spender choice; requires the `relaxed` marker.
    Relaxed,
}

#[derive(Debug, Clone)]
pub struct ParamInfo {
    pub name: String,
    pub ty: String,
    pub class: Class,
}

#[derive(Debug, Clone)]
pub struct PathInfo {
    pub name: String,
    /// "keypath" or "leaf".
    pub kind: &'static str,
    pub open: bool,
    pub params: Vec<ParamInfo>,
    /// Human-readable transaction obligations.
    pub obligations: Vec<String>,
    /// `(required, slots)` when the path contains a threshold family.
    pub threshold: Option<(i128, usize)>,
}

#[derive(Debug, Clone, Default)]
pub struct PathReport {
    pub paths: Vec<PathInfo>,
}

pub fn analyze(
    contract: &Contract,
    info: &ContractInfo,
    env: &Env,
) -> (Vec<Diagnostic>, PathReport) {
    let mut cx = Analyzer {
        env,
        const_keys: collect_const_keys(info),
        diags: Vec::new(),
        report: PathReport::default(),
    };
    for item in &contract.items {
        match item {
            Item::Spend(s) => {
                let sig = info.spends.iter().find(|x| x.name == s.name.text);
                if let Some(sig) = sig {
                    cx.spend(s, sig);
                }
            }
            Item::Keypath(Keypath::Key(_)) => {
                cx.report.paths.push(PathInfo {
                    name: "keypath".into(),
                    kind: "keypath",
                    open: false,
                    params: vec![ParamInfo {
                        name: "signature".into(),
                        ty: "Signature (aggregate)".into(),
                        class: Class::Signed,
                    }],
                    obligations: vec![],
                    threshold: None,
                });
            }
            _ => {}
        }
    }
    (cx.diags, cx.report)
}

/// Names whose values are const `PublicKey`s (externs and consts): the keys
/// authorization trusts directly.
fn collect_const_keys(info: &ContractInfo) -> BTreeMap<String, ()> {
    let mut m = BTreeMap::new();
    for (name, ty) in info.externs.iter().chain(&info.consts) {
        match ty {
            Ty::PublicKey => {
                m.insert(name.clone(), ());
            }
            Ty::Array(elem, _) if **elem == Ty::PublicKey => {
                m.insert(name.clone(), ());
            }
            _ => {}
        }
    }
    m
}

struct Analyzer<'a> {
    env: &'a Env,
    const_keys: BTreeMap<String, ()>,
    diags: Vec<Diagnostic>,
    report: PathReport,
}

/// What one spend's require items established.
#[derive(Default)]
struct Facts {
    /// Params pinned by hash/equality to const data.
    pinned: Vec<String>,
    /// Signature params consumed by counted checks.
    signed_sigs: Vec<String>,
    /// At least one counted check is against a const/pinned key.
    binding: bool,
    /// Threshold family (required, slots).
    threshold: Option<(i128, usize)>,
    /// Instantiated timelocks: (is_height, value, span) / (is_blocks, value, span).
    abs_locks: Vec<(LockAbs, Span)>,
    rel_locks: Vec<(LockRel, Span)>,
}

impl<'a> Analyzer<'a> {
    fn error(&mut self, code: &'static str, msg: impl Into<String>, span: Span) {
        self.diags.push(Diagnostic::error(code, msg, span));
    }

    fn spend(&mut self, s: &Spend, sig: &crate::analysis::sema::SpendSig) {
        let mut facts = Facts::default();

        // Two passes over require items: pins first (a pin may appear after
        // the check that relies on it; order within a require set is
        // semantically free), then checks/locks/feasibility.
        for stmt in &s.body {
            if let Stmt::Require(req) = stmt {
                for item in &req.items {
                    self.collect_pin(item, &mut facts);
                }
            }
        }
        for stmt in &s.body {
            if let Stmt::Require(req) = stmt {
                for item in &req.items {
                    self.collect_item(item, sig, &mut facts);
                }
            }
        }

        // Feasibility: per-path timelock domain consistency.
        let mut heights = facts
            .abs_locks
            .iter()
            .filter(|(l, _)| matches!(l, LockAbs::Height(_)));
        let mut times = facts
            .abs_locks
            .iter()
            .filter(|(l, _)| matches!(l, LockAbs::Time(_)));
        if let (Some(_), Some((_, tspan))) = (heights.next(), times.next()) {
            self.error(
                "feasibility/timelock-mix",
                "this path mixes height- and wall-clock absolute timelocks: a transaction \
                 has ONE nLockTime field, so the conjunction is unsatisfiable forever",
                *tspan,
            );
        }
        let mut blocks = facts
            .rel_locks
            .iter()
            .filter(|(l, _)| matches!(l, LockRel::Blocks(_)));
        let mut units = facts
            .rel_locks
            .iter()
            .filter(|(l, _)| matches!(l, LockRel::Units(_)));
        if let (Some(_), Some((_, uspan))) = (blocks.next(), units.next()) {
            self.error(
                "feasibility/timelock-mix",
                "this path mixes block- and time-based relative timelocks: an input has \
                 ONE nSequence field, so the conjunction is unsatisfiable forever",
                *uspan,
            );
        }

        // Authorization: theft-resistance.
        if !facts.binding && !s.open {
            self.error(
                "auth/theft",
                format!(
                    "spend `{}` requires no signature against a const or \
                     commitment-pinned key: its witness is public the moment it enters \
                     the mempool, and anyone can rebind it to their own transaction. Add \
                     a `key.check(sig)`, or declare `open spend` if anyone-can-spend \
                     is intended",
                    s.name.text
                ),
                s.name.span,
            );
        }

        // Non-malleability: classify every parameter.
        let used = collect_used_names(s);
        let mut params = Vec::new();
        for (p, ast_param) in sig.params.iter().zip(&s.params) {
            if !used.contains(&p.name) {
                self.error(
                    "malleability/unused",
                    format!(
                        "parameter `{}` is never used: an unconstrained witness element \
                         is freely malleable; remove it",
                        p.name
                    ),
                    ast_param.name.span,
                );
                continue;
            }
            let class = self.classify(p, &facts);
            match class {
                Class::Relaxed if !p.relaxed => {
                    self.diags.push(
                        Diagnostic::error(
                            "malleability/relaxed",
                            format!(
                                "parameter `{}` is a free spender choice -- nothing binds \
                                 witness data to the transaction, so third parties can \
                                 substitute any other valid value",
                                p.name
                            ),
                            ast_param.name.span,
                        )
                        .with_help("mark it `relaxed` to accept that, or pin it to a commitment"),
                    );
                }
                Class::Signed | Class::Determined if p.relaxed => {
                    self.diags.push(
                        Diagnostic::warning(
                            "malleability/relaxed-redundant",
                            format!(
                                "`relaxed` on `{}` is unnecessary -- it is already {}",
                                p.name,
                                if class == Class::Signed {
                                    "Signed"
                                } else {
                                    "Determined"
                                }
                            ),
                            ast_param.name.span,
                        )
                        .with_help("remove the `relaxed` qualifier"),
                    );
                }
                _ => {}
            }
            params.push(ParamInfo {
                name: p.name.clone(),
                ty: ty_display(&p.ty),
                class,
            });
        }

        // Obligations: the satisfier's transaction duties.
        let mut obligations = Vec::new();
        let max_height = facts
            .abs_locks
            .iter()
            .filter_map(|(l, _)| {
                if let LockAbs::Height(h) = l {
                    Some(*h)
                } else {
                    None
                }
            })
            .max();
        let max_time = facts
            .abs_locks
            .iter()
            .filter_map(|(l, _)| {
                if let LockAbs::Time(t) = l {
                    Some(*t)
                } else {
                    None
                }
            })
            .max();
        if let Some(h) = max_height {
            obligations.push(format!(
                "nLockTime >= {h} (height); input nSequence non-final"
            ));
        }
        if let Some(t) = max_time {
            obligations.push(format!(
                "nLockTime >= {t} (unix, MTP-evaluated); input nSequence non-final"
            ));
        }
        let max_blocks = facts
            .rel_locks
            .iter()
            .filter_map(|(l, _)| {
                if let LockRel::Blocks(b) = l {
                    Some(*b)
                } else {
                    None
                }
            })
            .max();
        let max_units = facts
            .rel_locks
            .iter()
            .filter_map(|(l, _)| {
                if let LockRel::Units(u) = l {
                    Some(*u)
                } else {
                    None
                }
            })
            .max();
        if let Some(b) = max_blocks {
            obligations.push(format!("input nSequence >= {b} blocks; tx version >= 2"));
        }
        if let Some(u) = max_units {
            obligations.push(format!(
                "input nSequence >= {u}*512s (time flag); tx version >= 2"
            ));
        }

        self.report.paths.push(PathInfo {
            name: s.name.text.clone(),
            kind: "leaf",
            open: s.open,
            params,
            obligations,
            threshold: facts.threshold,
        });
    }

    /// Pins: `hashfn(p) == <const>` / `<const> == hashfn(p)` / `p == <const>`.
    fn collect_pin(&mut self, item: &Expr, facts: &mut Facts) {
        let Expr::Compare { first, rest, .. } = item else {
            return;
        };
        if rest.len() != 1 || rest[0].0 != CmpOp::Eq {
            return;
        }
        let (l, r) = (first.as_ref(), &rest[0].1);
        for (side, other) in [(l, r), (r, l)] {
            // hashfn(p) == const
            if let Expr::Call { callee, args, .. } = side
                && let Expr::Name(f) = callee.as_ref()
                && matches!(
                    f.text.as_str(),
                    "sha256" | "hash256" | "hash160" | "ripemd160" | "sha1"
                )
                && args.len() == 1
                && let Expr::Name(p) = &args[0].value
                && self.is_const_value(other)
            {
                facts.pinned.push(p.text.clone());
            }
            // p == const
            if let Expr::Name(p) = side
                && self.env.get(&p.text).is_none()
                && self.is_const_value(other)
            {
                facts.pinned.push(p.text.clone());
            }
        }
    }

    /// True when `e` evaluates against the const env (no params involved).
    fn is_const_value(&self, e: &Expr) -> bool {
        eval_in_env(e, self.env).0.is_some()
    }

    fn collect_item(
        &mut self,
        item: &Expr,
        _sig: &crate::analysis::sema::SpendSig,
        facts: &mut Facts,
    ) {
        // Feasibility: a require item that is constantly false can never be satisfied.
        if let (Some(ConstValue::Bool(false)), _) = eval_in_env(item, self.env) {
            self.error(
                "feasibility/unsatisfiable",
                "this require item is constantly false: the path can never be spent",
                item.span(),
            );
            return;
        }

        match item {
            // Direct check: k.check(s).
            Expr::Call { .. } => {
                if let Some((key_binding, sig_name)) = self.as_check(item, facts) {
                    facts.binding |= key_binding;
                    facts.signed_sigs.push(sig_name);
                }
                // after(LockTime...): evaluate the argument, which also
                // value-validates body-level LockTime constructors.
                if let Expr::Call { callee, args, .. } = item
                    && let Expr::Name(f) = callee.as_ref()
                    && f.text == "after"
                    && args.len() == 1
                {
                    let (v, diags) = eval_in_env(&args[0].value, self.env);
                    self.diags.extend(diags);
                    match v {
                        Some(ConstValue::LockAbs(l)) => facts.abs_locks.push((l, item.span())),
                        Some(ConstValue::LockRel(l)) => facts.rel_locks.push((l, item.span())),
                        _ => {}
                    }
                }
            }
            // Threshold: <check-sum or comprehension> >= k / == k / > k.
            Expr::Compare { first, rest, .. } if rest.len() == 1 => {
                let (op, bound) = (&rest[0].0, &rest[0].1);
                let Some(ConstValue::Int(k)) = eval_in_env(bound, self.env).0 else {
                    return;
                };
                let min_required = match op {
                    CmpOp::Ge => k,
                    CmpOp::Gt => k + 1,
                    CmpOp::Eq => k,
                    _ => return,
                };
                let mut checks = Vec::new();
                if self.collect_check_sum(first, facts, &mut checks) && !checks.is_empty() {
                    let all_const_keys = checks.iter().all(|(b, _)| *b);
                    for (_, s) in &checks {
                        facts.signed_sigs.push(s.clone());
                    }
                    if min_required >= 1 && all_const_keys {
                        facts.binding = true;
                    }
                    facts.threshold = Some((min_required, checks.len()));
                }
            }
            _ => {}
        }
    }

    /// Recognize `k.check(s)`; returns (key is const/pinned, sig param name).
    fn as_check(&self, e: &Expr, facts: &Facts) -> Option<(bool, String)> {
        let Expr::Call { callee, args, .. } = e else {
            return None;
        };
        let Expr::Member { base, member, .. } = callee.as_ref() else {
            return None;
        };
        if member.text != "check" || args.len() != 1 {
            return None;
        }
        let sig_name = match &args[0].value {
            Expr::Name(n) => n.text.clone(),
            _ => return None,
        };
        let key_binding = match base.as_ref() {
            Expr::Name(k) => {
                self.const_keys.contains_key(&k.text) || facts.pinned.contains(&k.text)
            }
            // keys[i].check(s): const array element.
            Expr::Index { base, .. } => {
                matches!(base.as_ref(), Expr::Name(n) if self.const_keys.contains_key(&n.text))
            }
            _ => false,
        };
        Some((key_binding, sig_name))
    }

    /// Recognize a check-sum: an Add-tree of `k.check(s)` leaves, or the
    /// comprehension `sum(k in keys, s in sigs => k.check(s))`. Pushes
    /// (key-binding, sig-name) per slot; returns false if the shape doesn't
    /// match (then it's just arithmetic, not a threshold).
    fn collect_check_sum(&self, e: &Expr, facts: &Facts, out: &mut Vec<(bool, String)>) -> bool {
        match e {
            Expr::Binary {
                op: BinaryOp::Add,
                lhs,
                rhs,
                ..
            } => self.collect_check_sum(lhs, facts, out) && self.collect_check_sum(rhs, facts, out),
            Expr::Call { .. } => match self.as_check(e, facts) {
                Some(pair) => {
                    out.push(pair);
                    true
                }
                None => false,
            },
            Expr::Comprehension {
                callee,
                binders,
                body,
                ..
            } if callee.text == "sum" => {
                // sum(k in <const keys>, s in <sig array> => k.check(s))
                let Some((kb, sb)) = self.as_check_names(body) else {
                    return false;
                };
                let mut key_const = false;
                let mut slots = 0usize;
                let mut sig_pushed = false;
                for b in binders {
                    if let Seq::Expr(Expr::Name(arr)) = &b.seq {
                        if b.name.text == kb && self.const_keys.contains_key(&arr.text) {
                            key_const = true;
                            if let Some(ConstValue::Array(items)) = self.env.get(&arr.text) {
                                slots = items.len();
                            }
                        }
                        if b.name.text == sb {
                            out.push((false, arr.text.clone())); // placeholder; fixed below
                            sig_pushed = true;
                        }
                    }
                }
                // The family expansion below replaces the single sig-binder slot
                // with `slots` copies, so it MUST have a slot to expand. If the
                // signature binder is anything but a plain name -- e.g. an array
                // literal `s in [s1, s2, s3]`, which sema accepts as a valid
                // array-typed sequence -- nothing was pushed for it, and a
                // const key array (slots > 1) would make the old code
                // `out.pop().expect(..)` an empty vector (panic) or pop a
                // sibling term's entry (silent miscompile). Bail to the general
                // sum lowering instead; it handles any comprehension correctly.
                if !sig_pushed {
                    return false;
                }
                if let Some(last) = out.last_mut() {
                    last.0 = key_const;
                }
                // One entry represents the whole family; expand to slot count.
                if slots > 1 {
                    let entry = out.pop().expect("sig binder pushed above");
                    for _ in 0..slots {
                        out.push(entry.clone());
                    }
                }
                key_const
            }
            _ => false,
        }
    }

    /// `k.check(s)` with both sides plain names, yielding (key name, sig name).
    fn as_check_names(&self, e: &Expr) -> Option<(String, String)> {
        let Expr::Call { callee, args, .. } = e else {
            return None;
        };
        let Expr::Member { base, member, .. } = callee.as_ref() else {
            return None;
        };
        if member.text != "check" || args.len() != 1 {
            return None;
        }
        match (base.as_ref(), &args[0].value) {
            (Expr::Name(k), Expr::Name(s)) => Some((k.text.clone(), s.text.clone())),
            _ => None,
        }
    }

    fn classify(&self, p: &ParamSig, facts: &Facts) -> Class {
        match &p.ty {
            Ty::Signature => {
                if facts.signed_sigs.contains(&p.name) {
                    Class::Signed
                } else {
                    Class::Relaxed
                }
            }
            Ty::Array(elem, _) if **elem == Ty::Signature => {
                if facts.signed_sigs.contains(&p.name) {
                    Class::Signed
                } else {
                    Class::Relaxed
                }
            }
            Ty::PublicKey | Ty::Bytes(_) | Ty::Hash(_) | Ty::Int => {
                if facts.pinned.contains(&p.name) {
                    Class::Determined
                } else {
                    Class::Relaxed
                }
            }
            // Bool / arrays of free data: spender's choice.
            _ => Class::Relaxed,
        }
    }
}

fn ty_display(ty: &Ty) -> String {
    use crate::analysis::sema::{HashAlg, Len};
    match ty {
        Ty::Bool => "Bool".into(),
        Ty::Int => "Int".into(),
        Ty::PublicKey => "PublicKey".into(),
        Ty::Signature => "Signature".into(),
        Ty::Bytes(Len::Lit(n)) => format!("Bytes<{n}>"),
        Ty::Bytes(Len::Named(n)) => format!("Bytes<{n}>"),
        Ty::Hash(a) => format!(
            "Hash<{}>",
            match a {
                HashAlg::Sha256 => "Sha256",
                HashAlg::Hash256 => "Hash256",
                HashAlg::Hash160 => "Hash160",
                HashAlg::Ripemd160 => "Ripemd160",
                HashAlg::Sha1 => "Sha1",
            }
        ),
        Ty::LockTimeAbs => "LockTime.Absolute".into(),
        Ty::LockTimeRel => "LockTime.Relative".into(),
        Ty::Array(t, Len::Lit(n)) => format!("[{}; {n}]", ty_display(t)),
        Ty::Array(t, Len::Named(n)) => format!("[{}; {n}]", ty_display(t)),
    }
}

/// All names referenced anywhere in a spend's body.
fn collect_used_names(s: &Spend) -> Vec<String> {
    let mut out = Vec::new();
    fn walk(e: &Expr, out: &mut Vec<String>) {
        match e {
            Expr::Name(n) => out.push(n.text.clone()),
            Expr::Unary { operand, .. } => walk(operand, out),
            Expr::Binary { lhs, rhs, .. } => {
                walk(lhs, out);
                walk(rhs, out);
            }
            Expr::Compare { first, rest, .. } => {
                walk(first, out);
                for (_, e) in rest {
                    walk(e, out);
                }
            }
            Expr::In { value, lo, hi, .. } => {
                walk(value, out);
                walk(lo, out);
                walk(hi, out);
            }
            Expr::Index { base, index, .. } => {
                walk(base, out);
                walk(index, out);
            }
            Expr::Member { base, .. } => walk(base, out),
            Expr::Call { callee, args, .. } => {
                walk(callee, out);
                for a in args {
                    walk(&a.value, out);
                }
            }
            Expr::TypedCtor { args, .. } => {
                for a in args {
                    walk(&a.value, out);
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
                    walk(&a.init, out);
                }
                for b in binders {
                    match &b.seq {
                        Seq::Expr(e) => walk(e, out),
                        Seq::Range { lo, hi, .. } => {
                            walk(lo, out);
                            walk(hi, out);
                        }
                    }
                }
                for w in where_clauses {
                    walk(w, out);
                }
                walk(body, out);
            }
            Expr::ArrayLit { elems, .. } => {
                for e in elems {
                    walk(e, out);
                }
            }
            Expr::Int { .. } | Expr::Str { .. } | Expr::Duration { .. } | Expr::Bool { .. } => {}
        }
    }
    for stmt in &s.body {
        match stmt {
            Stmt::Let { value, .. } => walk(value, &mut out),
            Stmt::Require(req) => {
                for item in &req.items {
                    walk(item, &mut out);
                }
            }
        }
    }
    out
}
