//! Lowering: analyzed spends to tapscript ops plus witness layout.
//!
//! # Correct-and-naive, by design
//!
//! This is the baseline lowering: every named value is accessed by `PICK`
//! (copy), require items become VERIFY-form checks in source order, leftover
//! stack slots are dropped and `1` is pushed (CLEANSTACK by construction).
//! The optimizer passes (last-use `ROLL`, ordering, fusion beyond the
//! trivial VERIFY forms) layer on top once the interpreter can
//! differentially verify them against this baseline. Constant folding is
//! here: every subexpression is offered to the const evaluator first, so
//! exact values are pushed as minimal literals (always-on).
//!
//! # The stack model
//!
//! `stack: Vec<Slot>` mirrors the machine stack at every emission; named
//! slots are parameters (array params occupy one slot per element, named
//! `p[i]`) and `let` bindings. The model makes CLEANSTACK structural: the
//! leaf ends `[Temp]` (one truthy value) or it doesn't compile.
//!
//! # Witness layout
//!
//! Witness order is compiler-owned: no consensus or policy rule orders the
//! script-input elements, so the layout is whatever minimizes script bytes,
//! constrained only by determinism and disclosure (`witness_order` is the
//! per-leaf template; the satisfier fills by name, never by source
//! position).
//!
//! The baseline default is declaration order, first parameter deepest,
//! array parameters expanded in index order. The guaranteed threshold
//! lowering overrides it: chain-consumed signature slots lay out in reverse
//! chain order (the slot for the lexicographically-first key on top), so
//! `<k1> CHECKSIG <k2> CHECKSIGADD ...` eats them with zero stack
//! manipulation. The later optimizer generalizes this, scheduling all
//! single-use values in consumption order, under differential verification
//! against this baseline.
//!
//! # The guaranteed threshold chain (a cost contract)
//!
//! All-`check` threshold sums over const keys emit keys lexicographically
//! (BIP67 spirit: script and address depend on the key set) and, when the
//! signature slots are single-use trailing parameters, consume them in
//! place: `34n + ~2` script bytes, no PICK/SWAP/DROP overhead. In tail
//! position the comparison is the leaf result (no VERIFY, no `1`). When the
//! consuming layout is unavailable (slots reused, not trailing, keys not
//! const), the chain falls back to copy-based access, key-sorted whenever
//! keys are const; correctness never depends on the fast path.
//!
//! # Airlocks
//!
//! Emitted at leaf start: `Bytes<N>`/`Hash`/`PublicKey` parameters get the
//! never-elided `SIZE` check; `Bool` parameters get the canonicality check
//! (`DUP 0NOTEQUAL EQUALVERIFY` on a copy) only when used outside
//! IF-position; bare guards are MINIMALIF-checked for free. `Int`
//! parameters need nothing extra: range requires are the airlock, and the
//! 4-byte operand rule is enforced by the consuming opcodes.

use std::collections::{BTreeMap, BTreeSet};

use crate::analysis::consteval::{ConstValue, Env, LockAbs, LockRel, MACHINE_MAX, eval_in_env};
use crate::analysis::intervals::Report as IntervalReport;
use crate::analysis::sema::{ContractInfo, Len, Ty};
use crate::codegen::script::{self, Op};
use crate::diagnostics::Diagnostic;
use crate::syntax::ast::*;
use crate::syntax::span::Span;

#[derive(Debug, Clone)]
pub struct LoweredLeaf {
    pub name: String,
    pub ops: Vec<Op>,
    pub script: Vec<u8>,
    /// Witness element names in witness order (first = deepest).
    pub witness_order: Vec<String>,
    /// Op-index ranges `[start, end)` of `require` items the interval engine
    /// proved always-true. The naive leaf still emits them; the optimizer
    /// drops these dead checks. Empty unless dead constraints were found.
    pub removable: Vec<(usize, usize)>,
    /// Per-item subject computations recorded for common-subexpression
    /// elimination. The naive leaf computes each item's compared value in
    /// full; the optimizer shares one computation between adjacent items
    /// whose subject op-runs are byte-identical. Empty unless any single
    /// comparison item was recorded.
    pub cse_subjects: Vec<CseSubject>,
}

/// A `require` item shaped `subject <cmp> bound` (one comparison), recorded
/// by lowering for common-subexpression elimination. `subject` is the
/// `[start, end)` op-range that computes the compared value; `item_end` is
/// where the whole item ends (after the bound push, the comparison, and the
/// VERIFY). Two such items lowered back-to-back (`item_end` of one equal to
/// the `subject` start of the next) with byte-identical subject op-runs
/// compute the same value over the same stack, so the optimizer can compute
/// it once and test each bound against a kept copy.
#[derive(Debug, Clone)]
pub struct CseSubject {
    pub subject: (usize, usize),
    pub item_end: usize,
}

/// A require item that leaves NO value on the stack, so it can never be the
/// tail (leaf-result) item: the only such item today is an `after(...)` timelock
/// (it lowers to `<n> CSV/CLTV DROP`). These run first so a value-producing
/// conjunct can take the tail slot.
pub(crate) fn is_verify_only_item(item: &Expr) -> bool {
    matches!(
        item,
        Expr::Call { callee, args, .. }
            if args.len() == 1 && matches!(callee.as_ref(), Expr::Name(f) if f.text == "after")
    )
}

/// If `item` is `<key>.check(<name>)` with a bare-name signature argument,
/// returns that argument name -- the single witness slot the check consumes.
/// (A threshold comprehension `sum(.. => k.check(s))` is a `sum(...)`, not a
/// `.check(...)` call, so it returns None and is left to the chain-consume
/// layout.)
fn check_sig_param(item: &Expr) -> Option<&str> {
    let Expr::Call { callee, args, .. } = item else {
        return None;
    };
    let Expr::Member { member, .. } = callee.as_ref() else {
        return None;
    };
    if member.text != "check" || args.len() != 1 {
        return None;
    }
    match &args[0].value {
        Expr::Name(n) => Some(n.text.as_str()),
        _ => None,
    }
}

/// Body emission rank within a `require` conjunction: timelocks first (they are
/// verify-only and leave nothing), signature checks LAST (a signature is the
/// natural tail result, and -- consumed last -- it sits deepest in the witness,
/// so the preimages stacked above it airlock and hash IN PLACE with no SWAP/ROLL),
/// and everything else (hashlocks, thresholds) in between. A stable sort by this
/// rank keeps source order within each group, so the layout is canonical
/// (independent of how the conjuncts were written) and juggle-free.
pub(crate) fn item_tail_rank(item: &Expr) -> u8 {
    if is_verify_only_item(item) {
        0
    } else if check_sig_param(item).is_some() {
        2
    } else {
        1
    }
}

/// The order in which WITNESS parameters are first consumed by the body, using
/// the SAME emission order as the body loop (items sorted by `item_tail_rank`).
/// Laying the witness slots out in reverse of this order puts the first-consumed
/// param on top, so each consuming op (CHECKSIG, the hash after an interleaved
/// airlock, ...) eats off the stack top with no SWAP/ROLL/PICK -- including two
/// preimages, whose airlock+hash now run back-to-back with no leading SWAP.
fn param_consumption_order(s: &Spend) -> Vec<String> {
    let params: BTreeSet<&str> = s.params.iter().map(|p| p.name.text.as_str()).collect();
    let mut order: Vec<String> = Vec::new();
    let record = |e: &Expr, order: &mut Vec<String>| {
        walk_guard_uses(e, &mut |name, _| {
            if params.contains(name) && !order.iter().any(|n| n == name) {
                order.push(name.to_string());
            }
        });
    };
    // Body emission order: a `let` is lowered where it appears (its value is
    // consumed then -- e.g. cat_bounty's `drawing` array, used only inside a
    // `let score = .. sum(px in drawing ..)`), then each require's items in
    // tail-rank order. A param missing here is genuinely unconsumed.
    for stmt in &s.body {
        match stmt {
            Stmt::Let { value, .. } => record(value, &mut order),
            Stmt::Require(req) => {
                let mut items: Vec<&Expr> = req.items.iter().collect();
                items.sort_by_key(|it| item_tail_rank(it));
                for item in items {
                    record(item, &mut order);
                }
            }
        }
    }
    order
}

pub fn lower(
    contract: &Contract,
    info: &ContractInfo,
    env: &Env,
    report: &IntervalReport,
) -> (Vec<Diagnostic>, Vec<LoweredLeaf>) {
    let mut diags = Vec::new();
    let mut leaves = Vec::new();
    for item in &contract.items {
        if let Item::Spend(s) = item {
            let Some(sig) = info.spends.iter().find(|x| x.name == s.name.text) else {
                continue;
            };
            let mut lw = Lowerer {
                env,
                info,
                sig,
                dead: &report.dead_requires,
                ops: Vec::new(),
                stack: Vec::new(),
                removable: Vec::new(),
                cse_subjects: Vec::new(),
                binders: BTreeMap::new(),
                lets_bytes: BTreeMap::new(),
                eval_env: None,
                consume: None,
                consume_done: false,
                tail_result: false,
                diags: Vec::new(),
                dead_slots: BTreeSet::new(),
                pending_airlock: BTreeMap::new(),
            };
            if let Some(leaf) = lw.spend(s) {
                let bytes = script::serialize(&leaf.0);
                if let Err(e) = script::verify_script(&bytes) {
                    lw.diags.push(
                        Diagnostic::error(
                            "lower/poison",
                            format!("emitted script failed the poison gate: {e}"),
                            s.name.span,
                        )
                        .with_note("this is a compiler bug; please report it"),
                    );
                } else {
                    leaves.push(LoweredLeaf {
                        name: s.name.text.clone(),
                        ops: leaf.0,
                        script: bytes,
                        witness_order: leaf.1,
                        removable: lw.removable.clone(),
                        cse_subjects: lw.cse_subjects.clone(),
                    });
                }
            }
            diags.extend(lw.diags);
        }
    }
    (diags, leaves)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Slot {
    Named(String),
    Temp,
}

/// A comprehension binder's meaning during unrolling.
#[derive(Debug, Clone)]
enum BinderVal {
    /// References a named stack slot (witness array element).
    Slot(String),
    /// A const value (instantiated array element / range index).
    Const(ConstValue),
}

/// (key bytes, sig slot name) threshold pairs, written order.
type ThresholdPairs = Vec<(Vec<u8>, String)>;

/// The guaranteed threshold lowering's consuming layout: one require item
/// whose signature slots are laid out in reverse chain order and eaten by
/// the CHECKSIGADD chain with zero stack manipulation.
#[derive(Debug, Clone)]
struct ConsumePlan {
    /// The require item this plan serves (matched structurally; `done`
    /// guards against duplicate items).
    item: Expr,
    /// Chain emission order: (key bytes, sig slot name), lexicographic by
    /// key bytes; stable, so duplicate keys keep their pairing order.
    chain: Vec<(Vec<u8>, String)>,
    /// Parameter names whose slots the chain consumes (a trailing run of
    /// the declaration list; the layout pass emits them specially).
    covered: Vec<String>,
}

struct Lowerer<'a> {
    env: &'a Env,
    info: &'a ContractInfo,
    sig: &'a crate::analysis::sema::SpendSig,
    /// Spans of `require` items proven always-true (from the interval engine).
    dead: &'a [Span],
    ops: Vec<Op>,
    stack: Vec<Slot>,
    /// Op-index ranges of emitted-but-dead require items, for the optimizer.
    removable: Vec<(usize, usize)>,
    /// Single-comparison item subjects, for common-subexpression elimination.
    cse_subjects: Vec<CseSubject>,
    /// Active comprehension binders (name to current element).
    binders: BTreeMap<String, BinderVal>,
    /// `let` bindings: is the bound value byte-flavored? (EQUAL/NUMEQUAL).
    lets_bytes: BTreeMap<String, bool>,
    /// `env` merged with the active const binders (comprehension bodies
    /// fold per element); None when no const binder is active.
    eval_env: Option<Env>,
    /// The consuming threshold layout, if one item qualified.
    consume: Option<ConsumePlan>,
    /// The consuming chain has been emitted (duplicate-item guard).
    consume_done: bool,
    /// The final require item left its value as the script result.
    tail_result: bool,
    diags: Vec<Diagnostic>,
    /// Witness array-element slots proven dead: omitted from the layout AND the
    /// comprehension fold (their value cannot affect the spend).
    dead_slots: BTreeSet<String>,
    /// Scalar `Bytes`/`Hash` witness slots whose length airlock has not yet been
    /// emitted. Their airlock is INTERLEAVED -- emitted in place the first time
    /// the body brings the value to the top to consume it -- so two preimages no
    /// longer force a PICK/SWAP/DROP up front (matching rust-miniscript's leaf).
    /// A live scalar `Bytes`/`Hash` slot is always consumed (dead ones are
    /// eliminated), so every entry is drained by the body. Maps slot -> length.
    pending_airlock: BTreeMap<String, i64>,
}

impl<'a> Lowerer<'a> {
    fn error(&mut self, code: &'static str, msg: impl Into<String>, span: Span) {
        self.diags.push(Diagnostic::error(code, msg, span));
    }

    /// Warn, per array, that provably-dead witness elements were dropped.
    fn warn_dead_witness(&mut self, s: &Spend) {
        if self.dead_slots.is_empty() {
            return;
        }
        let mut by_array: BTreeMap<String, usize> = BTreeMap::new();
        for slot in &self.dead_slots {
            if let Some(idx) = slot.rfind('[') {
                *by_array.entry(slot[..idx].to_string()).or_insert(0) += 1;
            }
        }
        for (arr, count) in by_array {
            let span = s
                .params
                .iter()
                .find(|p| p.name.text == arr)
                .map(|p| p.name.span)
                .unwrap_or(s.name.span);
            let total = self
                .sig
                .params
                .iter()
                .find(|p| p.name == arr)
                .and_then(|p| array_len_of(&p.ty, self.env));
            let of_total = total.map(|t| format!(" of {t}")).unwrap_or_default();
            self.diags.push(
                Diagnostic::warning(
                    "opt/dead-witness",
                    format!(
                        "{count}{of_total} `{arr}` elements are dead and dropped from the script and witness"
                    ),
                    span,
                )
                .with_note("their value cannot affect whether the spend succeeds"),
            );
        }
    }

    /// Const-evaluate under the instantiated env merged with the active
    /// const binders (diagnostics from the speculative attempt are
    /// discarded; earlier phases own them).
    fn eval(&self, e: &Expr) -> Option<ConstValue> {
        eval_in_env(e, self.eval_env.as_ref().unwrap_or(self.env)).0
    }

    /// Rebuild the merged eval env from the active binders. Called when
    /// comprehension binders change (per unrolled element).
    fn rebuild_eval_env(&mut self) {
        let consts: Vec<(String, ConstValue)> = self
            .binders
            .iter()
            .filter_map(|(k, v)| match v {
                BinderVal::Const(c) => Some((k.clone(), c.clone())),
                BinderVal::Slot(_) => None,
            })
            .collect();
        self.eval_env = if consts.is_empty() {
            None
        } else {
            let mut env = self.env.clone();
            env.extend(consts);
            Some(env)
        };
    }

    // --- model-coupled emission helpers ---

    fn emit(&mut self, op: Op) {
        self.ops.push(op);
    }
    /// Emit an op that pushes one Temp.
    fn emit_push(&mut self, op: Op) {
        self.ops.push(op);
        self.stack.push(Slot::Temp);
    }
    /// Emit an op that pops `n` and pushes one Temp (binary/unary results).
    fn emit_op(&mut self, op: Op, pops: usize) {
        self.ops.push(op);
        for _ in 0..pops {
            // The pop MUST run in every build: it is the model mutation, not the
            // check. Keeping it outside the debug_assert is load-bearing -- a
            // `debug_assert!(self.stack.pop()...)` elides the pop in release, so
            // the model never shrinks and downstream indexing traps (a
            // release-only bug the debug-only test suite cannot see).
            let popped = self.stack.pop();
            debug_assert!(popped.is_some(), "stack model underflow");
        }
        self.stack.push(Slot::Temp);
    }
    /// Emit an op that pops `n` and pushes nothing (VERIFY family, DROP).
    fn emit_pop(&mut self, op: Op, pops: usize) {
        self.ops.push(op);
        for _ in 0..pops {
            // See emit_op: the pop must run in release too, not just in the assert.
            let popped = self.stack.pop();
            debug_assert!(popped.is_some(), "stack model underflow");
        }
    }
    /// SWAP: net-zero, reorders the top two model slots.
    fn emit_swap(&mut self) {
        self.ops.push(Op::Swap);
        let n = self.stack.len();
        debug_assert!(n >= 2, "swap on short stack");
        if n >= 2 {
            self.stack.swap(n - 1, n - 2);
        }
    }

    fn depth_of(&self, name: &str) -> Option<usize> {
        self.stack
            .iter()
            .rev()
            .position(|s| matches!(s, Slot::Named(n) if n == name))
    }

    /// Copy a named slot to the top.
    fn pick(&mut self, name: &str, span: Span) -> Result<(), ()> {
        let Some(depth) = self.depth_of(name) else {
            self.error(
                "lower/internal",
                format!("`{name}` has no stack slot"),
                span,
            );
            return Err(());
        };
        self.emit_push(Op::PushNum(depth as i64));
        // PICK pops the depth operand and pushes the copy: net stays +1.
        self.emit(Op::Pick);
        Ok(())
    }

    // --- the leaf ---

    fn spend(&mut self, s: &Spend) -> Option<(Vec<Op>, Vec<String>)> {
        // The guaranteed threshold lowering's consuming layout, if any
        // require item qualifies.
        self.consume = self.plan_consumption(s);

        // Provably-dead witness elements (e.g. zero-weight comprehension guard
        // pixels): dropped from the layout AND the fold. The SAME criterion runs
        // in the certifier (crate::verify::decide), so it proves the reduced script
        // against the reduced predicate.
        self.dead_slots = dead_witness_slots(s, self.sig, self.env);
        self.warn_dead_witness(s);

        // Witness layout. With a chain-consume present: declaration order,
        // first param deepest, chain-consumed slots laid out in reverse chain
        // order on top (left undisturbed below). Without one: a
        // reverse-consumption layout -- signatures, consumed last by CHECKSIG,
        // go deepest and other params shallower, so the optimizer consumes each
        // off the stack top with no ROLL (mirage's and htlc.swap's stray
        // `1 ROLL` vanish). Witness order is free -- only determinism and
        // disclosure constrain it -- and a stable partition keeps declaration
        // order within each group.
        let mut witness_order = Vec::new();
        let params = self.sig.params.clone();
        let covered: Vec<String> = self
            .consume
            .as_ref()
            .map(|p| p.covered.clone())
            .unwrap_or_default();
        let mut consume_emitted = false;
        let pairs: Vec<_> = if covered.is_empty() {
            // Reverse-consumption layout over ALL witness params: the param a
            // check/hash consumes FIRST goes on top, the last-consumed deepest, so
            // every consuming op eats off the stack top with no SWAP/ROLL/PICK.
            // Signatures still sit deepest because sig checks are emitted last
            // (item_tail_rank); two preimages now lay out in consumption order so
            // their interleaved airlock+hash run back-to-back with no leading
            // SWAP. Unconsumed params sit deepest; a stable sort keeps declaration
            // order among ties (so the result is canonical).
            let consume_order = param_consumption_order(s);
            let rank = |name: &str| consume_order.iter().position(|c| c == name);
            let mut all: Vec<_> = params.iter().zip(&s.params).collect();
            all.sort_by(|(a, _), (b, _)| match (rank(&a.name), rank(&b.name)) {
                (Some(ia), Some(ib)) => ib.cmp(&ia), // later-consumed deeper
                (Some(_), None) => std::cmp::Ordering::Greater, // unconsumed deepest
                (None, Some(_)) => std::cmp::Ordering::Less,
                (None, None) => std::cmp::Ordering::Equal, // keep declaration order
            });
            all
        } else {
            params.iter().zip(&s.params).collect()
        };
        for (p, ast_p) in pairs {
            if covered.contains(&p.name) {
                if !consume_emitted {
                    let chain = self
                        .consume
                        .as_ref()
                        .map(|c| c.chain.clone())
                        .unwrap_or_default();
                    for (_, slot) in chain.iter().rev() {
                        witness_order.push(slot.clone());
                        self.stack.push(Slot::Named(slot.clone()));
                    }
                    consume_emitted = true;
                }
                continue;
            }
            match &p.ty {
                Ty::Array(_, _) => {
                    let n = self.array_len(&p.ty, ast_p.name.span).ok()?;
                    // Comprehensions fold an array index-ascending. Without a
                    // chain-consume, lay element 0 on TOP (reverse index order)
                    // so each element is at depth 1 when the fold reaches it --
                    // the lift becomes a depth-1 ROLL (a SWAP) instead of a deep
                    // ROLL past every not-yet-consumed element. (With a chain
                    // layout, leave order alone.)
                    let order: Box<dyn Iterator<Item = usize>> = if covered.is_empty() {
                        Box::new((0..n).rev())
                    } else {
                        Box::new(0..n)
                    };
                    for i in order {
                        let slot = format!("{}[{i}]", p.name);
                        if self.dead_slots.contains(&slot) {
                            continue; // provably dead: not provided, not on the stack
                        }
                        witness_order.push(slot.clone());
                        self.stack.push(Slot::Named(slot));
                    }
                }
                _ => {
                    witness_order.push(p.name.clone());
                    self.stack.push(Slot::Named(p.name.clone()));
                }
            }
        }

        // Airlocks.
        let if_only_bools = self.if_position_only_bools(s);
        for (p, ast_p) in params.iter().zip(&s.params) {
            let span = ast_p.name.span;
            match &p.ty {
                // Scalar Bytes/Hash: defer to an INTERLEAVED airlock emitted in
                // place at first consumption (see `airlock_pending`), so multiple
                // preimages don't force a PICK/SWAP/DROP up front. PublicKey stays
                // a batch airlock (keys are pushed via push_key, not push_value).
                Ty::Bytes(_) | Ty::Hash(_) => {
                    let n = self.byte_len(&p.ty, span).ok()?;
                    self.pending_airlock.insert(p.name.clone(), n);
                }
                Ty::PublicKey => {
                    let n = self.byte_len(&p.ty, span).ok()?;
                    self.airlock_size(&p.name, n, span).ok()?;
                }
                Ty::Bool if !if_only_bools.contains(&p.name) => {
                    self.airlock_bool(&p.name, span).ok()?;
                }
                Ty::Array(elem, _) => {
                    let n = self.array_len(&p.ty, span).ok()?;
                    match elem.as_ref() {
                        Ty::Bytes(_) | Ty::Hash(_) | Ty::PublicKey => {
                            let len = self.byte_len(elem, span).ok()?;
                            for i in 0..n {
                                self.airlock_size(&format!("{}[{i}]", p.name), len, span)
                                    .ok()?;
                            }
                        }
                        Ty::Bool if !if_only_bools.contains(&p.name) => {
                            for i in 0..n {
                                self.airlock_bool(&format!("{}[{i}]", p.name), span).ok()?;
                            }
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }

        // Body. A `require` block is a conjunction, so its items may be emitted
        // in any order. We run the verify-only items (`after` timelocks, which
        // leave nothing on the stack) first and a value-producing item last, so
        // the trailing require's final item lands in tail position and its
        // boolean IS the leaf result -- no `DROP ... DROP 1` cleanup, and the
        // output no longer depends on the source order of the conjuncts. This is
        // semantically identity; the certifier re-proves the reordered leaf
        // against the predicate (T1) and the optimizer against the naive (T2).
        let last_is_require = matches!(s.body.last(), Some(Stmt::Require(_)));
        let stmt_count = s.body.len();
        for (si, stmt) in s.body.iter().enumerate() {
            match stmt {
                Stmt::Let { name, value, span } => {
                    let is_bytes = self.expr_is_bytes(value);
                    if self.push_value(value).is_err() {
                        return None;
                    }
                    let Some(top) = self.stack.last_mut() else {
                        self.error("lower/internal", "let produced no value", *span);
                        return None;
                    };
                    *top = Slot::Named(name.text.clone());
                    self.lets_bytes.insert(name.text.clone(), is_bytes);
                }
                Stmt::Require(req) => {
                    // Emission order by tail-rank (see `item_tail_rank`):
                    // timelocks first, then hashlocks / other value-producers,
                    // then signature checks last so a signature is the tail and
                    // the preimages above it airlock in place -- no juggle. A
                    // stable sort keeps source order within each rank, so the
                    // leaf is canonical (independent of conjunct source order).
                    let mut ordered: Vec<&Expr> = req.items.iter().collect();
                    ordered.sort_by_key(|it| item_tail_rank(it));
                    // Only the last item of the body's last require can be tail.
                    let tail: Option<&Expr> = if last_is_require && si + 1 == stmt_count {
                        ordered.last().copied()
                    } else {
                        None
                    };
                    for item in &ordered {
                        let is_tail = tail.is_some_and(|t| std::ptr::eq(t, *item));
                        let start = self.ops.len();
                        if self.require_item(item, is_tail).is_err() {
                            return None;
                        }
                        // An always-true item is dead weight; record its op
                        // range so the optimizer can drop it. Never the tail
                        // (its value is the leaf result).
                        if !is_tail && self.dead.contains(&item.span()) {
                            self.removable.push((start, self.ops.len()));
                        }
                    }
                }
            }
        }

        // Safety net: a deferred Bytes/Hash airlock the body never consumed (a
        // rare dead-but-not-eliminated scalar) still needs its length check to
        // match the typed predicate, or the leaf would under-constrain the
        // witness. Emit the copy-form airlock for any leftover before CLEANSTACK.
        if !self.pending_airlock.is_empty() {
            let leftover: Vec<(String, i64)> = self
                .pending_airlock
                .iter()
                .map(|(k, v)| (k.clone(), *v))
                .collect();
            for (slot, n) in leftover {
                self.pending_airlock.remove(&slot);
                let span = s
                    .params
                    .iter()
                    .find(|p| p.name.text == slot)
                    .map_or(s.name.span, |p| p.name.span);
                self.airlock_size(&slot, n, span).ok()?;
            }
        }

        // CLEANSTACK: the tail item's value IS the result, or drop every
        // remaining slot and leave exactly one truthy.
        if self.tail_result {
            debug_assert_eq!(self.stack.len(), 1, "tail result must stand alone");
        } else {
            while self.stack.len() >= 2 {
                self.emit_pop(Op::Drop2, 2);
            }
            if self.stack.len() == 1 {
                self.emit_pop(Op::Drop, 1);
            }
            self.emit_push(Op::PushNum(1));
        }
        debug_assert_eq!(self.stack.len(), 1, "CLEANSTACK model violated");

        Some((std::mem::take(&mut self.ops), witness_order))
    }

    fn array_len(&mut self, ty: &Ty, span: Span) -> Result<usize, ()> {
        match ty {
            Ty::Array(_, crate::analysis::sema::Len::Lit(n)) => Ok(*n as usize),
            Ty::Array(_, crate::analysis::sema::Len::Named(n)) => match self.env.get(n) {
                Some(ConstValue::Int(v)) if *v >= 0 => Ok(*v as usize),
                _ => {
                    self.error(
                        "lower/internal",
                        format!("array length `{n}` did not instantiate"),
                        span,
                    );
                    Err(())
                }
            },
            _ => {
                self.error("lower/internal", "not an array type", span);
                Err(())
            }
        }
    }

    fn byte_len(&mut self, ty: &Ty, span: Span) -> Result<i64, ()> {
        use crate::analysis::sema::{HashAlg, Len};
        match ty {
            Ty::PublicKey => Ok(32),
            Ty::Bytes(Len::Lit(n)) => Ok(*n as i64),
            Ty::Bytes(Len::Named(n)) => match self.env.get(n) {
                Some(ConstValue::Int(v)) if *v >= 0 => Ok(*v as i64),
                _ => {
                    self.error(
                        "lower/internal",
                        format!("byte length `{n}` did not instantiate"),
                        span,
                    );
                    Err(())
                }
            },
            Ty::Hash(HashAlg::Sha256 | HashAlg::Hash256) => Ok(32),
            Ty::Hash(_) => Ok(20),
            _ => {
                self.error("lower/internal", "type has no byte length", span);
                Err(())
            }
        }
    }

    /// The never-elided length airlock. `OP_SIZE` is non-consuming, so when the
    /// value is already on top we check it IN PLACE -- `SIZE <n> EQUALVERIFY` --
    /// with no PICK-copy and no trailing DROP (it stays on the stack for its
    /// later consuming use). Off the top it falls back to the copy form
    /// `PICK SIZE <n> EQUALVERIFY DROP`. (The check itself is never removed --
    /// proving it redundant would mean inverting the hash; it enforces Bytes<N>.)
    /// `EQUALVERIFY` (not `NUMEQUALVERIFY`): `OP_SIZE` and a minimal `<n>` push
    /// share their byte encoding, so the bytewise compare is identical to the
    /// numeric one for any valid length -- and it matches rust-miniscript. The
    /// certifier recognises `SIZE <n> EQUALVERIFY` as the numeric length check
    /// (see `decode_to_sym`), so the proof still unifies with the typed domain.
    fn airlock_size(&mut self, slot: &str, n: i64, span: Span) -> Result<(), ()> {
        let in_place = self.depth_of(slot) == Some(0);
        if !in_place {
            self.pick(slot, span)?;
        }
        self.emit_op(Op::Size, 0); // pushes len without popping: model +1
        self.emit_push(Op::PushNum(n));
        self.emit_pop(Op::EqualVerify, 2);
        if !in_place {
            self.emit_pop(Op::Drop, 1); // discard the PICK copy
        }
        Ok(())
    }

    /// Interleaved length airlock: the first time a deferred scalar Bytes/Hash
    /// witness slot reaches the stack top (just brought up to be consumed), check
    /// its length IN PLACE -- `SIZE <n> EQUALVERIFY` -- then forget it. `OP_SIZE`
    /// is non-consuming, so the value stays on top for its consuming use (the
    /// hash/compare). No-op for a slot already airlocked or never deferred. This
    /// is what removes the up-front PICK/SWAP/DROP for a second preimage.
    fn airlock_pending(&mut self, name: &str) {
        if let Some(n) = self.pending_airlock.remove(name) {
            self.emit_op(Op::Size, 0); // push len, value stays: model +1
            self.emit_push(Op::PushNum(n));
            self.emit_pop(Op::EqualVerify, 2);
        }
    }

    /// Bool canonicality ({} or 0x01) for params used outside IF-position
    /// (MINIMALIF covers guards for free). On top, check in place with
    /// `DUP DUP 0NOTEQUAL EQUALVERIFY` (a fresh copy to consume, the value
    /// preserved); off the top, `PICK DUP 0NOTEQUAL EQUALVERIFY`.
    fn airlock_bool(&mut self, slot: &str, span: Span) -> Result<(), ()> {
        if self.depth_of(slot) == Some(0) {
            self.emit_op(Op::Dup, 0); // preserve the value; check a copy
        } else {
            self.pick(slot, span)?;
        }
        self.emit_op(Op::Dup, 0);
        self.emit_op(Op::ZeroNotEqual, 1);
        self.emit_pop(Op::EqualVerify, 2);
        Ok(())
    }

    /// Bool params whose every use is a bare IF condition (where-guard binder
    /// over the array, or bare select condition); MINIMALIF makes their
    /// airlock free.
    fn if_position_only_bools(&self, s: &Spend) -> Vec<String> {
        let mut bool_params: Vec<String> = self
            .sig
            .params
            .iter()
            .filter(|p| {
                matches!(&p.ty, Ty::Bool) || matches!(&p.ty, Ty::Array(e, _) if **e == Ty::Bool)
            })
            .map(|p| p.name.clone())
            .collect();
        // Disqualify any param with a non-guard use.
        let mut disqualify = |name: &str| bool_params.retain(|p| p != name);
        for stmt in &s.body {
            let exprs: Vec<&Expr> = match stmt {
                Stmt::Let { value, .. } => vec![value],
                Stmt::Require(req) => req.items.iter().collect(),
            };
            for e in exprs {
                walk_guard_uses(e, &mut |name, in_guard_position| {
                    if !in_guard_position {
                        disqualify(name);
                    }
                });
            }
        }
        bool_params
    }

    // --- the consuming threshold plan ---

    /// Find the first require item eligible for the consuming chain layout:
    /// an all-`check` threshold over const keys whose signature slots are
    /// single-use trailing parameters. Returns None when no item qualifies;
    /// the copy-based fallback handles everything else.
    fn plan_consumption(&mut self, s: &Spend) -> Option<ConsumePlan> {
        for stmt in &s.body {
            let Stmt::Require(req) = stmt else { continue };
            for item in &req.items {
                if let Some(plan) = self.consumable_threshold(item, s) {
                    return Some(plan);
                }
            }
        }
        None
    }

    fn consumable_threshold(&mut self, item: &Expr, s: &Spend) -> Option<ConsumePlan> {
        let Expr::Compare { first, rest, .. } = item else {
            return None;
        };
        let [(op, bound)] = rest.as_slice() else {
            return None;
        };
        if !matches!(op, CmpOp::Ge | CmpOp::Gt | CmpOp::Eq) {
            return None;
        }
        // The spec contract is for const k.
        if !matches!(self.eval(bound), Some(ConstValue::Int(_))) {
            return None;
        }

        // Extract (key bytes, sig slot name) pairs + covered param names.
        let (pairs, covered) = self.threshold_pairs(first)?;
        if pairs.is_empty() {
            return None;
        }
        // Slot names must be distinct (e.g. `a.check(s) + b.check(s)` reuses
        // one slot: copy-based only).
        let mut names: Vec<&str> = pairs.iter().map(|(_, s)| s.as_str()).collect();
        names.sort_unstable();
        names.dedup();
        if names.len() != pairs.len() {
            return None;
        }
        // Covered params must be the trailing declared parameters: their
        // slots must sit on top of the stack with nothing above.
        let n = self.sig.params.len();
        if covered.len() > n {
            return None;
        }
        let trailing = self.sig.params[n - covered.len()..]
            .iter()
            .map(|p| p.name.as_str());
        if covered.iter().map(String::as_str).ne(trailing) {
            return None;
        }
        // Single-use: no covered name may appear anywhere outside this item.
        for stmt in &s.body {
            let exprs: Vec<&Expr> = match stmt {
                Stmt::Let { value, .. } => vec![value],
                Stmt::Require(req) => req
                    .items
                    .iter()
                    .filter(|i| !std::ptr::eq(*i, item))
                    .collect(),
            };
            for e in exprs {
                let mut used = false;
                walk_guard_uses(e, &mut |name, _| {
                    used |= covered.iter().any(|c| c == name);
                });
                if used {
                    return None;
                }
            }
        }

        // Lexicographic chain order (stable: duplicate keys keep pairing).
        let mut chain = pairs;
        chain.sort_by(|(a, _), (b, _)| a.cmp(b));
        Some(ConsumePlan {
            item: item.clone(),
            chain,
            covered,
        })
    }

    /// (key bytes, slot name) pairs for both threshold spellings, plus the
    /// covered parameter names in declaration order. None when any key is
    /// not const bytes, or any signature operand is not a witness slot.
    fn threshold_pairs(&mut self, sum: &Expr) -> Option<(ThresholdPairs, Vec<String>)> {
        // Comprehension spelling: sum(k in keys, s in sigs => k.check(s)).
        if let Expr::Comprehension {
            callee,
            binders,
            where_clauses,
            body,
            ..
        } = sum
        {
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
            let (Expr::Name(kb), Expr::Name(sb)) = (base.as_ref(), &args[0].value) else {
                return None;
            };
            let mut keys: Option<Vec<Vec<u8>>> = None;
            let mut sigs: Option<String> = None;
            for b in binders {
                let Seq::Expr(seq) = &b.seq else { return None };
                if b.name.text == kb.text {
                    let Some(ConstValue::Array(items)) = self.eval(seq) else {
                        return None;
                    };
                    let mut bytes = Vec::with_capacity(items.len());
                    for it in items {
                        let ConstValue::Bytes(b) = it else {
                            return None;
                        };
                        bytes.push(b);
                    }
                    keys = Some(bytes);
                }
                if b.name.text == sb.text {
                    let Expr::Name(arr) = seq else { return None };
                    let p = self.sig.params.iter().find(|p| p.name == arr.text)?;
                    if !matches!(&p.ty, Ty::Array(e, _) if **e == Ty::Signature) {
                        return None;
                    }
                    sigs = Some(arr.text.clone());
                }
            }
            let (keys, sigs) = (keys?, sigs?);
            let n = self.array_len_quiet(&sigs)?;
            if keys.len() != n {
                return None;
            }
            let pairs = keys
                .into_iter()
                .enumerate()
                .map(|(i, k)| (k, format!("{sigs}[{i}]")))
                .collect();
            return Some((pairs, vec![sigs]));
        }
        // Explicit spelling: an Add-tree of checks over scalar sig params.
        let mut tree: Vec<(Expr, Expr)> = Vec::new();
        if !collect_checks_tree(sum, &mut tree) || tree.is_empty() {
            return None;
        }
        let mut pairs = Vec::with_capacity(tree.len());
        let mut covered = Vec::new();
        for (key, sig) in &tree {
            let Some(ConstValue::Bytes(kb)) = self.eval(key) else {
                return None;
            };
            let Expr::Name(sn) = sig else { return None };
            let p = self.sig.params.iter().find(|p| p.name == sn.text)?;
            if p.ty != Ty::Signature {
                return None;
            }
            pairs.push((kb, sn.text.clone()));
        }
        // Covered = the named params, in declaration order.
        for p in &self.sig.params {
            if pairs.iter().any(|(_, s)| s == &p.name) {
                covered.push(p.name.clone());
            }
        }
        Some((pairs, covered))
    }

    /// Array length lookup without diagnostics (recognition probes).
    fn array_len_quiet(&self, name: &str) -> Option<usize> {
        let p = self.sig.params.iter().find(|p| p.name == name)?;
        match &p.ty {
            Ty::Array(_, crate::analysis::sema::Len::Lit(n)) => Some(*n as usize),
            Ty::Array(_, crate::analysis::sema::Len::Named(n)) => match self.env.get(n) {
                Some(ConstValue::Int(v)) if *v >= 0 => Some(*v as usize),
                _ => None,
            },
            _ => None,
        }
    }

    /// Emit the consuming chain: keys lexicographic, signatures eaten off
    /// the stack top, zero stack manipulation. In tail position with nothing
    /// else on the stack, the comparison is the leaf result. Returns
    /// Ok(None) when the model's top slots don't match the plan (e.g. a let
    /// intervened); the copy-based fallback takes over.
    fn try_consuming_chain(
        &mut self,
        item: &Expr,
        (op, bound): &(CmpOp, Expr),
        is_tail: bool,
    ) -> Result<Option<()>, ()> {
        if self.consume_done {
            return Ok(None);
        }
        let Some(plan) = &self.consume else {
            return Ok(None);
        };
        if plan.item != *item {
            return Ok(None);
        }
        let chain = plan.chain.clone();
        // The model must show exactly the planned slots on top, in
        // consumption order (chain[0] topmost).
        if self.stack.len() < chain.len() {
            return Ok(None);
        }
        let top = self.stack.len() - 1;
        for (i, (_, slot)) in chain.iter().enumerate() {
            if !matches!(&self.stack[top - i], Slot::Named(n) if n == slot) {
                return Ok(None);
            }
        }
        let cmp = match op {
            CmpOp::Ge => Op::GreaterThanOrEqual,
            CmpOp::Gt => Op::GreaterThan,
            CmpOp::Eq => Op::NumEqual,
            _ => return Ok(None),
        };
        self.consume_done = true;
        let n = chain.len();
        // n-of-n (`== n`, or `>= n` which is equivalent since the count cannot
        // exceed n) is a pure conjunction: every signature must verify. Emit the
        // AND-chain `<k0> CHECKSIGVERIFY .. <k_{n-1}> CHECKSIG` -- the same form a
        // hand-written `k0.check(s0) && .. && kn.check(sn)` lowers to, and the
        // form rust-miniscript collapses n-of-n to -- instead of the CHECKSIGADD
        // tally plus `<n> NUMEQUAL`. Both consume the same sig slots off the top
        // in chain order; the AND-chain just drops the dead count (-2 bytes).
        let n_of_n = matches!(op, CmpOp::Eq | CmpOp::Ge)
            && matches!(self.eval(bound), Some(ConstValue::Int(b)) if b == n as i128);
        if n_of_n {
            for (i, (key, _)) in chain.iter().enumerate() {
                self.emit_push(Op::Push(key.clone()));
                if i + 1 < n {
                    self.emit_pop(Op::CheckSigVerify, 2); // consumes (pk, sig)
                } else {
                    self.emit_op(Op::CheckSig, 2); // last: leaves the bool result
                }
            }
            if is_tail && self.stack.len() == 1 {
                self.tail_result = true; // the final CHECKSIG is the leaf result
            } else {
                self.emit_pop(Op::Verify, 1);
            }
            return Ok(Some(()));
        }
        for (i, (key, _)) in chain.iter().enumerate() {
            self.emit_push(Op::Push(key.clone()));
            if i == 0 {
                // CHECKSIG pops (pk, sig): consumes the top slot.
                self.emit_op(Op::CheckSig, 2);
            } else {
                // CHECKSIGADD pops (pk, n, sig): consumes the next slot.
                self.emit_op(Op::CheckSigAdd, 3);
            }
        }
        self.push_value(bound)?;
        self.emit_op(cmp, 2);
        if is_tail && self.stack.len() == 1 {
            self.tail_result = true; // the comparison is the leaf result
        } else {
            self.emit_pop(Op::Verify, 1);
        }
        Ok(Some(()))
    }

    // --- require items ---

    fn require_item(&mut self, item: &Expr, is_tail: bool) -> Result<(), ()> {
        // after(lock): operand push + CLTV/CSV + DROP.
        if let Expr::Call { callee, args, span } = item {
            if let Expr::Name(f) = callee.as_ref()
                && f.text == "after"
                && args.len() == 1
            {
                return self.lower_after(&args[0].value, *span);
            }
            // Bare check: fused CHECKSIGVERIFY.
            if let Some(()) = self.try_check(item, true)? {
                return Ok(());
            }
        }
        // Threshold: the consuming chain (the cost contract) when planned
        // and the stack cooperates; copy-based chain otherwise.
        if let Expr::Compare { first, rest, .. } = item
            && rest.len() == 1
        {
            if let Some(()) = self.try_consuming_chain(item, &rest[0], is_tail)? {
                return Ok(());
            }
            if let Some(()) = self.try_threshold(first, &rest[0])? {
                return Ok(());
            }
            // Fused equality verify.
            if rest[0].0 == CmpOp::Eq {
                self.push_value(first)?;
                self.push_value(&rest[0].1)?;
                let op = if self.expr_is_bytes(first) || self.expr_is_bytes(&rest[0].1) {
                    Op::EqualVerify
                } else {
                    Op::NumEqualVerify
                };
                self.emit_pop(op, 2);
                return Ok(());
            }
            // Single comparison (Lt/Le/Gt/Ge/Ne): lower the subject, record
            // its op-range, then the bound and the comparison. The emitted
            // ops are byte-identical to the general `push_value(item)` path
            // below; the recorded range only lets the optimizer share a
            // subject that two adjacent items would otherwise each recompute.
            let cmp = match rest[0].0 {
                CmpOp::Lt => Some(Op::LessThan),
                CmpOp::Le => Some(Op::LessThanOrEqual),
                CmpOp::Gt => Some(Op::GreaterThan),
                CmpOp::Ge => Some(Op::GreaterThanOrEqual),
                CmpOp::Ne => Some(Op::NumNotEqual),
                CmpOp::Eq => None, // handled above; fall through defensively
            };
            // Only a witness-dependent subject is worth recording: a const
            // subject folds to a literal (cheaper than a kept copy). The guard
            // also keeps the oracle exact -- a non-const `first` implies the
            // whole comparison does not fold, so this split emits the same ops
            // the general `push_value(item)` path would; a fully-const item
            // (which that path folds to one literal) is left to it untouched.
            if let Some(cmp) = cmp
                && self.eval(first).is_none()
            {
                let subj_start = self.ops.len();
                self.push_value(first)?;
                let subj_end = self.ops.len();
                self.push_value(&rest[0].1)?;
                self.emit_op(cmp, 2);
                self.emit_pop(Op::Verify, 1);
                self.cse_subjects.push(CseSubject {
                    subject: (subj_start, subj_end),
                    item_end: self.ops.len(),
                });
                return Ok(());
            }
        }
        // General: value + VERIFY.
        self.push_value(item)?;
        self.emit_pop(Op::Verify, 1);
        Ok(())
    }

    fn lower_after(&mut self, lock: &Expr, span: Span) -> Result<(), ()> {
        let (v, diags) = eval_in_env(lock, self.env);
        self.diags.extend(diags);
        let n = match v {
            Some(ConstValue::LockAbs(LockAbs::Height(h))) => h as i64,
            Some(ConstValue::LockAbs(LockAbs::Time(t))) => t as i64,
            Some(ConstValue::LockRel(LockRel::Blocks(b))) => b as i64,
            // BIP68: the time-type flag is bit 22.
            Some(ConstValue::LockRel(LockRel::Units(u))) => (u as i64) | (1 << 22),
            _ => {
                self.error("lower/internal", "timelock value did not evaluate", span);
                return Err(());
            }
        };
        let is_rel = matches!(v, Some(ConstValue::LockRel(_)));
        self.emit_push(Op::PushNum(n));
        self.emit(if is_rel { Op::Csv } else { Op::Cltv }); // leaves operand
        self.emit_pop(Op::Drop, 1);
        Ok(())
    }

    /// `k.check(s)`: push sig, push key, CHECKSIG(VERIFY). Returns
    /// Ok(Some(())) when the shape matched and was emitted.
    fn try_check(&mut self, e: &Expr, verify: bool) -> Result<Option<()>, ()> {
        let Expr::Call { callee, args, span } = e else {
            return Ok(None);
        };
        let Expr::Member { base, member, .. } = callee.as_ref() else {
            return Ok(None);
        };
        if member.text != "check" || args.len() != 1 {
            return Ok(None);
        }
        self.push_value(&args[0].value)?; // signature
        self.push_key(base, *span)?;
        if verify {
            self.emit_pop(Op::CheckSigVerify, 2);
        } else {
            self.emit_op(Op::CheckSig, 2);
        }
        Ok(Some(()))
    }

    /// Push a key operand: const key bytes, pinned witness key slot, or a
    /// const array element.
    fn push_key(&mut self, base: &Expr, span: Span) -> Result<(), ()> {
        // Binder indirection first (comprehension thresholds).
        if let Expr::Name(n) = base
            && let Some(b) = self.binders.get(&n.text).cloned()
        {
            return match b {
                BinderVal::Const(ConstValue::Bytes(bytes)) => {
                    self.emit_push(Op::Push(bytes));
                    Ok(())
                }
                BinderVal::Slot(slot) => self.pick(&slot, span),
                _ => {
                    self.error("lower/internal", "binder is not a key", span);
                    Err(())
                }
            };
        }
        match self.eval(base) {
            Some(ConstValue::Bytes(bytes)) => {
                self.emit_push(Op::Push(bytes));
                Ok(())
            }
            _ => match base {
                Expr::Name(n) => self.pick(&n.text, span),
                _ => {
                    self.error("lower/internal", "unsupported key expression", span);
                    Err(())
                }
            },
        }
    }

    /// The copy-based threshold chain (the fallback when the consuming
    /// layout doesn't apply): signatures accessed by PICK,
    /// `<s1> <k1> CHECKSIG <s2> SWAP <k2> CHECKSIGADD ... <k> NUMEQUAL/GTE VERIFY`.
    /// Both spellings, the explicit Add-tree and the comprehension form,
    /// lower to the identical chain; keys are emitted lexicographically
    /// whenever all of them are const (canonical ordering).
    fn try_threshold(&mut self, sum: &Expr, (op, bound): &(CmpOp, Expr)) -> Result<Option<()>, ()> {
        let cmp = match op {
            CmpOp::Ge => Op::GreaterThanOrEqual,
            CmpOp::Eq => Op::NumEqual,
            CmpOp::Gt => Op::GreaterThan,
            _ => return Ok(None),
        };
        // Each slot: (key operand, sig operand) as pushable specs.
        let mut slots: Vec<(PushSpec, PushSpec)> =
            if let Some(slots) = self.comprehension_slots(sum)? {
                slots
            } else {
                let mut pairs: Vec<(Expr, Expr)> = Vec::new();
                if !collect_checks_tree(sum, &mut pairs) || pairs.is_empty() {
                    return Ok(None);
                }
                pairs
                    .into_iter()
                    .map(|(k, s)| (PushSpec::Expr(k), PushSpec::Expr(s)))
                    .collect()
            };
        if slots.is_empty() {
            return Ok(None);
        }
        // Canonical key ordering: stable lexicographic sort by key bytes,
        // pairs kept intact. Skipped when any key isn't const (the chain
        // then follows written order; correctness unaffected).
        let key_bytes: Vec<Option<Vec<u8>>> =
            slots.iter().map(|(k, _)| self.spec_key_bytes(k)).collect();
        if key_bytes.iter().all(Option::is_some) {
            let mut keyed: Vec<(Vec<u8>, (PushSpec, PushSpec))> = key_bytes
                .into_iter()
                .map(|b| b.unwrap_or_default())
                .zip(slots)
                .collect();
            keyed.sort_by(|(a, _), (b, _)| a.cmp(b));
            slots = keyed.into_iter().map(|(_, s)| s).collect();
        }
        let span = sum.span();
        let mut first = true;
        for (key, sig_s) in &slots {
            if first {
                self.push_spec(sig_s, span)?;
                self.push_key_spec(key, span)?;
                self.emit_op(Op::CheckSig, 2);
                first = false;
            } else {
                self.push_spec(sig_s, span)?;
                self.emit_swap(); // reorder [n, sig] to [sig, n]
                self.push_key_spec(key, span)?;
                // CHECKSIGADD pops (sig, n, pk), pushes n'.
                self.emit_op(Op::CheckSigAdd, 3);
            }
        }
        self.push_value(bound)?;
        self.emit_op(cmp, 2);
        self.emit_pop(Op::Verify, 1);
        Ok(Some(()))
    }

    /// The comprehension threshold: `sum(k in keys, s in sigs => k.check(s))`
    /// to per-slot (key, sig) specs via the binder element lists.
    fn comprehension_slots(&mut self, sum: &Expr) -> Result<Option<Vec<(PushSpec, PushSpec)>>, ()> {
        let Expr::Comprehension {
            callee,
            binders,
            where_clauses,
            body,
            ..
        } = sum
        else {
            return Ok(None);
        };
        if callee.text != "sum" || !where_clauses.is_empty() {
            return Ok(None);
        }
        let Expr::Call {
            callee: c2, args, ..
        } = body.as_ref()
        else {
            return Ok(None);
        };
        let Expr::Member { base, member, .. } = c2.as_ref() else {
            return Ok(None);
        };
        if member.text != "check" || args.len() != 1 {
            return Ok(None);
        }
        let (Expr::Name(kb), Expr::Name(sb)) = (base.as_ref(), &args[0].value) else {
            return Ok(None);
        };
        let mut keys = None;
        let mut sigs = None;
        for b in binders {
            if b.name.text == kb.text {
                keys = Some(self.binder_elements(b)?);
            }
            if b.name.text == sb.text {
                sigs = Some(self.binder_elements(b)?);
            }
        }
        let (Some(keys), Some(sigs)) = (keys, sigs) else {
            return Ok(None);
        };
        if keys.len() != sigs.len() {
            return Ok(None); // survived analysis only if equal; defensive
        }
        Ok(Some(
            keys.into_iter()
                .zip(sigs)
                .map(|(k, s)| (PushSpec::Val(k), PushSpec::Val(s)))
                .collect(),
        ))
    }

    /// The key bytes of a threshold slot's key spec, if const.
    fn spec_key_bytes(&self, spec: &PushSpec) -> Option<Vec<u8>> {
        match spec {
            PushSpec::Val(BinderVal::Const(ConstValue::Bytes(b))) => Some(b.clone()),
            PushSpec::Expr(e) => match self.eval(e) {
                Some(ConstValue::Bytes(b)) => Some(b),
                _ => None,
            },
            _ => None,
        }
    }

    fn push_spec(&mut self, spec: &PushSpec, span: Span) -> Result<(), ()> {
        match spec {
            PushSpec::Expr(e) => self.push_value(e),
            PushSpec::Val(BinderVal::Slot(slot)) => self.pick(slot, span),
            PushSpec::Val(BinderVal::Const(v)) => self.push_const(v, span),
        }
    }

    fn push_key_spec(&mut self, spec: &PushSpec, span: Span) -> Result<(), ()> {
        match spec {
            PushSpec::Expr(e) => self.push_key(e, e.span()),
            other => self.push_spec(other, span),
        }
    }

    // --- values ---

    /// Lower an expression, leaving exactly one value on the stack.
    fn push_value(&mut self, e: &Expr) -> Result<(), ()> {
        // Binder substitution.
        if let Expr::Name(n) = e
            && let Some(b) = self.binders.get(&n.text).cloned()
        {
            return match b {
                BinderVal::Slot(slot) => self.pick(&slot, n.span),
                BinderVal::Const(v) => self.push_const(&v, n.span),
            };
        }
        // Constant folding: exact values push as literals.
        // Witness-dependent expressions evaluate to None (diagnostics from
        // the speculative attempt are discarded; earlier phases own them).
        if let Some(v) = self.eval(e) {
            return self.push_const(&v, e.span());
        }
        match e {
            Expr::Name(n) => {
                self.pick(&n.text, n.span)?;
                // First time this preimage reaches the top, airlock its length
                // in place (deferred from the batch phase) so its size-check sits
                // right before the hash, not juggled up front.
                self.airlock_pending(&n.text);
                Ok(())
            }
            Expr::Unary { op, operand, .. } => {
                self.push_value(operand)?;
                match op {
                    UnaryOp::Not => self.emit_op(Op::Not, 1),
                    UnaryOp::Neg => self.emit_op(Op::Negate, 1),
                }
                Ok(())
            }
            Expr::Binary { op, lhs, rhs, .. } => {
                // Add is commutative: evaluate a comprehension/fold operand
                // FIRST so its accumulator sits on top of a clean stack and
                // each folded element stays at depth 1 (a SWAP lift, not a deep
                // ROLL past the other operand). Sub is not commutative -- leave
                // its order. Pure operands, so reordering is sound (cf. Compare).
                let fold_first = *op == BinaryOp::Add
                    && matches!(rhs.as_ref(), Expr::Comprehension { .. })
                    && !matches!(lhs.as_ref(), Expr::Comprehension { .. });
                if fold_first {
                    self.push_value(rhs)?;
                    self.push_value(lhs)?;
                } else {
                    self.push_value(lhs)?;
                    self.push_value(rhs)?;
                }
                self.emit_op(
                    if *op == BinaryOp::Add {
                        Op::Add
                    } else {
                        Op::Sub
                    },
                    2,
                );
                Ok(())
            }
            Expr::Compare { first, rest, .. } => {
                // Chains: pairwise comparisons ANDed (operands re-evaluated:
                // pure, so correct; the optimizer dedups later).
                let mut prev: &Expr = first;
                for (i, (op, next)) in rest.iter().enumerate() {
                    self.push_value(prev)?;
                    self.push_value(next)?;
                    let opcode = match op {
                        CmpOp::Lt => Op::LessThan,
                        CmpOp::Le => Op::LessThanOrEqual,
                        CmpOp::Gt => Op::GreaterThan,
                        CmpOp::Ge => Op::GreaterThanOrEqual,
                        CmpOp::Eq => {
                            if self.expr_is_bytes(prev) || self.expr_is_bytes(next) {
                                Op::Equal
                            } else {
                                Op::NumEqual
                            }
                        }
                        CmpOp::Ne => Op::NumNotEqual,
                    };
                    self.emit_op(opcode, 2);
                    if i > 0 {
                        self.emit_op(Op::BoolAnd, 2);
                    }
                    prev = next;
                }
                Ok(())
            }
            Expr::In {
                value,
                lo,
                hi,
                inclusive,
                ..
            } => {
                // `..` is native OP_WITHIN (half-open, zero adjustment).
                // `..=` const-folds `hi+1`; when `hi` is +max or not const,
                // two conjoined comparisons instead: a runtime `1ADD` could
                // exceed the 4-byte WITHIN operand domain.
                if !*inclusive {
                    self.push_value(value)?;
                    self.push_value(lo)?;
                    self.push_value(hi)?;
                    self.emit_op(Op::Within, 3);
                    return Ok(());
                }
                match self.eval(hi) {
                    Some(ConstValue::Int(h)) if h < MACHINE_MAX => {
                        self.push_value(value)?;
                        self.push_value(lo)?;
                        self.emit_push(Op::PushNum(h as i64 + 1));
                        self.emit_op(Op::Within, 3);
                    }
                    _ => {
                        self.push_value(value)?;
                        self.push_value(lo)?;
                        self.emit_op(Op::GreaterThanOrEqual, 2);
                        self.push_value(value)?;
                        self.push_value(hi)?;
                        self.emit_op(Op::LessThanOrEqual, 2);
                        self.emit_op(Op::BoolAnd, 2);
                    }
                }
                Ok(())
            }
            Expr::Index { base, index, span } => {
                // Const arrays fold above; this is a witness-array element.
                let (Expr::Name(arr), Some(ConstValue::Int(i))) = (base.as_ref(), self.eval(index))
                else {
                    self.error("lower/internal", "unsupported index form", *span);
                    return Err(());
                };
                self.pick(&format!("{}[{i}]", arr.text), *span)
            }
            Expr::Call { .. } => self.lower_call(e),
            Expr::Comprehension { .. } => self.lower_comprehension(e),
            other => {
                let (msg, span) = ("expression not lowerable here".to_string(), other.span());
                self.error("lower/internal", msg, span);
                Err(())
            }
        }
    }

    fn push_const(&mut self, v: &ConstValue, span: Span) -> Result<(), ()> {
        match v {
            ConstValue::Int(n) => {
                self.emit_push(Op::PushNum(*n as i64));
                Ok(())
            }
            ConstValue::Bool(b) => {
                self.emit_push(Op::PushNum(*b as i64));
                Ok(())
            }
            ConstValue::Bytes(b) => {
                self.emit_push(Op::Push(b.clone()));
                Ok(())
            }
            _ => {
                self.error("lower/internal", "value has no push form here", span);
                Err(())
            }
        }
    }

    /// Defensive arity gate: sema already validated; never panic regardless.
    fn arity(&mut self, args: &[Arg], n: usize, span: Span) -> Result<(), ()> {
        if args.len() == n {
            Ok(())
        } else {
            self.error("lower/internal", "call arity survived sema", span);
            Err(())
        }
    }

    fn lower_call(&mut self, e: &Expr) -> Result<(), ()> {
        let Expr::Call { callee, args, span } = e else {
            self.error("lower/internal", "not a call", e.span());
            return Err(());
        };
        // key.check(sig) in value position.
        if let Some(()) = self.try_check(e, false)? {
            return Ok(());
        }
        let Expr::Name(f) = callee.as_ref() else {
            self.error("lower/internal", "unsupported call", *span);
            return Err(());
        };
        match f.text.as_str() {
            "min" | "max" => {
                self.arity(args, 2, *span)?;
                self.push_value(&args[0].value)?;
                self.push_value(&args[1].value)?;
                self.emit_op(if f.text == "min" { Op::Min } else { Op::Max }, 2);
                Ok(())
            }
            "abs" => {
                self.arity(args, 1, *span)?;
                self.push_value(&args[0].value)?;
                self.emit_op(Op::Abs, 1);
                Ok(())
            }
            "int" => {
                self.arity(args, 1, *span)?;
                self.push_value(&args[0].value)
            }
            "sha256" | "hash256" | "hash160" | "ripemd160" | "sha1" => {
                self.arity(args, 1, *span)?;
                self.push_value(&args[0].value)?;
                let op = match f.text.as_str() {
                    "sha256" => Op::Sha256,
                    "hash256" => Op::Hash256,
                    "hash160" => Op::Hash160,
                    "ripemd160" => Op::Ripemd160,
                    _ => Op::Sha1,
                };
                self.emit_op(op, 1);
                Ok(())
            }
            "select" => {
                self.arity(args, 3, *span)?;
                self.push_value(&args[0].value)?;
                self.emit_pop(Op::If, 1);
                let depth = self.stack.len();
                self.push_value(&args[1].value)?;
                self.emit(Op::Else);
                debug_assert_eq!(self.stack.len(), depth + 1);
                self.stack.pop(); // model: else-arm replays from the IF state
                self.push_value(&args[2].value)?;
                self.emit(Op::EndIf);
                debug_assert_eq!(self.stack.len(), depth + 1);
                Ok(())
            }
            other => {
                let msg = format!("`{other}` has no lowering yet");
                self.error("lower/internal", msg, *span);
                Err(())
            }
        }
    }

    // --- comprehensions (unrolled) ---

    fn lower_comprehension(&mut self, e: &Expr) -> Result<(), ()> {
        let Expr::Comprehension {
            callee,
            acc,
            binders,
            where_clauses,
            body,
            span,
        } = e
        else {
            self.error("lower/internal", "not a comprehension", e.span());
            return Err(());
        };
        // Materialize binder element lists.
        let mut elems: Vec<(String, Vec<BinderVal>)> = Vec::new();
        let mut n = None;
        for b in binders {
            let vals = self.binder_elements(b)?;
            match n {
                None => n = Some(vals.len()),
                Some(m) if m == vals.len() => {}
                _ => {
                    self.error(
                        "lower/internal",
                        "zip length mismatch survived analysis",
                        *span,
                    );
                    return Err(());
                }
            }
            elems.push((b.name.text.clone(), vals));
        }
        let n = n.unwrap_or(0);
        let agg = callee.text.as_str();

        // Initial accumulator.
        match agg {
            "sum" | "count" => self.emit_push(Op::PushNum(0)),
            "all" => self.emit_push(Op::PushNum(1)),
            "any" => self.emit_push(Op::PushNum(0)),
            "fold" => match acc {
                Some(a) => self.push_value(&a.init)?,
                None => {
                    self.error("lower/internal", "fold without acc survived sema", *span);
                    return Err(());
                }
            },
            _ => {
                self.error("lower/internal", "unknown aggregator survived sema", *span);
                return Err(());
            }
        }
        let acc_name = acc.as_ref().map(|a| a.name.text.clone());

        for i in 0..n {
            // Provably-dead element (a guard slot eliminated up front): its
            // contribution is the identity, so emit nothing -- it is neither on
            // the stack nor in the witness.
            if elems
                .iter()
                .any(|(_, vals)| matches!(&vals[i], BinderVal::Slot(slot) if self.dead_slots.contains(slot)))
            {
                continue;
            }
            let saved: Vec<_> = elems
                .iter()
                .map(|(name, vals)| {
                    (
                        name.clone(),
                        self.binders.insert(name.clone(), vals[i].clone()),
                    )
                })
                .collect();
            self.rebuild_eval_env(); // const binders fold per element
            if let Some(an) = &acc_name {
                match self.stack.last_mut() {
                    Some(top) => *top = Slot::Named(an.clone()),
                    None => {
                        self.error("lower/internal", "accumulator slot missing", *span);
                        return Err(());
                    }
                }
            }

            // Guard: a single bare binder guard goes straight to IF
            // (MINIMALIF); anything else evaluates to a Bool first.
            let guarded = !where_clauses.is_empty();
            if guarded {
                let mut first = true;
                for w in where_clauses {
                    self.push_value(w)?;
                    if !first {
                        self.emit_op(Op::BoolAnd, 2);
                    }
                    first = false;
                }
                self.emit_pop(Op::If, 1);
            }
            let depth = self.stack.len();
            match agg {
                "sum" => {
                    // Instruction selection: a `+1` body is OP_1ADD and a `-1`
                    // body is OP_1SUB, not `<1> ADD` / `<-1> ADD`. The certifier
                    // matches both: decode gives `Add(x,1)` for OP_1ADD, and the
                    // arena canonicalizes OP_1SUB's `Sub(x,1)` to `Add(x,-1)`.
                    match self.eval(body) {
                        Some(ConstValue::Int(1)) => self.emit_op(Op::Add1, 1),
                        Some(ConstValue::Int(-1)) => self.emit_op(Op::Sub1, 1),
                        _ => {
                            self.push_value(body)?;
                            self.emit_op(Op::Add, 2);
                        }
                    }
                }
                "count" => {
                    // A const body needs no inner IF: a truthy body always
                    // increments (the outer guard already gates it), a falsy one
                    // never does. `count(.. where v => true)` thus lowers to a
                    // bare `<v> IF ADD1 ENDIF` instead of a nested IF.
                    match self.eval(body) {
                        Some(ConstValue::Int(n)) if n != 0 => self.emit_op(Op::Add1, 1),
                        Some(ConstValue::Bool(true)) => self.emit_op(Op::Add1, 1),
                        Some(ConstValue::Int(_) | ConstValue::Bool(false)) => {}
                        _ => {
                            self.push_value(body)?;
                            self.emit_pop(Op::If, 1);
                            self.emit_op(Op::Add1, 1);
                            self.emit(Op::EndIf);
                        }
                    }
                }
                "all" => {
                    self.push_value(body)?;
                    self.emit_op(Op::BoolAnd, 2);
                }
                "any" => {
                    self.push_value(body)?;
                    self.emit_op(Op::BoolOr, 2);
                }
                "fold" => {
                    self.push_value(body)?;
                    // OP_NIP is [old_acc, new] -> [new]: it pops TWO and pushes
                    // one. Model it as such (emit_op pops 2, pushes one Temp) so
                    // the surviving slot is the NEW accumulator -- not emit_pop's
                    // single pop, which would leave the model pointing at the
                    // old_acc slot the script just removed. (The relabel below
                    // then names that Temp; both emit one OP_NIP, so the script
                    // bytes are identical -- this only fixes the stack model.)
                    self.emit_op(Op::Nip, 2); // replace old acc with new
                    if let Some(an) = &acc_name {
                        match self.stack.last_mut() {
                            Some(top) => *top = Slot::Named(an.clone()),
                            None => {
                                self.error("lower/internal", "accumulator slot missing", *span);
                                return Err(());
                            }
                        }
                    }
                }
                _ => {
                    self.error("lower/internal", "unknown aggregator survived sema", *span);
                    return Err(());
                }
            }
            debug_assert_eq!(
                self.stack.len(),
                depth,
                "comprehension arm must be balanced"
            );
            if guarded {
                self.emit(Op::EndIf);
            }

            for (name, old) in saved {
                match old {
                    Some(v) => {
                        self.binders.insert(name, v);
                    }
                    None => {
                        self.binders.remove(&name);
                    }
                }
            }
        }
        self.rebuild_eval_env(); // binders restored (outer scope or none)
        // The accumulator is the result: make it a Temp again.
        match self.stack.last_mut() {
            Some(top) => *top = Slot::Temp,
            None => {
                self.error("lower/internal", "accumulator slot missing", *span);
                return Err(());
            }
        }
        Ok(())
    }

    fn binder_elements(&mut self, b: &Binder) -> Result<Vec<BinderVal>, ()> {
        match &b.seq {
            Seq::Range {
                lo,
                hi,
                inclusive,
                span,
            } => {
                let Some(ConstValue::Int(l)) = self.eval(lo) else {
                    self.error("lower/internal", "range bound did not evaluate", *span);
                    return Err(());
                };
                let Some(ConstValue::Int(h)) = self.eval(hi) else {
                    self.error("lower/internal", "range bound did not evaluate", *span);
                    return Err(());
                };
                let end = if *inclusive { h + 1 } else { h };
                Ok((l..end)
                    .map(|v| BinderVal::Const(ConstValue::Int(v)))
                    .collect())
            }
            Seq::Expr(e) => {
                // Const array?
                if let Some(ConstValue::Array(items)) = self.eval(e) {
                    return Ok(items.into_iter().map(BinderVal::Const).collect());
                }
                // Witness array: per-element slots.
                let Expr::Name(arr) = e else {
                    self.error("lower/internal", "unsupported binder sequence", e.span());
                    return Err(());
                };
                let Some(p) = self.sig.params.iter().find(|p| p.name == arr.text) else {
                    self.error("lower/internal", "binder over unknown array", arr.span);
                    return Err(());
                };
                let ty = p.ty.clone();
                let n = self.array_len(&ty, arr.span)?;
                Ok((0..n)
                    .map(|i| BinderVal::Slot(format!("{}[{i}]", arr.text)))
                    .collect())
            }
        }
    }

    /// Byte-flavored operands take OP_EQUAL; numeric take OP_NUMEQUAL.
    fn expr_is_bytes(&self, e: &Expr) -> bool {
        match e {
            Expr::Call { callee, .. } => matches!(
                callee.as_ref(),
                Expr::Name(f) if matches!(
                    f.text.as_str(),
                    "sha256" | "hash256" | "hash160" | "ripemd160" | "sha1" | "PublicKey"
                )
            ),
            Expr::TypedCtor { .. } => true,
            Expr::Str { .. } => true,
            Expr::Name(n) => self.name_is_bytes(&n.text),
            Expr::Index { base, .. } => {
                // An element of a byte-flavored array.
                let Expr::Name(arr) = base.as_ref() else {
                    return false;
                };
                self.array_elem_is_bytes(&arr.text)
            }
            _ => false,
        }
    }

    fn name_is_bytes(&self, name: &str) -> bool {
        // Comprehension binders resolve to their current element.
        if let Some(b) = self.binders.get(name) {
            return match b {
                BinderVal::Const(v) => matches!(v, ConstValue::Bytes(_)),
                BinderVal::Slot(slot) => match slot.split_once('[') {
                    Some((arr, _)) => self.array_elem_is_bytes(arr),
                    None => self.name_is_bytes(slot),
                },
            };
        }
        if let Some(is_bytes) = self.lets_bytes.get(name) {
            return *is_bytes;
        }
        if let Some(p) = self.sig.params.iter().find(|p| p.name == name) {
            return matches!(&p.ty, Ty::Bytes(_) | Ty::Hash(_) | Ty::PublicKey);
        }
        matches!(
            self.info
                .externs
                .iter()
                .chain(&self.info.consts)
                .find(|(n, _)| n == name)
                .map(|(_, t)| t),
            Some(Ty::Bytes(_) | Ty::Hash(_) | Ty::PublicKey)
        )
    }

    fn array_elem_is_bytes(&self, arr: &str) -> bool {
        let elem_of = |t: &Ty| match t {
            Ty::Array(e, _) => matches!(**e, Ty::Bytes(_) | Ty::Hash(_) | Ty::PublicKey),
            _ => false,
        };
        if let Some(p) = self.sig.params.iter().find(|p| p.name == arr) {
            return elem_of(&p.ty);
        }
        self.info
            .externs
            .iter()
            .chain(&self.info.consts)
            .find(|(n, _)| n == arr)
            .is_some_and(|(_, t)| elem_of(t))
    }
}

/// A pushable operand for threshold slots.
enum PushSpec {
    Expr(Expr),
    Val(BinderVal),
}

/// Collect (key, sig) pairs from an explicit check-sum Add-tree. Mirrors
/// the recognition in paths.rs; the comprehension form is handled by
/// [`Lowerer::comprehension_slots`], which has binder machinery.
fn collect_checks_tree(e: &Expr, out: &mut Vec<(Expr, Expr)>) -> bool {
    match e {
        Expr::Binary {
            op: BinaryOp::Add,
            lhs,
            rhs,
            ..
        } => collect_checks_tree(lhs, out) && collect_checks_tree(rhs, out),
        Expr::Call { callee, args, .. } => {
            let Expr::Member { base, member, .. } = callee.as_ref() else {
                return false;
            };
            if member.text != "check" || args.len() != 1 {
                return false;
            }
            out.push(((**base).clone(), args[0].value.clone()));
            true
        }
        _ => false,
    }
}

/// Walk an expression reporting every parameter use to `f(name, in_guard)`,
/// where `in_guard` means the use is a bare IF condition (a where-guard
/// binder over the array, or a bare select condition): the positions where
/// MINIMALIF provides the Bool airlock for free.
fn walk_guard_uses(e: &Expr, f: &mut impl FnMut(&str, bool)) {
    fn resolve<'x>(name: &'x str, map: &'x BTreeMap<String, String>) -> &'x str {
        map.get(name).map(String::as_str).unwrap_or(name)
    }
    fn walk(e: &Expr, map: &BTreeMap<String, String>, f: &mut impl FnMut(&str, bool)) {
        match e {
            Expr::Name(n) => f(resolve(&n.text, map), false),
            Expr::Unary { operand, .. } => walk(operand, map, f),
            Expr::Binary { lhs, rhs, .. } => {
                walk(lhs, map, f);
                walk(rhs, map, f);
            }
            Expr::Compare { first, rest, .. } => {
                walk(first, map, f);
                for (_, e) in rest {
                    walk(e, map, f);
                }
            }
            Expr::In { value, lo, hi, .. } => {
                walk(value, map, f);
                walk(lo, map, f);
                walk(hi, map, f);
            }
            Expr::Index { base, index, .. } => {
                walk(base, map, f);
                walk(index, map, f);
            }
            Expr::Member { base, .. } => walk(base, map, f),
            Expr::Call { callee, args, .. } => {
                // select(cond, ...): a bare Name condition is guard-position.
                if let Expr::Name(fname) = callee.as_ref()
                    && fname.text == "select"
                    && args.len() == 3
                {
                    if let Expr::Name(c) = &args[0].value {
                        f(resolve(&c.text, map), true);
                    } else {
                        walk(&args[0].value, map, f);
                    }
                    walk(&args[1].value, map, f);
                    walk(&args[2].value, map, f);
                    return;
                }
                walk(callee, map, f);
                for a in args {
                    walk(&a.value, map, f);
                }
            }
            Expr::TypedCtor { args, .. } => {
                for a in args {
                    walk(&a.value, map, f);
                }
            }
            Expr::Comprehension {
                acc,
                binders,
                where_clauses,
                body,
                ..
            } => {
                let mut inner = map.clone();
                for b in binders {
                    match &b.seq {
                        Seq::Expr(Expr::Name(arr)) => {
                            inner.insert(b.name.text.clone(), arr.text.clone());
                        }
                        Seq::Expr(other) => walk(other, map, f),
                        Seq::Range { lo, hi, .. } => {
                            walk(lo, map, f);
                            walk(hi, map, f);
                        }
                    }
                }
                if let Some(a) = acc {
                    walk(&a.init, &inner, f);
                }
                // A bare-Name guard is IF-position only when it is the sole
                // clause: multi-clause guards conjoin via BOOLAND, which
                // accepts non-canonical truthy values, so an airlock is
                // required.
                if let [Expr::Name(n)] = where_clauses.as_slice() {
                    f(resolve(&n.text, &inner), true);
                } else {
                    for w in where_clauses {
                        walk(w, &inner, f);
                    }
                }
                walk(body, &inner, f);
            }
            Expr::ArrayLit { elems, .. } => {
                for e in elems {
                    walk(e, map, f);
                }
            }
            Expr::Int { .. } | Expr::Str { .. } | Expr::Duration { .. } | Expr::Bool { .. } => {}
        }
    }
    walk(e, &BTreeMap::new(), f)
}

// --- dead-witness elimination (shared by lowering AND the certifier) ---
//
// A witness array element is DEAD when its value provably cannot affect whether
// the spend succeeds, so it is dropped from BOTH the script and the witness.
// The criterion MUST be identical in the lowering and in the certifier's
// predicate builder (`crate::verify::decide`), so the certifier proves the REDUCED
// script against the REDUCED predicate -- otherwise the predicate would
// reference an atom the script no longer has and certification would break.
//
// The one sound, decidable case (cat_bounty's zero-weight pixels): a `sum`
// comprehension `sum(px in arr, ... where px => body)` whose per-element body
// const-folds to 0 (the sum identity), over an array used ONLY as a guard
// (`if_position_only_bools`), so `px`'s only effect -- gating a `+0` and a
// MINIMALIF bool-check -- vanishes with it. Conservative: anything that does
// not fit returns "not dead".

/// Bool-array params used only as comprehension/`select` guards (never read for
/// their value), so dropping a provably-irrelevant element removes no live use.
fn guard_only_arrays(s: &Spend, sig: &crate::analysis::sema::SpendSig) -> BTreeSet<String> {
    let mut arrays: BTreeSet<String> = sig
        .params
        .iter()
        .filter(|p| matches!(&p.ty, Ty::Array(e, _) if **e == Ty::Bool))
        .map(|p| p.name.clone())
        .collect();
    for stmt in &s.body {
        let exprs: Vec<&Expr> = match stmt {
            Stmt::Let { value, .. } => vec![value],
            Stmt::Require(req) => req.items.iter().collect(),
        };
        for e in exprs {
            walk_guard_uses(e, &mut |name, in_guard| {
                if !in_guard {
                    arrays.remove(name);
                }
            });
        }
    }
    arrays
}

fn array_len_of(ty: &Ty, env: &Env) -> Option<usize> {
    let Ty::Array(_, len) = ty else { return None };
    match len {
        Len::Lit(n) => Some(*n as usize),
        Len::Named(name) => match env.get(name) {
            Some(ConstValue::Int(v)) if *v >= 0 => Some(*v as usize),
            _ => None,
        },
    }
}

/// The const element values of a binder's sequence, or None if it is a witness
/// (non-const) sequence or does not fully evaluate.
fn const_binder_elements(b: &Binder, env: &Env) -> Option<Vec<ConstValue>> {
    match &b.seq {
        Seq::Range {
            lo, hi, inclusive, ..
        } => {
            let ConstValue::Int(l) = eval_in_env(lo, env).0? else {
                return None;
            };
            let ConstValue::Int(h) = eval_in_env(hi, env).0? else {
                return None;
            };
            let end = if *inclusive { h + 1 } else { h };
            Some((l..end).map(ConstValue::Int).collect())
        }
        Seq::Expr(e) => match eval_in_env(e, env).0 {
            Some(ConstValue::Array(items)) => Some(items),
            _ => None,
        },
    }
}

/// The witness array-element slots that are provably dead for this spend.
pub(crate) fn dead_witness_slots(
    s: &Spend,
    sig: &crate::analysis::sema::SpendSig,
    env: &Env,
) -> BTreeSet<String> {
    let guard_only = guard_only_arrays(s, sig);
    let mut dead = BTreeSet::new();
    if guard_only.is_empty() {
        return dead;
    }
    for stmt in &s.body {
        let exprs: Vec<&Expr> = match stmt {
            Stmt::Let { value, .. } => vec![value],
            Stmt::Require(req) => req.items.iter().collect(),
        };
        for e in exprs {
            collect_dead_elements(e, sig, env, &guard_only, &mut dead);
        }
    }
    dead
}

fn collect_dead_elements(
    e: &Expr,
    sig: &crate::analysis::sema::SpendSig,
    env: &Env,
    guard_only: &BTreeSet<String>,
    dead: &mut BTreeSet<String>,
) {
    if let Expr::Comprehension {
        callee,
        binders,
        where_clauses,
        body,
        ..
    } = e
    {
        sum_dead_elements(
            callee,
            binders,
            where_clauses,
            body,
            sig,
            env,
            guard_only,
            dead,
        );
    }
    // Recurse into every sub-expression so a nested comprehension (e.g. inside
    // `bias + sum(...)`) is reached.
    match e {
        Expr::Unary { operand, .. } => collect_dead_elements(operand, sig, env, guard_only, dead),
        Expr::Binary { lhs, rhs, .. } => {
            collect_dead_elements(lhs, sig, env, guard_only, dead);
            collect_dead_elements(rhs, sig, env, guard_only, dead);
        }
        Expr::Compare { first, rest, .. } => {
            collect_dead_elements(first, sig, env, guard_only, dead);
            for (_, x) in rest {
                collect_dead_elements(x, sig, env, guard_only, dead);
            }
        }
        Expr::In { value, lo, hi, .. } => {
            collect_dead_elements(value, sig, env, guard_only, dead);
            collect_dead_elements(lo, sig, env, guard_only, dead);
            collect_dead_elements(hi, sig, env, guard_only, dead);
        }
        Expr::Index { base, index, .. } => {
            collect_dead_elements(base, sig, env, guard_only, dead);
            collect_dead_elements(index, sig, env, guard_only, dead);
        }
        Expr::Member { base, .. } => collect_dead_elements(base, sig, env, guard_only, dead),
        Expr::Call { callee, args, .. } => {
            collect_dead_elements(callee, sig, env, guard_only, dead);
            for a in args {
                collect_dead_elements(&a.value, sig, env, guard_only, dead);
            }
        }
        Expr::TypedCtor { args, .. } => {
            for a in args {
                collect_dead_elements(&a.value, sig, env, guard_only, dead);
            }
        }
        Expr::ArrayLit { elems, .. } => {
            for x in elems {
                collect_dead_elements(x, sig, env, guard_only, dead);
            }
        }
        Expr::Comprehension { body, .. } => {
            collect_dead_elements(body, sig, env, guard_only, dead);
        }
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn sum_dead_elements(
    callee: &Ident,
    binders: &[Binder],
    where_clauses: &[Expr],
    body: &Expr,
    sig: &crate::analysis::sema::SpendSig,
    env: &Env,
    guard_only: &BTreeSet<String>,
    dead: &mut BTreeSet<String>,
) {
    if callee.text != "sum" {
        return;
    }
    // A single bare-binder guard: `where px`.
    let [Expr::Name(g)] = where_clauses else {
        return;
    };
    let Some(gb) = binders.iter().find(|b| b.name.text == g.text) else {
        return;
    };
    // The guard binder must iterate a guard-only witness array.
    let Seq::Expr(Expr::Name(arr)) = &gb.seq else {
        return;
    };
    if !guard_only.contains(&arr.text) {
        return;
    }
    let Some(p) = sig.params.iter().find(|p| p.name == arr.text) else {
        return;
    };
    let Some(n) = array_len_of(&p.ty, env) else {
        return;
    };
    // Materialize every OTHER binder as const element lists (the body references
    // them); bail if any is non-const or the lengths do not zip.
    let mut const_binders: Vec<(String, Vec<ConstValue>)> = Vec::new();
    for b in binders {
        if b.name.text == g.text {
            continue;
        }
        match const_binder_elements(b, env) {
            Some(vals) if vals.len() == n => const_binders.push((b.name.text.clone(), vals)),
            _ => return,
        }
    }
    // Element i is dead when the body folds to the sum identity (0) for it.
    for i in 0..n {
        let mut env_i = env.clone();
        env_i.extend(
            const_binders
                .iter()
                .map(|(name, vals)| (name.clone(), vals[i].clone())),
        );
        if let Some(ConstValue::Int(0)) = eval_in_env(body, &env_i).0 {
            dead.insert(format!("{}[{i}]", arr.text));
        }
    }
}
