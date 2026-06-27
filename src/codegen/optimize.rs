//! Stack-scheduling optimizer, run after lowering.
//!
//! Lowering stays naive and is the differential oracle: it copies every
//! value with PICK, drops the originals at the end, and pushes a literal 1.
//! This pass rewrites a leaf to consume each value (witness slot or
//! intermediate) at its last use (ROLL instead of PICK plus a trailing DROP)
//! and to let the final check's own boolean be the leaf result. The witness
//! stays exactly the declared parameters; nothing hidden is added.
//!
//! Branch (IF) leaves are handled when each branch body is stack-balanced and
//! contains no pick or roll (so consumption stays in the linear flow); the
//! block is then a balanced unit that pops its condition. An `Else`, a pick
//! inside a branch, or any unmodeled op makes the pass fall back to the naive
//! leaf.
//!
//! It is conservative by construction: it transforms only leaves whose shape
//! it can prove safe, re-simulates the output independently, re-checks it
//! against the poison gate, keeps the rewrite only when it shrinks, and falls
//! back to the naive leaf otherwise.

use std::collections::{BTreeMap, BTreeSet};

use crate::analysis::consteval::MACHINE_MAX;
use crate::codegen::lower::{CseSubject, LoweredLeaf};
use crate::codegen::script::{self, Op};

/// Optimize a leaf, or return it unchanged when no safe rewrite applies.
pub fn optimize(leaf: &LoweredLeaf) -> LoweredLeaf {
    // First drop dead require checks (the interval engine proved them always
    // true), then share any subject two adjacent items recompute, then
    // stack-schedule the result. Each step verifies its own output and falls
    // back, so the worst case is the naive leaf.
    let base = eliminate_dead(leaf).unwrap_or_else(|| leaf.clone());
    let shared = coalesce_cse(&base).unwrap_or(base);
    let scheduled = try_optimize(&shared).unwrap_or(shared);
    // Finally, two arithmetic peepholes: fuse a CSE'd two-sided range into a
    // single WITHIN, and fold a constant addend across a comparison.
    let fused = fuse_within(&scheduled).unwrap_or(scheduled);
    let folded = fold_const_add_cmp(&fused).unwrap_or(fused);
    // Finally, hoist a single trailing-eligible timelock to the tail: CSV/CLTV's
    // own (always-positive) operand becomes the leaf result, so the up-front
    // OP_DROP vanishes (matching rust-miniscript's trailing-timelock form).
    hoist_timelock_to_tail(&folded).unwrap_or(folded)
}

/// Fold a constant addend across a comparison: `<c> ADD <k> CMP` -> `<k-c> CMP`,
/// since `(x + c) op k == x op (k - c)`. The `x + c` was overflow-checked at
/// compile time (the leaf would not exist otherwise), and we fold only when
/// `k-c` stays in the 4-byte CScriptNum domain. The certifier's arena performs
/// the same fold on the predicate, so Engine B stays consistent (e.g.
/// cat_bounty's `sum + 5 > 40` -> `sum > 35`).
fn fold_const_add_cmp(leaf: &LoweredLeaf) -> Option<LoweredLeaf> {
    let ops = &leaf.ops;
    let mut out: Vec<Op> = Vec::with_capacity(ops.len());
    let mut i = 0;
    let mut changed = false;
    while i < ops.len() {
        if i + 3 < ops.len()
            && let Op::PushNum(c) = ops[i]
            && ops[i + 1] == Op::Add
            && let Op::PushNum(k) = ops[i + 2]
            && matches!(
                ops[i + 3],
                Op::GreaterThan
                    | Op::LessThan
                    | Op::GreaterThanOrEqual
                    | Op::LessThanOrEqual
                    | Op::NumEqual
                    | Op::NumNotEqual
            )
            && i128::from(k - c).abs() <= MACHINE_MAX
        {
            out.push(Op::PushNum(k - c));
            out.push(ops[i + 3].clone());
            i += 4;
            changed = true;
        } else {
            out.push(ops[i].clone());
            i += 1;
        }
    }
    if !changed {
        return None;
    }
    let script = script::serialize(&out);
    script::verify_script(&script).ok()?;
    if script.len() >= leaf.script.len() {
        return None;
    }
    Some(LoweredLeaf {
        name: leaf.name.clone(),
        ops: out,
        script,
        witness_order: leaf.witness_order.clone(),
        removable: Vec::new(),
        cse_subjects: Vec::new(),
    })
}

/// Fuse a DUP'd two-sided range check into one WITHIN:
///   `DUP <a> GREATERTHANOREQUAL VERIFY <b> LESSTHANOREQUAL VERIFY`
///     ->  `<a> <b+1> WITHIN VERIFY`     (both mean `a <= x <= b`)
/// The subject is then consumed once, so the DUP and one compare/verify vanish.
/// This is the fusion coalesce_cse leaves on the table (it shares the tally but
/// keeps both comparisons). Sound: `OP_WITHIN(x, a, b+1)` is `a <= x < b+1`.
fn fuse_within(leaf: &LoweredLeaf) -> Option<LoweredLeaf> {
    let ops = &leaf.ops;
    let mut out: Vec<Op> = Vec::with_capacity(ops.len());
    let mut i = 0;
    let mut changed = false;
    while i < ops.len() {
        if i + 6 < ops.len()
            && ops[i] == Op::Dup
            && let Op::PushNum(a) = ops[i + 1]
            && ops[i + 2] == Op::GreaterThanOrEqual
            && ops[i + 3] == Op::Verify
            && let Op::PushNum(b) = ops[i + 4]
            && ops[i + 5] == Op::LessThanOrEqual
            && ops[i + 6] == Op::Verify
            && i128::from(b) < MACHINE_MAX
        // b+1 must stay in the 4-byte CScriptNum domain
        {
            out.push(Op::PushNum(a));
            out.push(Op::PushNum(b + 1));
            out.push(Op::Within);
            out.push(Op::Verify);
            i += 7;
            changed = true;
        } else {
            out.push(ops[i].clone());
            i += 1;
        }
    }
    if !changed {
        return None;
    }
    let script = script::serialize(&out);
    script::verify_script(&script).ok()?;
    if script.len() >= leaf.script.len() {
        return None;
    }
    Some(LoweredLeaf {
        name: leaf.name.clone(),
        ops: out,
        script,
        witness_order: leaf.witness_order.clone(),
        removable: Vec::new(),
        cse_subjects: Vec::new(),
    })
}

/// Drop the op-ranges of always-true `require` items (recorded by lowering).
/// Returns None when there is nothing to drop or the reduced script is not
/// provably clean, so the caller keeps the naive leaf.
fn eliminate_dead(leaf: &LoweredLeaf) -> Option<LoweredLeaf> {
    if leaf.removable.is_empty() {
        return None;
    }
    let mut ranges = leaf.removable.clone();
    ranges.sort_by_key(|r| r.0);
    let mut reduced: Vec<Op> = Vec::with_capacity(leaf.ops.len());
    let mut i = 0;
    let mut ri = 0;
    while i < leaf.ops.len() {
        if ri < ranges.len() && i == ranges[ri].0 {
            i = ranges[ri].1; // skip the dead range
            ri += 1;
        } else {
            reduced.push(leaf.ops[i].clone());
            i += 1;
        }
    }
    // Each dropped range is a net-zero check, so the remainder must still end
    // with exactly one result and pass the poison gate. If not, do not drop.
    let script = script::serialize(&reduced);
    script::verify_script(&script).ok()?;
    match simulate(&reduced, leaf.witness_order.len()) {
        Some((_, 1)) => {}
        _ => return None,
    }
    Some(LoweredLeaf {
        name: leaf.name.clone(),
        ops: reduced,
        script,
        witness_order: leaf.witness_order.clone(),
        removable: Vec::new(),
        // CSE candidates whose ops survive the deletions, shifted to their
        // new positions; any candidate inside a dropped range is gone with it.
        cse_subjects: remap_subjects(&leaf.cse_subjects, &ranges),
    })
}

/// Shift recorded CSE subjects past deleted op-ranges. A subject overlapping
/// any deleted range was part of a dropped item and is discarded; the rest
/// move left by the total length deleted before them. `deleted` is sorted by
/// start and its ranges are disjoint (each is a whole dead require item).
fn remap_subjects(subjects: &[CseSubject], deleted: &[(usize, usize)]) -> Vec<CseSubject> {
    let mut out = Vec::new();
    for s in subjects {
        let (lo, hi) = (s.subject.0, s.item_end);
        // `[lo, hi)` intersects any deleted `[ds, de)`?
        if deleted.iter().any(|&(ds, de)| lo < de && ds < hi) {
            continue;
        }
        let shift: usize = deleted
            .iter()
            .filter(|&&(_, de)| de <= lo)
            .map(|&(ds, de)| de - ds)
            .sum();
        // `shift` is the length deleted entirely before `lo`, so it is <= lo
        // for any survivor; `saturating_sub` keeps remap total even if that
        // ever failed (the coalesce_cse gate then rejects a malformed set).
        out.push(CseSubject {
            subject: (
                s.subject.0.saturating_sub(shift),
                s.subject.1.saturating_sub(shift),
            ),
            item_end: s.item_end.saturating_sub(shift),
        });
    }
    out
}

/// Common-subexpression elimination across adjacent require items.
///
/// Lowering records, per single-comparison item, the op-range that computes
/// the compared value (`subject`) and where the item ends (`item_end`). When
/// two or more such items are back-to-back (`item_end` of one equals the
/// `subject` start of the next) and their subject op-runs are byte-identical,
/// they compute the same value over the same base stack: adjacency means the
/// preceding item returned the stack to base, the layout below is fixed (the
/// naive leaf never moves a slot, only copies it), so identical PICK depths
/// read identical slots and every Seal value is pure.
///
/// Such a run is rewritten to compute the subject once, then test each bound
/// against a copy: `subject` then, per item but the last, `DUP <predicate>`,
/// then the last `<predicate>`. Each predicate consumes one copy; the last
/// consumes the original, so the stack returns to base and ops after the run
/// are untouched.
///
/// A run is only eligible when every predicate (`bound push <cmp> VERIFY`) is
/// free of PICK/ROLL: the kept copy sits one slot above base while the
/// predicates run, so a depth-based read (a witness-dependent bound) would
/// land on the wrong slot. Constant bounds, the common case, push no copy.
///
/// Returns None when nothing applies or the rewrite is not provably clean,
/// so the caller keeps the prior leaf.
fn coalesce_cse(leaf: &LoweredLeaf) -> Option<LoweredLeaf> {
    let subjects = &leaf.cse_subjects;
    if subjects.len() < 2 {
        return None;
    }
    let ops = &leaf.ops;
    // Defensive well-formedness gate. Lowering records subjects ascending,
    // non-overlapping, and in-bounds (subject.0 <= subject.1 <= item_end <=
    // ops.len()), and eliminate_dead's remap preserves that. CSE must never
    // panic on a malformed annotation, so a set that violates the invariant
    // falls back to the prior leaf instead of indexing out of range; every
    // slice and gap-fill below is then in range by construction. No valid
    // lowering produces a violating set.
    let n = ops.len();
    let well_formed = subjects
        .iter()
        .all(|s| s.subject.0 <= s.subject.1 && s.subject.1 <= s.item_end && s.item_end <= n)
        && subjects.windows(2).all(|w| w[0].item_end <= w[1].subject.0);
    if !well_formed {
        return None;
    }
    let subj_ops = |s: &CseSubject| &ops[s.subject.0..s.subject.1];
    let predicate_is_depth_free = |s: &CseSubject| {
        !ops[s.subject.1..s.item_end]
            .iter()
            .any(|o| matches!(o, Op::Pick | Op::Roll))
    };

    // Maximal runs of consecutive subjects that are back-to-back, share a
    // byte-identical subject, and have depth-free predicates.
    let mut runs: Vec<(usize, usize)> = Vec::new(); // inclusive [a, b] into subjects
    let mut i = 0;
    while i < subjects.len() {
        let mut j = i;
        if predicate_is_depth_free(&subjects[i]) {
            while j + 1 < subjects.len()
                && subjects[j].item_end == subjects[j + 1].subject.0
                && subj_ops(&subjects[j + 1]) == subj_ops(&subjects[i])
                && predicate_is_depth_free(&subjects[j + 1])
            {
                j += 1;
            }
        }
        if j > i {
            runs.push((i, j));
        }
        i = j + 1;
    }
    if runs.is_empty() {
        return None;
    }

    // Rebuild: copy the gaps between runs verbatim; replace each run with one
    // shared subject computation plus a per-item predicate (the non-final
    // ones preceded by a DUP that keeps a copy alive).
    let mut out: Vec<Op> = Vec::with_capacity(ops.len());
    let mut pos = 0;
    for &(a, b) in &runs {
        out.extend_from_slice(&ops[pos..subjects[a].subject.0]);
        out.extend_from_slice(&ops[subjects[a].subject.0..subjects[a].subject.1]);
        for m in a..=b {
            if m != b {
                out.push(Op::Dup);
            }
            out.extend_from_slice(&ops[subjects[m].subject.1..subjects[m].item_end]);
        }
        pos = subjects[b].item_end;
    }
    out.extend_from_slice(&ops[pos..]);

    // Independent gates: poison-clean, ends with exactly one result, smaller.
    let script = script::serialize(&out);
    script::verify_script(&script).ok()?;
    match simulate(&out, leaf.witness_order.len()) {
        Some((_, 1)) => {}
        _ => return None,
    }
    if script.len() >= leaf.script.len() {
        return None;
    }
    Some(LoweredLeaf {
        name: leaf.name.clone(),
        ops: out,
        script,
        witness_order: leaf.witness_order.clone(),
        removable: Vec::new(),
        cse_subjects: Vec::new(),
    })
}

fn try_optimize(leaf: &LoweredLeaf) -> Option<LoweredLeaf> {
    let ops = &leaf.ops;
    let n_witness = leaf.witness_order.len();

    // Per-op target cell for each PICK/ROLL, from a naive simulation.
    let (targets, _) = simulate(ops, n_witness)?;

    // The naive tail is <verify> (DROP|DROP2)* PushNum(1): the run drops the
    // witness originals and pushes the true result. Without it there is
    // nothing to consume into, so the leaf is already in its tight form.
    let (verify_idx, cleanup_start) = tail_shape(ops)?;

    // Each cell's last PICK becomes a ROLL (consume in place): witness slots
    // and intermediates alike, so leftover copies need no trailing DROP.
    let mut last_pick: BTreeMap<usize, usize> = BTreeMap::new();
    for (i, op) in ops.iter().enumerate() {
        if matches!(op, Op::Pick)
            && let Some(t) = targets[i]
        {
            last_pick.insert(t, i);
        }
    }
    let to_roll: BTreeSet<usize> = last_pick.values().copied().collect();

    let new_ops = rebuild(
        ops,
        n_witness,
        &targets,
        &to_roll,
        verify_idx,
        cleanup_start,
    )?;

    // Independent re-check: simulate the OUTPUT from scratch (not rebuild's
    // incremental model) and require every PICK/ROLL depth in range and a
    // single result on the stack. This catches any rebuild bookkeeping error
    // regardless of how the rebuild model evolved.
    match simulate(&new_ops, n_witness) {
        Some((_, 1)) => {}
        _ => return None,
    }

    let script = script::serialize(&new_ops);
    script::verify_script(&script).ok()?;

    // Only keep the rewrite if it actually helped.
    if script.len() >= leaf.script.len() {
        return None;
    }
    Some(LoweredLeaf {
        name: leaf.name.clone(),
        ops: new_ops,
        script,
        witness_order: leaf.witness_order.clone(),
        removable: Vec::new(),
        cse_subjects: Vec::new(),
    })
}

/// Net stack effect (pops, pushes) for an op handled generically. PICK and
/// ROLL are handled by the caller. Returns None for ops this pass does not
/// model (control flow, the reordering ops), which forces a naive fallback.
fn effect(op: &Op) -> Option<(usize, usize)> {
    Some(match op {
        Op::Push(_) | Op::PushNum(_) | Op::Size => (0, 1),
        Op::Cltv | Op::Csv => (0, 0),
        Op::Verify | Op::Drop => (1, 0),
        Op::Drop2 => (2, 0),
        Op::Add1
        | Op::Sub1
        | Op::Negate
        | Op::Abs
        | Op::Not
        | Op::ZeroNotEqual
        | Op::Ripemd160
        | Op::Sha1
        | Op::Sha256
        | Op::Hash160
        | Op::Hash256 => (1, 1),
        Op::Equal
        | Op::NumEqual
        | Op::NumNotEqual
        | Op::Add
        | Op::Sub
        | Op::BoolAnd
        | Op::BoolOr
        | Op::LessThan
        | Op::GreaterThan
        | Op::LessThanOrEqual
        | Op::GreaterThanOrEqual
        | Op::Min
        | Op::Max
        | Op::CheckSig => (2, 1),
        Op::EqualVerify | Op::NumEqualVerify | Op::CheckSigVerify => (2, 0),
        Op::Within | Op::CheckSigAdd => (3, 1),
        _ => return None,
    })
}

/// Simulate ops over the initial witness stack, recording the target cell of
/// every PICK/ROLL and returning the final stack depth. Cells are ids:
/// 0..n_witness are the witness slots, higher ids are produced values.
/// Returns None on an out-of-range depth or an unmodeled op.
fn simulate(ops: &[Op], n_witness: usize) -> Option<(Vec<Option<usize>>, usize)> {
    // Cell ids are stable across simulate and rebuild: witness slots are
    // 0..n_witness; a cell produced at op index `i` is `n_witness + i`. This
    // keeps target ids valid even when rebuild turns a copy into a consume.
    let mut model: Vec<usize> = (0..n_witness).collect();
    let mut targets = vec![None; ops.len()];
    // Stack of model depths captured at each open IF, to confirm each branch
    // body is stack-balanced at its ENDIF.
    let mut if_stack: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < ops.len() {
        if let Op::PushNum(d) = ops[i]
            && i + 1 < ops.len()
            && matches!(ops[i + 1], Op::Pick | Op::Roll)
        {
            // A pick or roll inside a branch would consume conditionally; do
            // not optimize such leaves.
            if !if_stack.is_empty() {
                return None;
            }
            if d < 0 || d as usize >= model.len() {
                return None;
            }
            let depth = d as usize;
            let pos = model.len() - 1 - depth;
            targets[i + 1] = Some(model[pos]);
            if matches!(ops[i + 1], Op::Pick) {
                model.push(n_witness + i + 1);
            } else {
                let c = model.remove(pos);
                model.push(c);
            }
            i += 2;
            continue;
        }
        match ops[i] {
            Op::If | Op::NotIf => {
                if model.is_empty() {
                    return None;
                }
                model.pop(); // the condition
                if_stack.push(model.len());
                i += 1;
                continue;
            }
            Op::EndIf => {
                let want = if_stack.pop()?;
                if model.len() != want {
                    return None; // branch body was not stack-balanced
                }
                i += 1;
                continue;
            }
            Op::Else => return None, // if/else not handled in this pass
            Op::Dup => {
                // Duplicate the top cell. Modeled here so a CSE-produced leaf
                // (or a Bool airlock) keeps a consistent depth, but DUP is
                // deliberately absent from `effect`/`rebuild`: such a leaf can
                // be depth-verified yet is never re-scheduled, so the rewrite
                // that introduced the DUP is its final form.
                let top = *model.last()?;
                model.push(top);
                i += 1;
                continue;
            }
            Op::Swap => {
                // Reorders the top two cells (e.g. a comprehension-fold lift
                // rewritten from `1 ROLL`). Modeled so the output re-check
                // stays consistent.
                let n = model.len();
                if n < 2 {
                    return None;
                }
                model.swap(n - 1, n - 2);
                i += 1;
                continue;
            }
            _ => {}
        }
        let (pops, pushes) = effect(&ops[i])?;
        if model.len() < pops {
            return None;
        }
        model.truncate(model.len() - pops);
        for _ in 0..pushes {
            model.push(n_witness + i);
        }
        i += 1;
    }
    if !if_stack.is_empty() {
        return None;
    }
    Some((targets, model.len()))
}

/// Match the naive tail `<verify> (DROP|DROP2)* PushNum(1)`. Returns the
/// verify op index and the index where the removable cleanup begins.
fn tail_shape(ops: &[Op]) -> Option<(usize, usize)> {
    let n = ops.len();
    if n == 0 || ops[n - 1] != Op::PushNum(1) {
        return None;
    }
    let mut j = n - 1;
    while j > 0 && matches!(ops[j - 1], Op::Drop | Op::Drop2) {
        j -= 1;
    }
    if j == 0 {
        return None;
    }
    let v = j - 1;
    if matches!(
        ops[v],
        Op::CheckSigVerify | Op::EqualVerify | Op::NumEqualVerify | Op::Verify
    ) {
        Some((v, v + 1))
    } else {
        None
    }
}

/// The bool-producing counterpart of a verify op, or None for a bare VERIFY
/// (whose input bool is simply left as the result).
fn tail_result(op: &Op) -> Option<Op> {
    match op {
        Op::CheckSigVerify => Some(Op::CheckSig),
        Op::EqualVerify => Some(Op::Equal),
        Op::NumEqualVerify => Some(Op::NumEqual),
        _ => None,
    }
}

fn rebuild(
    ops: &[Op],
    n_witness: usize,
    targets: &[Option<usize>],
    to_roll: &BTreeSet<usize>,
    verify_idx: usize,
    cleanup_start: usize,
) -> Option<Vec<Op>> {
    let mut model: Vec<usize> = (0..n_witness).collect();
    let mut out: Vec<Op> = Vec::new();
    let mut i = 0;
    while i < ops.len() {
        if i >= cleanup_start {
            break;
        }
        if i == verify_idx {
            match tail_result(&ops[i]) {
                Some(bool_op) => {
                    if model.len() < 2 {
                        return None;
                    }
                    out.push(bool_op);
                    model.truncate(model.len() - 2);
                    model.push(n_witness + i);
                }
                None => {
                    // A bare VERIFY: drop it and leave its input bool.
                    if model.is_empty() {
                        return None;
                    }
                }
            }
            i += 1;
            continue;
        }
        if let Op::PushNum(_) = ops[i]
            && i + 1 < ops.len()
            && matches!(ops[i + 1], Op::Pick | Op::Roll)
        {
            let target = targets[i + 1]?;
            let depth = model.iter().rev().position(|&c| c == target)?;
            let roll = matches!(ops[i + 1], Op::Roll) || to_roll.contains(&(i + 1));
            if roll {
                // Consume the value in place. At depth 0 it is already on top,
                // so ROLL is a no-op: emit nothing (the bare-check case, e.g.
                // the sig on top in the vault). At depth 1, moving it to the top
                // is exactly OP_SWAP -- 1 byte vs `PushNum(1) ROLL` (2 bytes) --
                // which is the comprehension-fold lift (the running accumulator
                // sits on top, each element just below it).
                if depth == 1 {
                    out.push(Op::Swap);
                } else if depth != 0 {
                    out.push(Op::PushNum(depth as i64));
                    out.push(Op::Roll);
                }
                let pos = model.len() - 1 - depth;
                let c = model.remove(pos);
                model.push(c);
            } else {
                out.push(Op::PushNum(depth as i64));
                out.push(Op::Pick);
                model.push(n_witness + i + 1);
            }
            i += 2;
            continue;
        }
        match ops[i] {
            Op::If | Op::NotIf => {
                if model.is_empty() {
                    return None;
                }
                out.push(ops[i].clone());
                model.pop(); // the condition
                i += 1;
                continue;
            }
            Op::EndIf => {
                out.push(ops[i].clone());
                i += 1;
                continue;
            }
            Op::Dup => {
                // A CSE-shared subject's duplicate: emit it and model the copy
                // as sharing the top's cell id (as `simulate` does), so the
                // re-scheduled leaf keeps consistent depths. This lets a
                // post-CSE leaf still be scheduled (PICK->ROLL); behavior is
                // re-verified by the output simulate + the certifier (T2).
                let top = *model.last()?;
                out.push(Op::Dup);
                model.push(top);
                i += 1;
                continue;
            }
            Op::Else => return None,
            _ => {}
        }
        let (pops, pushes) = effect(&ops[i])?;
        if model.len() < pops {
            return None;
        }
        out.push(ops[i].clone());
        model.truncate(model.len() - pops);
        for _ in 0..pushes {
            model.push(n_witness + i);
        }
        i += 1;
    }
    // The leaf must end clean: exactly one result on the stack.
    if model.len() == 1 { Some(out) } else { None }
}

/// Hoist a single trailing-eligible timelock to the tail. Lowering emits an
/// `after` as `<t> CSV/CLTV DROP` (verify-only, leaves nothing) ahead of the
/// body, so a timelocked spend ends in its sig/hash result with the timelock
/// dropped up front: `<t> CSV DROP .. <result>`. rust-miniscript instead places
/// one timelock LAST, where CSV/CLTV's own (always-positive) operand IS the leaf
/// result -- no DROP. This peephole performs that move on the optimized leaf:
/// remove one `<t> CSV/CLTV DROP` triple, turn the final result op into its
/// VERIFY form, and append `<t> CSV/CLTV`. Net: -1 byte, and byte-identical to
/// Miniscript for a single timelock. Conservative: flat (branch-free) leaves
/// only, only when a convertible boolean result trails, re-simulated and
/// re-serialized (and never kept unless it shrinks) before returning.
fn hoist_timelock_to_tail(leaf: &LoweredLeaf) -> Option<LoweredLeaf> {
    let ops = &leaf.ops;
    // A timelock inside a branch must not be hoisted past the branch boundary.
    if ops
        .iter()
        .any(|o| matches!(o, Op::If | Op::NotIf | Op::Else | Op::EndIf))
    {
        return None;
    }
    // The last `<t> (CSV|CLTV) DROP` triple. It leaves nothing, so its position
    // is immaterial to the rest of the leaf; a single timelock has exactly one.
    let mut found: Option<(usize, i64, Op)> = None;
    for i in 0..ops.len().saturating_sub(2) {
        if let (Op::PushNum(t), lock @ (Op::Csv | Op::Cltv), Op::Drop) =
            (&ops[i], &ops[i + 1], &ops[i + 2])
        {
            found = Some((i, *t, lock.clone()));
        }
    }
    let (start, t, lock) = found?;
    let last = ops.len() - 1;
    if last <= start + 2 {
        return None; // nothing trails the triple to become the new result
    }
    let verify_form = result_to_verify(&ops[last])?;

    let mut new_ops: Vec<Op> = Vec::with_capacity(ops.len() + 1);
    for (j, op) in ops.iter().enumerate() {
        if (start..=start + 2).contains(&j) {
            continue; // drop the `<t> CSV/CLTV DROP` triple
        }
        if j == last {
            new_ops.extend(verify_form.iter().cloned());
        } else {
            new_ops.push(op.clone());
        }
    }
    new_ops.push(Op::PushNum(t));
    new_ops.push(lock);

    // Independent re-check (mirrors try_optimize): the rewritten leaf must
    // simulate to a single result, serialize, validate, and actually shrink.
    match simulate(&new_ops, leaf.witness_order.len()) {
        Some((_, 1)) => {}
        _ => return None,
    }
    let script = script::serialize(&new_ops);
    script::verify_script(&script).ok()?;
    if script.len() >= leaf.script.len() {
        return None;
    }
    Some(LoweredLeaf {
        name: leaf.name.clone(),
        ops: new_ops,
        script,
        witness_order: leaf.witness_order.clone(),
        removable: Vec::new(),
        cse_subjects: Vec::new(),
    })
}

/// The VERIFY form of a boolean leaf-result op (the inverse of `tail_result`):
/// the timelock's `<t>` now supplies the leaf result, so the prior result must
/// be asserted instead of left on the stack. Ops with a fused verify counterpart
/// use it (1 byte); the rest get an explicit VERIFY appended. Returns None for
/// anything that is not a boolean result we can safely verify (keeps the leaf).
fn result_to_verify(op: &Op) -> Option<Vec<Op>> {
    Some(match op {
        Op::CheckSig => vec![Op::CheckSigVerify],
        Op::Equal => vec![Op::EqualVerify],
        Op::NumEqual => vec![Op::NumEqualVerify],
        Op::GreaterThan
        | Op::GreaterThanOrEqual
        | Op::LessThan
        | Op::LessThanOrEqual
        | Op::NumNotEqual
        | Op::Within
        | Op::BoolAnd
        | Op::BoolOr => vec![op.clone(), Op::Verify],
        _ => return None,
    })
}
