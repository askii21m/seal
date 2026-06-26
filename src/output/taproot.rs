//! Taproot output assembly (BIP341): leaf hashes to Merkle tree to tweak to
//! output key plus per-leaf control blocks.
//!
//! Ground truth: the official BIP341 wallet test vectors, vendored at
//! tests/vectors/bip341_wallet_vectors.json. Every intermediate this
//! module produces (leaf hashes, root, tweak, output key, scriptPubKey,
//! address, control blocks) is asserted against them in tests/taproot.rs.
//!
//! # The NUMS key path
//!
//! `keypath: None` means "no key-path spend exists". BIP341's
//! recommendation: use H (the standard nothing-up-my-sleeve point) plus a
//! re-randomizing tweak so the output doesn't fingerprint the compiler:
//! `internal = H + r*G`, with `r = int(hashSeal/NUMS(merkle_root))`.
//! r is deterministic from the leaf set (the address is always
//! re-derivable from source plus externs) and disclosed in the descriptor,
//! so anyone can verify key-path unspendability.

use std::collections::BTreeMap;

use crate::crypto::secp::{N, Point, U256, generator};
use crate::crypto::sha256::tagged_hash;

/// The BIP341 NUMS point H (x-only): `lift_x` of the SHA-256 of the
/// standard uncompressed-G encoding; nothing up anyone's sleeve.
pub const NUMS_H: [u8; 32] = [
    0x50, 0x92, 0x9b, 0x74, 0xc1, 0xa0, 0x49, 0x54, 0xb7, 0x8b, 0x4b, 0x60, 0x35, 0xe9, 0x7a, 0x5e,
    0x07, 0x8a, 0x5a, 0x0f, 0x28, 0xec, 0x96, 0xd5, 0x47, 0xbf, 0xee, 0x9a, 0xce, 0x80, 0x3a, 0xc0,
];

/// One tapscript leaf: serialized script plus leaf version (0xc0 for
/// everything the compiler emits; the parameter exists so the BIP341
/// vectors' non-default versions exercise the same code).
#[derive(Debug, Clone)]
pub struct LeafSpec {
    pub script: Vec<u8>,
    pub version: u8,
}

/// A leaf-index tree shape. Branch hashes sort children, so the shape
/// determines only DEPTHS, never the commitment's identity beyond the
/// (leaf, depth) multiset.
#[derive(Debug, Clone)]
pub enum LeafTree {
    Leaf(usize),
    Branch(Box<LeafTree>, Box<LeafTree>),
}

/// The deterministic balanced default: split the leaf range in half,
/// left side gets the extra. Any deterministic shape is sound, since
/// sorting makes the tree unordered.
pub fn balanced_tree(n: usize) -> Option<LeafTree> {
    fn build(lo: usize, hi: usize) -> LeafTree {
        if hi - lo == 1 {
            return LeafTree::Leaf(lo);
        }
        let mid = lo + (hi - lo).div_ceil(2);
        LeafTree::Branch(Box::new(build(lo, mid)), Box::new(build(mid, hi)))
    }
    (n > 0).then(|| build(0, n))
}

/// The default (no `@weight`) micro-weight = 1.0.
pub const DEFAULT_WEIGHT: u64 = 1_000_000;

/// A planner request for one leaf: its index, an optional
/// `@depth` pin (a hard cost ceiling), and a `@weight` micro-weight
/// (relative usage; only ordering matters to the planner).
#[derive(Debug, Clone, Copy)]
pub struct LeafReq {
    pub index: usize,
    pub depth: Option<u32>,
    pub weight: u64,
}

/// Plan the tapleaf tree from per-spend decorators:
/// `@depth` pins are hard constraints, `@weight` optimizes the rest. The
/// result is deterministic. Errors when the pins can't form a binary
/// tree (Kraft sum of 2^-d != 1).
///
/// This is the deterministic, pin-honoring, always-valid baseline: equal
/// weights give a balanced tree, matching the prior default.
pub fn plan_tree(reqs: &[LeafReq]) -> Result<LeafTree, String> {
    let n = reqs.len();
    if n == 0 {
        return Err("no spends to place in a tree".into());
    }
    if n == 1 {
        if let Some(d) = reqs[0].depth
            && d != 0
        {
            return Err(format!(
                "a lone spend is the entire tree: it sits at depth 0, but `@depth({d})` was requested"
            ));
        }
        return Ok(LeafTree::Leaf(reqs[0].index));
    }
    let depths = assign_depths(reqs)?;
    build_from_depths(depths)
}

/// Optimal tapleaf depths by Huffman coding: minimize the weighted path length
/// sum(weight * depth) (= the expected control-block cost). Equal weights give a
/// balanced tree; heavier spends sit strictly shallower. No `@depth` pins here.
///
/// Determinism (consensus-critical): ties are broken by a FIFO sequence number,
/// so equal weights merge in a fixed order and the depth assignment, hence the
/// tree and the address, is a pure function of the inputs. `n >= 2` (the lone-leaf
/// case is handled in `plan_tree`). O(n^2), and `n` is the spend count.
fn huffman_depths(reqs: &[LeafReq]) -> Result<Vec<(usize, u32)>, String> {
    struct Node {
        weight: u128,
        seq: usize,
        leaves: Vec<usize>,
    }
    let mut forest: Vec<Node> = reqs
        .iter()
        .enumerate()
        .map(|(seq, r)| Node {
            weight: u128::from(r.weight),
            seq,
            leaves: vec![r.index],
        })
        .collect();
    let mut depth: std::collections::HashMap<usize, u32> =
        reqs.iter().map(|r| (r.index, 0u32)).collect();
    let mut next_seq = forest.len();

    while forest.len() > 1 {
        // Two lowest-weight nodes, ties by insertion order (FIFO -> balanced).
        forest.sort_by(|a, b| a.weight.cmp(&b.weight).then(a.seq.cmp(&b.seq)));
        let a = forest.remove(0);
        let b = forest.remove(0);
        for &i in a.leaves.iter().chain(b.leaves.iter()) {
            if let Some(d) = depth.get_mut(&i) {
                *d += 1;
                if *d as usize > MAX_TREE_DEPTH {
                    return Err(format!(
                        "placing {} spends would require depth > {MAX_TREE_DEPTH} \
                         (BIP341 control-block limit)",
                        reqs.len()
                    ));
                }
            }
        }
        let mut leaves = a.leaves;
        leaves.extend(b.leaves);
        forest.push(Node {
            weight: a.weight + b.weight,
            seq: next_seq,
            leaves,
        });
        next_seq += 1;
    }

    Ok(reqs.iter().map(|r| (r.index, depth[&r.index])).collect())
}

/// Assign every leaf a depth such that Kraft sum of 2^-d = 1 by construction.
///
/// With no `@depth` pins this is the pure weighted-optimal (Huffman) problem, so
/// equal weights yield a balanced tree and heavier spends sit shallower. With
/// pins, the pinned leaves are placed first (a Kraft-valid frontier of open
/// slots) and the rest fill the frontier, splitting the SHALLOWEST open slot so
/// an equal-weight fill stays balanced (splitting the deepest produced a
/// degenerate staircase). Pin+weight together is valid + deterministic but only
/// near-optimal; the unpinned-only path above is exactly optimal.
fn assign_depths(reqs: &[LeafReq]) -> Result<Vec<(usize, u32)>, String> {
    if reqs.iter().all(|r| r.depth.is_none()) {
        return huffman_depths(reqs);
    }

    let mut slots: Vec<u32> = vec![0];
    let mut out: Vec<(usize, u32)> = Vec::new();

    // 1. Pinned leaves first, shallowest pin first (deterministic).
    let mut pinned: Vec<&LeafReq> = reqs.iter().filter(|r| r.depth.is_some()).collect();
    pinned.sort_by_key(|r| (r.depth.unwrap_or(0), r.index));
    for r in &pinned {
        let target = r.depth.unwrap_or(0);
        slots.sort_unstable();
        if slots.is_empty() {
            return Err(format!(
                "`@depth({target})` cannot be honored: the pinned depths already fill the tree \
                 (Kraft sum of 2^-d would exceed 1)"
            ));
        }
        let s = slots.remove(0); // shallowest open slot
        if s > target {
            return Err(format!(
                "`@depth({target})` cannot be honored: the pinned depths already fill the tree \
                 above depth {target} (Kraft sum of 2^-d would exceed 1)"
            ));
        }
        let mut d = s;
        while d < target {
            slots.push(d + 1); // the sibling created drilling down
            d += 1;
        }
        out.push((r.index, target));
    }

    // 2. Unpinned leaves, heaviest first into the shallowest holes.
    let mut unpinned: Vec<&LeafReq> = reqs.iter().filter(|r| r.depth.is_none()).collect();
    unpinned.sort_by(|a, b| b.weight.cmp(&a.weight).then(a.index.cmp(&b.index)));
    let u = unpinned.len();
    if u == 0 {
        if !slots.is_empty() {
            return Err(format!(
                "the pinned depths leave {} unfilled tree position(s): every position must be a \
                 spend (Kraft sum of 2^-d < 1)",
                slots.len()
            ));
        }
        return Ok(out);
    }
    if u < slots.len() {
        return Err(format!(
            "the pinned depths leave {} open positions but only {u} unpinned spend(s) remain to \
             fill them",
            slots.len()
        ));
    }
    // Split the SHALLOWEST open slot until there is one per unpinned leaf, so an
    // equal-weight fill is balanced (heaviest still lands in the shallowest slot
    // via the weight-ordered match below).
    while slots.len() < u {
        slots.sort_unstable();
        let shallow = slots.remove(0);
        if shallow as usize >= MAX_TREE_DEPTH {
            return Err(format!(
                "placing {u} spends would require depth > {MAX_TREE_DEPTH} (BIP341 control-block limit)"
            ));
        }
        slots.push(shallow + 1);
        slots.push(shallow + 1);
    }
    slots.sort_unstable(); // ascending; shallowest first
    for (r, &slot) in unpinned.iter().zip(&slots) {
        out.push((r.index, slot));
    }
    Ok(out)
}

/// Build the canonical tree from a Kraft-valid depth assignment: sort by
/// (depth, index), assign canonical prefix-free codewords, insert each
/// leaf at its codeword path. Deterministic; pairing is irrelevant to the
/// commitment (sorted branches), so any canonical pairing is sound.
fn build_from_depths(mut leaves: Vec<(usize, u32)>) -> Result<LeafTree, String> {
    validate_kraft(leaves.iter().map(|x| x.1))?;
    leaves.sort_by_key(|&(idx, d)| (d, idx));

    enum Partial {
        Empty,
        Leaf(usize),
        Branch(Box<Partial>, Box<Partial>),
    }
    fn insert(node: &mut Partial, idx: usize, code: u128, depth: u32) -> Result<(), String> {
        if depth == 0 {
            return match node {
                Partial::Empty => {
                    *node = Partial::Leaf(idx);
                    Ok(())
                }
                _ => Err("internal: codeword collision (depths not prefix-free)".into()),
            };
        }
        if matches!(node, Partial::Empty) {
            *node = Partial::Branch(Box::new(Partial::Empty), Box::new(Partial::Empty));
        }
        let Partial::Branch(l, r) = node else {
            return Err("internal: codeword path runs through a leaf".into());
        };
        let bit = code >> 127;
        let next = code << 1;
        if bit == 0 {
            insert(l, idx, next, depth - 1)
        } else {
            insert(r, idx, next, depth - 1)
        }
    }
    fn finalize(p: &Partial) -> Result<LeafTree, String> {
        match p {
            Partial::Empty => Err("internal: unfilled tree position".into()),
            Partial::Leaf(i) => Ok(LeafTree::Leaf(*i)),
            Partial::Branch(l, r) => Ok(LeafTree::Branch(
                Box::new(finalize(l)?),
                Box::new(finalize(r)?),
            )),
        }
    }

    let mut root = Partial::Empty;
    let mut code: u128 = 0;
    for &(idx, d) in &leaves {
        insert(&mut root, idx, code, d)?;
        code = code.wrapping_add(1u128 << (128 - d)); // d >= 1 (validate_kraft)
    }
    finalize(&root)
}

/// Kraft equality check by pairing reduction (no big-number arithmetic):
/// a full binary tree's leaf depths satisfy sum of 2^-d = 1 iff repeatedly
/// pairing the deepest leaves reduces to a single depth-0 root.
fn validate_kraft(depths: impl Iterator<Item = u32>) -> Result<(), String> {
    let mut count: BTreeMap<u32, u64> = BTreeMap::new();
    for d in depths {
        *count.entry(d).or_insert(0) += 1;
    }
    while let Some((&d, &c)) = count.iter().next_back() {
        if d == 0 {
            return if c == 1 && count.len() == 1 {
                Ok(())
            } else {
                Err("the leaf depths cannot form a binary tree (Kraft sum of 2^-d != 1)".into())
            };
        }
        if !c.is_multiple_of(2) {
            return Err(format!(
                "the leaf depths cannot form a binary tree (Kraft sum of 2^-d != 1): an odd number of \
                 leaves sit at depth {d}"
            ));
        }
        count.remove(&d);
        *count.entry(d - 1).or_insert(0) += c / 2;
    }
    Err("no leaves to place".into())
}

/// `hashTapLeaf(version || compact_size(script) || script)`.
pub fn leaf_hash(script: &[u8], version: u8) -> [u8; 32] {
    let cs = compact_size(script.len() as u64);
    tagged_hash("TapLeaf", &[&[version], &cs, script])
}

/// `hashTapBranch(min(a,b) || max(a,b))`.
pub fn branch_hash(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    if a <= b {
        tagged_hash("TapBranch", &[a, b])
    } else {
        tagged_hash("TapBranch", &[b, a])
    }
}

/// Bitcoin's variable-length integer.
fn compact_size(n: u64) -> Vec<u8> {
    match n {
        0..=0xfc => vec![n as u8],
        0xfd..=0xffff => {
            let mut v = vec![0xfd];
            v.extend((n as u16).to_le_bytes());
            v
        }
        0x1_0000..=0xffff_ffff => {
            let mut v = vec![0xfe];
            v.extend((n as u32).to_le_bytes());
            v
        }
        _ => {
            let mut v = vec![0xff];
            v.extend(n.to_le_bytes());
            v
        }
    }
}

/// The assembled output: everything the lockfile, descriptor, and
/// satisfier need.
#[derive(Debug, Clone)]
pub struct Assembled {
    pub internal_key: [u8; 32],
    pub output_key: [u8; 32],
    /// Q's y-parity: the low bit of every control byte.
    pub parity: bool,
    /// None for a key-path-only output (no scripts).
    pub merkle_root: Option<[u8; 32]>,
    /// The TapTweak scalar t (disclosed in the lockfile; spenders verify
    /// `Q = P + t*G`).
    pub tweak: [u8; 32],
    /// Per input leaf, in input order.
    pub leaves: Vec<AssembledLeaf>,
}

#[derive(Debug, Clone)]
pub struct AssembledLeaf {
    pub hash: [u8; 32],
    /// Sibling hashes, leaf-to-root.
    pub path: Vec<[u8; 32]>,
    /// `(0xc0|version|parity) || internal_key || path...`: what the
    /// witness reveals to spend this leaf.
    pub control_block: Vec<u8>,
}

/// A control block carries at most 128 sibling hashes; deeper
/// trees are consensus-invalid. The cap also bounds the recursion below
/// (totality: this is a pub-API-reachable input).
const MAX_TREE_DEPTH: usize = 128;

/// Per-leaf Merkle paths (sibling hashes, leaf-to-root).
type LeafPaths = Vec<Vec<[u8; 32]>>;

/// Merkle root + per-leaf paths for a tree over `leaves`.
/// Errors are internal-grade (index out of range, duplicate leaf use).
fn merkle(leaves: &[LeafSpec], tree: &LeafTree) -> Result<([u8; 32], LeafPaths), String> {
    let mut paths: Vec<Option<Vec<[u8; 32]>>> = vec![None; leaves.len()];
    fn walk(
        t: &LeafTree,
        leaves: &[LeafSpec],
        paths: &mut Vec<Option<Vec<[u8; 32]>>>,
        depth: usize,
    ) -> Result<([u8; 32], Vec<usize>), String> {
        if depth > MAX_TREE_DEPTH {
            return Err(format!(
                "tree depth exceeds {MAX_TREE_DEPTH} (BIP341 control-block limit)"
            ));
        }
        match t {
            LeafTree::Leaf(i) => {
                let spec = leaves
                    .get(*i)
                    .ok_or_else(|| format!("leaf index {i} out of range"))?;
                let slot = paths
                    .get_mut(*i)
                    .ok_or_else(|| format!("leaf index {i} out of range"))?;
                if slot.is_some() {
                    return Err(format!("leaf index {i} appears twice in the tree"));
                }
                *slot = Some(Vec::new());
                Ok((leaf_hash(&spec.script, spec.version), vec![*i]))
            }
            LeafTree::Branch(l, r) => {
                let (lh, li) = walk(l, leaves, paths, depth + 1)?;
                let (rh, ri) = walk(r, leaves, paths, depth + 1)?;
                for i in &li {
                    if let Some(Some(p)) = paths.get_mut(*i) {
                        p.push(rh);
                    }
                }
                for i in &ri {
                    if let Some(Some(p)) = paths.get_mut(*i) {
                        p.push(lh);
                    }
                }
                let mut all = li;
                all.extend(ri);
                Ok((branch_hash(&lh, &rh), all))
            }
        }
    }
    let (root, covered) = walk(tree, leaves, &mut paths, 0)?;
    if covered.len() != leaves.len() {
        return Err(format!(
            "the tree covers {} leaves but {} were lowered",
            covered.len(),
            leaves.len()
        ));
    }
    let paths = paths
        .into_iter()
        .map(|p| p.ok_or_else(|| "a leaf is missing from the tree".to_string()))
        .collect::<Result<Vec<_>, _>>()?;
    Ok((root, paths))
}

/// The Merkle root alone, needed BEFORE key selection when the key path
/// is NUMS (the re-randomizer commits to the leaf set).
pub fn merkle_root_of(leaves: &[LeafSpec], tree: &LeafTree) -> Result<[u8; 32], String> {
    merkle(leaves, tree).map(|(root, _)| root)
}

/// The NUMS internal key for `keypath: None`: `H + r*G` with
/// `r = int(hashSeal/NUMS(merkle_root)) mod n`. Returns
/// (x-only key, r); r is disclosed for re-derivability.
pub fn nums_internal_key(merkle_root: &[u8; 32]) -> Result<([u8; 32], [u8; 32]), String> {
    let r_bytes = tagged_hash("Seal/NUMS", &[merkle_root]);
    let mut r = U256::from_be_bytes(&r_bytes);
    if r.ge(N) {
        // about 2^-128; reduce rather than fail (still deterministic).
        let (reduced, _) = sub_n(r);
        r = reduced;
    }
    let h = Point::lift_x(&NUMS_H).ok_or("NUMS H must lift (curve constant)")?;
    let p = h + (generator() * r);
    let x = p
        .x_bytes()
        .ok_or("NUMS internal key is the point at infinity")?;
    Ok((x, r.to_be_bytes()))
}

fn sub_n(v: U256) -> (U256, bool) {
    // U256 lacks public sbb; reimplement the borrow chain locally.
    let mut r = [0u64; 4];
    let mut borrow = 0i128;
    for (i, limb) in r.iter_mut().enumerate() {
        let d = v.0[i] as i128 - N.0[i] as i128 - borrow;
        *limb = d as u64;
        borrow = i128::from(d < 0);
    }
    (U256(r), borrow != 0)
}

/// Assemble the output: tweak the internal key with the tree commitment
/// and derive every leaf's control block.
pub fn assemble(
    internal_x: &[u8; 32],
    leaves: &[LeafSpec],
    tree: Option<&LeafTree>,
) -> Result<Assembled, String> {
    let internal = Point::lift_x(internal_x)
        .ok_or("internal key is not on the curve (not a valid x-only public key)")?;

    let (merkle_root, paths) = match (leaves.is_empty(), tree) {
        (true, None) => (None, Vec::new()),
        (false, Some(t)) => {
            let (root, paths) = merkle(leaves, t)?;
            (Some(root), paths)
        }
        (false, None) => return Err("leaves without a tree shape".into()),
        (true, Some(_)) => return Err("a tree shape without leaves".into()),
    };

    // t = hashTapTweak(P || root); root absent entirely (not zeroed)
    // for key-path-only outputs.
    let t_bytes = match &merkle_root {
        Some(root) => tagged_hash("TapTweak", &[internal_x, root]),
        None => tagged_hash("TapTweak", &[internal_x]),
    };
    let t = U256::from_be_bytes(&t_bytes);
    if t.ge(N) {
        // BIP341 declares this invalid (probability about 2^-128).
        return Err("tap tweak exceeds the group order (astronomically unlikely)".into());
    }
    let q = internal + (generator() * t);
    let output_key = q.x_bytes().ok_or("tweaked key is the point at infinity")?;
    let parity = !q.has_even_y();

    let assembled_leaves = leaves
        .iter()
        .zip(&paths)
        .map(|(spec, path)| {
            let hash = leaf_hash(&spec.script, spec.version);
            let mut cb = Vec::with_capacity(33 + 32 * path.len());
            cb.push(spec.version | u8::from(parity));
            cb.extend_from_slice(internal_x);
            for sib in path {
                cb.extend_from_slice(sib);
            }
            AssembledLeaf {
                hash,
                path: path.clone(),
                control_block: cb,
            }
        })
        .collect();

    Ok(Assembled {
        internal_key: *internal_x,
        output_key,
        parity,
        merkle_root,
        tweak: t_bytes,
        leaves: assembled_leaves,
    })
}

/// Everything `--address`, the descriptor, and the lockfile need from a
/// compiled contract: the assembled output plus the NUMS disclosure.
#[derive(Debug, Clone)]
pub struct ContractOutput {
    pub assembled: Assembled,
    /// Some(r) when the key path is NUMS (`keypath: None`): the
    /// re-randomizer, disclosed so anyone can verify unspendability.
    pub nums_r: Option<[u8; 32]>,
    /// The realized tree over leaf indices (None means key-path-only output).
    pub tree: Option<LeafTree>,
}

/// Assemble the taproot output from a contract's `keypath` declaration
/// and its lowered leaves, planning the tree from each spend's
/// `@depth`/`@weight` decorators.
pub fn assemble_contract(
    contract: &crate::syntax::ast::Contract,
    env: &crate::analysis::consteval::Env,
    leaves: &[crate::codegen::lower::LoweredLeaf],
) -> Result<ContractOutput, Vec<crate::diagnostics::Diagnostic>> {
    use crate::diagnostics::Diagnostic;
    use crate::syntax::ast::{Item, Keypath};

    let mut diags = Vec::new();
    let Some(keypath) = contract.items.iter().find_map(|i| match i {
        Item::Keypath(kp) => Some(kp),
        _ => None,
    }) else {
        diags.push(Diagnostic::error(
            "addr/internal",
            "no keypath declaration",
            contract.span,
        ));
        return Err(diags);
    };

    // Every spend is its own 0xc0 leaf (v1), declaration order.
    let specs: Vec<LeafSpec> = leaves
        .iter()
        .map(|l| LeafSpec {
            script: l.script.clone(),
            version: 0xc0,
        })
        .collect();

    // Plan the tree from per-spend decorators (`@depth`/`@weight`).
    let tree: Option<LeafTree> = if leaves.is_empty() {
        None
    } else {
        let reqs: Vec<LeafReq> = leaves
            .iter()
            .enumerate()
            .map(|(i, leaf)| {
                let spend = contract.items.iter().find_map(|it| match it {
                    Item::Spend(s) if s.name.text == leaf.name => Some(s),
                    _ => None,
                });
                let (depth, weight) = spend
                    .map(|s| (s.depth, s.weight.unwrap_or(DEFAULT_WEIGHT)))
                    .unwrap_or((None, DEFAULT_WEIGHT));
                LeafReq {
                    index: i,
                    depth,
                    weight,
                }
            })
            .collect();
        match plan_tree(&reqs) {
            Ok(t) => Some(t),
            Err(e) => {
                diags.push(Diagnostic::error("addr/layout", e, contract.span));
                return Err(diags);
            }
        }
    };

    // Key path: an explicit const key, or NUMS over the leaf-set
    // commitment (H + r*G, r disclosed).
    let (internal, nums_r): ([u8; 32], Option<[u8; 32]>) = match keypath {
        Keypath::Key(expr) => match crate::analysis::consteval::eval_in_env(expr, env) {
            (Some(crate::analysis::consteval::ConstValue::Bytes(b)), _) if b.len() == 32 => {
                let mut k = [0u8; 32];
                k.copy_from_slice(&b);
                (k, None)
            }
            (_, mut eval_diags) => {
                if eval_diags.is_empty() {
                    diags.push(Diagnostic::error(
                        "addr/keypath",
                        "keypath did not evaluate to a 32-byte public key",
                        expr.span(),
                    ));
                } else {
                    diags.append(&mut eval_diags);
                }
                return Err(diags);
            }
        },
        Keypath::None(span) => {
            let Some(t) = &tree else {
                diags.push(Diagnostic::error(
                    "addr/burn",
                    "`keypath None` with no spends would burn funds: \
                     unspendable output",
                    *span,
                ));
                return Err(diags);
            };
            match merkle_root_of(&specs, t).and_then(|root| nums_internal_key(&root)) {
                Ok((k, r)) => (k, Some(r)),
                Err(e) => {
                    diags.push(Diagnostic::error("addr/internal", e, *span));
                    return Err(diags);
                }
            }
        }
    };

    match assemble(&internal, &specs, tree.as_ref()) {
        Ok(assembled) => Ok(ContractOutput {
            assembled,
            nums_r,
            tree,
        }),
        Err(e) => {
            diags.push(Diagnostic::error("addr/internal", e, contract.span));
            Err(diags)
        }
    }
}
