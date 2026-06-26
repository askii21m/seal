//! BIP341 + BIP350 against the OFFICIAL wallet test vectors (vendored at
//! tests/vectors/bip341_wallet_vectors.json, retrieved from bitcoin/bips).
//!
//! Every artifact the assembler produces is asserted for all seven cases:
//! per-leaf TapLeaf hashes (including the non-default 0xfa leaf version),
//! the Merkle root, the TapTweak scalar, the tweaked output key, the
//! scriptPubKey, the bech32m address, and every script-path control
//! block. A single wrong bit in SHA-256, the tagged-hash forms, the field
//! arithmetic, the point math, the tree, or the address encoding fails
//! this suite.

use seal::json::{self, Json};
use seal::output::bech32m::{encode_p2tr, verify_checksum};
use seal::output::taproot::{LeafReq, LeafSpec, LeafTree, assemble, balanced_tree, plan_tree};

fn hexv(s: &str) -> Vec<u8> {
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).expect("hex"))
        .collect()
}

fn hex32(s: &str) -> [u8; 32] {
    let v = hexv(s);
    let mut b = [0u8; 32];
    b.copy_from_slice(&v);
    b
}

fn to_hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn get<'a>(obj: &'a Json, key: &str) -> &'a Json {
    let Json::Object(fields) = obj else {
        panic!("expected object")
    };
    &fields.iter().find(|(k, _)| k == key).expect(key).1
}

fn s(j: &Json) -> &str {
    let Json::Str(s) = j else {
        panic!("expected string")
    };
    s
}

/// The vendored file is official and byte-exact. The strict JSON subset
/// rejects `null`, so the test rewrites it to the string "NULL" before
/// parsing.
fn load_vectors() -> Json {
    let raw = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/vectors/bip341_wallet_vectors.json"),
    )
    .expect("vendored vectors");
    json::parse(&raw.replace("null", "\"NULL\"")).expect("vectors parse")
}

fn is_null(j: &Json) -> bool {
    matches!(j, Json::Str(s) if s == "NULL")
}

/// Collect (id-ordered leaves, index tree) from the vectors' tree JSON:
/// a leaf is `{id, script, leafVersion}`, a branch a 2-element array.
fn parse_tree(j: &Json, leaves: &mut Vec<(usize, LeafSpec)>) -> LeafTree {
    match j {
        Json::Array(children) => {
            assert_eq!(children.len(), 2, "branches are binary");
            let l = parse_tree(&children[0], leaves);
            let r = parse_tree(&children[1], leaves);
            LeafTree::Branch(Box::new(l), Box::new(r))
        }
        Json::Object(_) => {
            let Json::Int(id) = get(j, "id") else {
                panic!("leaf id")
            };
            let Json::Int(ver) = get(j, "leafVersion") else {
                panic!("leaf version")
            };
            let spec = LeafSpec {
                script: hexv(s(get(j, "script"))),
                version: *ver as u8,
            };
            leaves.push((*id as usize, spec));
            LeafTree::Leaf(*id as usize)
        }
        _ => panic!("unexpected tree node"),
    }
}

#[test]
fn bip341_official_wallet_vectors() {
    let v = load_vectors();
    let Json::Array(cases) = get(&v, "scriptPubKey") else {
        panic!("cases")
    };
    assert_eq!(cases.len(), 7);

    for (i, case) in cases.iter().enumerate() {
        let given = get(case, "given");
        let inter = get(case, "intermediary");
        let expected = get(case, "expected");
        let internal = hex32(s(get(given, "internalPubkey")));

        let tree_json = get(given, "scriptTree");
        let (leaves, tree) = if is_null(tree_json) {
            (Vec::new(), None)
        } else {
            let mut found = Vec::new();
            let t = parse_tree(tree_json, &mut found);
            // The vectors order leafHashes and control blocks by leaf id.
            found.sort_by_key(|(id, _)| *id);
            assert!(
                found.iter().enumerate().all(|(i, (id, _))| i == *id),
                "case {i}: leaf ids are dense"
            );
            (
                found.into_iter().map(|(_, spec)| spec).collect::<Vec<_>>(),
                Some(t),
            )
        };

        let asm = assemble(&internal, &leaves, tree.as_ref()).expect("assemble");

        // Intermediaries.
        match get(inter, "merkleRoot") {
            j if is_null(j) => assert_eq!(asm.merkle_root, None, "case {i}"),
            j => assert_eq!(to_hex(&asm.merkle_root.expect("root")), s(j), "case {i}"),
        }
        assert_eq!(to_hex(&asm.tweak), s(get(inter, "tweak")), "case {i} tweak");
        assert_eq!(
            to_hex(&asm.output_key),
            s(get(inter, "tweakedPubkey")),
            "case {i} output key"
        );
        if !leaves.is_empty() {
            let Json::Array(want_hashes) = get(inter, "leafHashes") else {
                panic!()
            };
            assert_eq!(want_hashes.len(), asm.leaves.len());
            for (j, want) in want_hashes.iter().enumerate() {
                assert_eq!(to_hex(&asm.leaves[j].hash), s(want), "case {i} leaf {j}");
            }
        }

        // Expected outputs.
        let spk = format!("5120{}", to_hex(&asm.output_key));
        assert_eq!(
            spk,
            s(get(expected, "scriptPubKey")),
            "case {i} scriptPubKey"
        );
        let addr = encode_p2tr("bc", &asm.output_key);
        assert_eq!(addr, s(get(expected, "bip350Address")), "case {i} address");
        assert!(verify_checksum(&addr), "case {i} checksum");
        if !leaves.is_empty() {
            let Json::Array(cbs) = get(expected, "scriptPathControlBlocks") else {
                panic!()
            };
            for (j, want) in cbs.iter().enumerate() {
                assert_eq!(
                    to_hex(&asm.leaves[j].control_block),
                    s(want),
                    "case {i} control block {j}"
                );
            }
        }
    }
}

#[test]
fn bech32m_checksum_is_bit_sensitive() {
    let addr = encode_p2tr("bc", &[0x77u8; 32]);
    assert!(addr.starts_with("bc1p"));
    assert!(verify_checksum(&addr));
    // Flipping any payload character breaks the checksum.
    let bytes = addr.as_bytes();
    for pos in 4..addr.len() {
        let mut mutated = bytes.to_vec();
        mutated[pos] = if mutated[pos] == b'q' { b'p' } else { b'q' };
        let m = String::from_utf8(mutated).unwrap();
        if m != addr {
            assert!(
                !verify_checksum(&m),
                "mutation at {pos} must break the checksum"
            );
        }
    }
}

// --- the tree planner ---

/// Map each leaf index to its depth in a planned tree.
fn leaf_depths(tree: &LeafTree) -> std::collections::BTreeMap<usize, u32> {
    fn walk(t: &LeafTree, d: u32, out: &mut std::collections::BTreeMap<usize, u32>) {
        match t {
            LeafTree::Leaf(i) => {
                out.insert(*i, d);
            }
            LeafTree::Branch(l, r) => {
                walk(l, d + 1, out);
                walk(r, d + 1, out);
            }
        }
    }
    let mut out = std::collections::BTreeMap::new();
    walk(tree, 0, &mut out);
    out
}

fn req(index: usize, depth: Option<u32>, weight: u64) -> LeafReq {
    LeafReq {
        index,
        depth,
        weight,
    }
}

#[test]
fn planner_default_is_balanced_and_kraft_valid() {
    // No decorators (weight 1): equal-weight balanced trees, every leaf
    // placed, sum of 2^-d == 1.
    assert!(matches!(
        plan_tree(&[req(0, None, 1)]).unwrap(),
        LeafTree::Leaf(0)
    ));
    let two = plan_tree(&[req(0, None, 1), req(1, None, 1)]).unwrap();
    assert_eq!(leaf_depths(&two), [(0, 1), (1, 1)].into_iter().collect());
    for n in 1..=33usize {
        let reqs: Vec<_> = (0..n).map(|i| req(i, None, 1)).collect();
        let t = plan_tree(&reqs).unwrap();
        let depths = leaf_depths(&t);
        assert_eq!(depths.len(), n, "every leaf placed (n={n})");
        // Kraft: sum of 2^-d == 1 (scaled by 2^max).
        let max = *depths.values().max().unwrap();
        let sum: u64 = depths.values().map(|&d| 1u64 << (max - d)).sum();
        assert_eq!(sum, 1u64 << max, "Kraft must equal 1 (n={n})");
        // ACTUALLY balanced: the depth profile must match the balanced tree's
        // (equal weights => no leaf is deeper than necessary). This is the
        // assertion the old test lacked, which let a 1/2/3/3 staircase pass.
        let mut got: Vec<u32> = depths.values().copied().collect();
        let want_map = leaf_depths(&balanced_tree(n).unwrap());
        let mut want: Vec<u32> = want_map.values().copied().collect();
        got.sort_unstable();
        want.sort_unstable();
        assert_eq!(
            got, want,
            "equal weights must give the balanced depth profile (n={n})"
        );
    }
}

#[test]
fn planner_weighted_is_huffman_optimal() {
    // The planner minimizes the expected control-block cost = sum(weight * depth).
    // Compare its weighted path length to the optimum from an independent
    // heap-Huffman (whose total merge cost equals the optimal weighted path
    // length). Any optimal tree has this cost regardless of tie-breaking.
    fn optimal_cost(weights: &[u64]) -> u128 {
        use std::cmp::Reverse;
        use std::collections::BinaryHeap;
        if weights.len() < 2 {
            return 0;
        }
        let mut h: BinaryHeap<Reverse<u128>> =
            weights.iter().map(|&w| Reverse(u128::from(w))).collect();
        let mut cost = 0u128;
        while h.len() > 1 {
            let a = h.pop().unwrap().0;
            let b = h.pop().unwrap().0;
            cost += a + b;
            h.push(Reverse(a + b));
        }
        cost
    }
    let cases: &[&[u64]] = &[
        &[1, 1],
        &[1, 1, 1],
        &[1, 1, 1, 1],
        &[1, 2, 3, 4],
        &[8, 3, 1, 1],
        &[5, 5, 5, 5, 5],
        &[1, 1, 1, 1, 1, 9],
        &[100, 1, 1, 1],
        &[7, 6, 5, 4, 3, 2, 1],
    ];
    for ws in cases {
        let reqs: Vec<LeafReq> = ws
            .iter()
            .enumerate()
            .map(|(i, &w)| req(i, None, w))
            .collect();
        let depths = leaf_depths(&plan_tree(&reqs).unwrap());
        let got: u128 = ws
            .iter()
            .enumerate()
            .map(|(i, &w)| u128::from(w) * u128::from(depths[&i]))
            .sum();
        assert_eq!(
            got,
            optimal_cost(ws),
            "weighted path length must be optimal for {ws:?}"
        );
    }
}

#[test]
fn planner_honors_depth_pin_and_weight_order() {
    // Example: solve@depth(1), two unpinned default-weight, so solve sits
    // at depth 1 and the others both at depth 2 (the pin determines it).
    let t = plan_tree(&[req(0, Some(1), 1), req(1, None, 1), req(2, None, 1)]).unwrap();
    assert_eq!(
        leaf_depths(&t),
        [(0, 1), (1, 2), (2, 2)].into_iter().collect()
    );

    // Pure weights, no pins: the heaviest leaf is shallowest.
    let t = plan_tree(&[req(0, None, 1), req(1, None, 1), req(2, None, 8)]).unwrap();
    let d = leaf_depths(&t);
    assert!(
        d[&2] < d[&0] && d[&2] < d[&1],
        "heaviest is shallowest: {d:?}"
    );
}

#[test]
fn planner_rejects_impossible_pins() {
    // Three leaves all pinned at depth 1: Kraft 3 * 1/2 = 1.5 > 1.
    let e = plan_tree(&[req(0, Some(1), 1), req(1, Some(1), 1), req(2, Some(1), 1)]).unwrap_err();
    assert!(e.contains("depth") || e.contains("Kraft"), "{e}");
    // A lone spend cannot sit below depth 0.
    let e = plan_tree(&[req(0, Some(2), 1)]).unwrap_err();
    assert!(e.contains("depth 0"), "{e}");
    // Two leaves both pinned at depth 1 is exactly Kraft = 1: fine.
    assert!(plan_tree(&[req(0, Some(1), 1), req(1, Some(1), 1)]).is_ok());
}

#[test]
fn planner_is_deterministic() {
    let reqs = [
        req(0, Some(1), 1),
        req(1, None, 3),
        req(2, None, 1),
        req(3, None, 2),
    ];
    let a = leaf_depths(&plan_tree(&reqs).unwrap());
    let b = leaf_depths(&plan_tree(&reqs).unwrap());
    assert_eq!(a, b);
}

#[test]
fn balanced_tree_shapes() {
    // n = 1: a bare leaf. n = 2: one branch. n = 3: left-heavy split.
    assert!(matches!(balanced_tree(1), Some(LeafTree::Leaf(0))));
    assert!(balanced_tree(0).is_none());
    let Some(LeafTree::Branch(l, r)) = balanced_tree(3) else {
        panic!("branch")
    };
    assert!(matches!(*l, LeafTree::Branch(_, _)), "left gets the extra");
    assert!(matches!(*r, LeafTree::Leaf(2)));
}

#[test]
fn tree_deeper_than_128_is_rejected() {
    // BIP341 caps control blocks at 128 sibling hashes; the cap also
    // bounds the assembler's recursion.
    let leaves: Vec<LeafSpec> = (0..130)
        .map(|i| LeafSpec {
            script: vec![0x51, i as u8],
            version: 0xc0,
        })
        .collect();
    // A maximally unbalanced comb: leaf 0 at depth 129.
    let mut tree = LeafTree::Leaf(129);
    for i in (0..129).rev() {
        tree = LeafTree::Branch(Box::new(LeafTree::Leaf(i)), Box::new(tree));
    }
    let err = assemble(
        &hex32("d6889cb081036e0faefa3a35157ad71086b123b2b144b649798b494c300a961d"),
        &leaves,
        Some(&tree),
    )
    .expect_err("must reject");
    assert!(err.contains("128"), "{err}");
    // The balanced default at the same leaf count is fine (depth ~8).
    let t = balanced_tree(130).expect("tree");
    assert!(
        assemble(
            &hex32("d6889cb081036e0faefa3a35157ad71086b123b2b144b649798b494c300a961d"),
            &leaves,
            Some(&t)
        )
        .is_ok()
    );
}

#[test]
fn nums_internal_key_is_deterministic_and_disclosed() {
    let root = [0x42u8; 32];
    let (k1, r1) = seal::output::taproot::nums_internal_key(&root).expect("nums");
    let (k2, r2) = seal::output::taproot::nums_internal_key(&root).expect("nums");
    assert_eq!((k1, r1), (k2, r2), "deterministic");
    let other = seal::output::taproot::nums_internal_key(&[0x43u8; 32]).expect("nums");
    assert_ne!(k1, other.0, "re-randomized per leaf set");
    // The disclosed r re-derives the key: H + r*G.
    use seal::crypto::secp::{Point, U256, generator};
    let h = Point::lift_x(&seal::output::taproot::NUMS_H).unwrap();
    let p = h + (generator() * U256::from_be_bytes(&r1));
    assert_eq!(p.x_bytes().unwrap(), k1);
}
