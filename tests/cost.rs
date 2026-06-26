//! Worst-case satisfaction cost (`src/cost.rs`). The EXACT pieces (leaf script
//! size, control-block size) are cross-checked against the corpus's
//! hand-computed cost tables; the witness is the worst-case (largest valid)
//! satisfaction, validated by its element composition.

use seal::analysis::consteval::{Env, bind_args, instantiate};
use seal::analysis::intervals;
use seal::analysis::paths;
use seal::analysis::sema;
use seal::analysis::sema::ContractInfo;
use seal::codegen::lower::{LoweredLeaf, lower};
use seal::codegen::optimize::optimize;
use seal::cost::{self, SpendCost};
use seal::diagnostics::Severity;
use seal::json;
use seal::output::taproot;
use seal::syntax::ast::Contract;
use seal::syntax::parser;

fn costs(name: &str) -> Vec<SpendCost> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
    let src = std::fs::read_to_string(dir.join(format!("{name}.sl"))).unwrap();
    let args = std::fs::read_to_string(dir.join(format!("{name}.args.json"))).unwrap();
    let (contract, pd) = parser::parse_source(&src);
    assert!(pd.is_empty(), "parse: {pd:#?}");
    let c: Contract = contract.unwrap();
    let (sd, info): (_, ContractInfo) = sema::analyze(&c);
    assert!(sd.is_empty(), "sema: {sd:#?}");
    let mut env: Env = bind_args(&info, &json::parse(&args).unwrap()).unwrap();
    assert!(
        instantiate(&c, &mut env)
            .iter()
            .all(|d| d.severity != Severity::Error)
    );
    let (b, report) = intervals::analyze(&c, &env);
    assert!(b.is_empty());
    let (pd2, _) = paths::analyze(&c, &info, &env);
    assert!(pd2.iter().all(|d| d.severity != Severity::Error));
    let (ld, naive) = lower(&c, &info, &env, &report);
    assert!(ld.iter().all(|d| d.severity != Severity::Error));
    let leaves: Vec<LoweredLeaf> = naive.iter().map(optimize).collect();
    let out = taproot::assemble_contract(&c, &env, &leaves).expect("assemble");
    cost::analyze(&info, &env, &leaves, &out.assembled)
}

fn by_name(cs: &[SpendCost], name: &str) -> SpendCost {
    cs.iter().find(|c| c.name == name).expect("spend").clone()
}

#[test]
fn multisig_2of3_matches_hand_computed_script_size() {
    // Corpus comment: "Instantiated 2-of-3: script 104, control 34, witness ...".
    let c = by_name(&costs("multisig"), "fallback");
    assert_eq!(c.script_bytes, 104, "script = 34*N + 2 = 104 for N=3");
    assert_eq!(
        c.control_bytes, 33,
        "single leaf: 0xc0|parity + 32-byte internal key"
    );
    // worst-case witness: all 3 signatures present (65 B each: 64-byte BIP340
    // sig + a sighash-type byte, the largest valid element).
    assert_eq!(c.witness_elem_bytes, 3 * 65);
}

#[test]
fn mirage_optimized_script_size() {
    // Reverse-consumption witness layout drops the stray ROLL: 42 -> 40.
    let c = by_name(&costs("mirage"), "claim");
    assert_eq!(c.script_bytes, 40);
    assert_eq!(c.witness_elem_bytes, 5 + 65, "Int(5) + Signature(65)");
}

#[test]
fn cat_bounty_witness_composition() {
    let c = by_name(&costs("cat_bounty"), "claim");
    // 37 zero-weight pixels are dead and dropped from the witness: 747 survive.
    assert_eq!(
        c.witness_elem_bytes,
        747 + 65,
        "747 surviving Bool pixels + 1 Signature"
    );
    // SWAP-fold lift + dead-pixel elimination (was >6000 with deep ROLLs).
    assert!(c.script_bytes < 4200, "747-pixel SWAP-fold IfAdd chain");
}

#[test]
fn htlc_two_leaf_control_block_and_weight_formula() {
    let cs = costs("htlc");
    let swap = by_name(&cs, "swap");
    // Two-leaf tree: control block = 33 + one 32-byte sibling = 65.
    assert_eq!(swap.control_bytes, 65);
    assert_eq!(
        swap.witness_elem_bytes,
        32 + 65,
        "Bytes<32> preimage + Signature(65)"
    );

    // Weight is the serialized witness: item count + each item's compactsize
    // prefix + bytes. swap items: preimage(32), sig(65), script, control(65).
    let cs_pref = |l: usize| if l < 0xfd { 1 } else { 3 };
    let items = [32usize, 65, swap.script_bytes, 65];
    let expect: usize = cs_pref(items.len()) + items.iter().map(|&l| cs_pref(l) + l).sum::<usize>();
    assert_eq!(swap.max_witness_weight, expect as u64);
    assert!((swap.max_vbytes - expect as f64 / 4.0).abs() < 1e-9);

    // Per-input weight adds the input's non-witness base (prevout 36 + empty
    // scriptSig length 1 + nSequence 4 = 41 bytes, at 4 WU/byte = 164 WU).
    assert_eq!(swap.max_input_weight, expect as u64 + 164);
    assert!((swap.max_input_vbytes - (expect + 164) as f64 / 4.0).abs() < 1e-9);
}
