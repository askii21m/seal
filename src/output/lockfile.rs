//! `seal.lock`, a reproducible build artifact for contracts.
//!
//! Emitted on build, byte-for-byte reproducible: compiler version and
//! target, source/args hashes, the bound extern values, the full realized
//! layout (leaf scripts, tree, internal key plus NUMS disclosure, control
//! blocks, witness templates), the address, and a per-leaf cost snapshot.
//! `seal --verify <lock>` recompiles and requires an exact match: this is
//! the funded-address recovery guarantee, where a lockfile-bearing repo can
//! always re-derive its address or learn precisely why not.
//!
//! The writer is deterministic by construction: field order is fixed in
//! code, collections iterate sorted structures, and every value renders
//! canonically (ints decimal, bytes 0x-hex, locktimes as resolved
//! integers). There is no serde; the format is this module.

use crate::analysis::consteval::{ConstValue, Env, LockAbs, LockRel};
use crate::analysis::sema::ContractInfo;
use crate::codegen::lower::LoweredLeaf;
use crate::crypto::sha256::sha256;
use crate::output::taproot::{ContractOutput, LeafTree};

/// Render the lockfile. Inputs are everything compilation consumed plus
/// everything it produced; the result is the canonical artifact.
pub fn render(
    source: &str,
    args_src: &str,
    info: &ContractInfo,
    env: &Env,
    leaves: &[LoweredLeaf],
    out: &ContractOutput,
    address: &str,
) -> String {
    let mut w = Writer::new();
    w.open();
    w.field_int("version", 1);
    w.field_str("compiler", &format!("seal {}", env!("CARGO_PKG_VERSION")));
    w.field_str("target", "bitcoin-mainnet-tapscript-v1");
    w.field_str("source_sha256", &hex(&sha256(source.as_bytes())));
    w.field_str("args_sha256", &hex(&sha256(args_src.as_bytes())));

    // The bound extern values (the compilation inputs; consts are derived
    // and covered by the source hash). Declaration order.
    w.key("externs");
    w.open();
    for (name, _) in &info.externs {
        if let Some(v) = env.get(name) {
            w.field_str(name, &render_value(v));
        }
    }
    w.close();

    let asm = &out.assembled;
    w.field_str("address", address);
    w.field_str("output_key", &hex(&asm.output_key));
    w.field_int("parity", i128::from(asm.parity));
    w.field_str("internal_key", &hex(&asm.internal_key));
    if let Some(r) = &out.nums_r {
        w.field_str("nums_r", &hex(r));
    }
    if let Some(root) = &asm.merkle_root {
        w.field_str("merkle_root", &hex(root));
    }
    w.field_str("tweak", &hex(&asm.tweak));
    if let Some(tree) = &out.tree {
        w.field_str("tree", &render_tree(tree, leaves));
    }

    w.key("leaves");
    w.open_array();
    for (leaf, a) in leaves.iter().zip(&asm.leaves) {
        w.array_item();
        w.open();
        w.field_str("name", &leaf.name);
        w.field_str("script", &hex(&leaf.script));
        w.field_str("leaf_hash", &hex(&a.hash));
        w.field_int("depth", a.path.len() as i128);
        w.field_str("control_block", &hex(&a.control_block));
        w.key("witness");
        w.open_array();
        for slot in &leaf.witness_order {
            w.array_item();
            w.string(slot);
        }
        w.close_array();
        // Cost snapshot (script-side; the full funding report lands with the
        // satisfier, which knows worst-case element sizes).
        w.field_int("script_bytes", leaf.script.len() as i128);
        w.field_int("control_bytes", a.control_block.len() as i128);
        w.field_int("witness_elements", leaf.witness_order.len() as i128);
        w.close();
    }
    w.close_array();
    w.close();
    w.finish()
}

/// `branch(a, branch(b, c))` over leaf names: the human-readable shape.
/// The commitment-relevant facts (leaf, depth) are in the leaves array.
fn render_tree(tree: &LeafTree, leaves: &[LoweredLeaf]) -> String {
    match tree {
        LeafTree::Leaf(i) => leaves
            .get(*i)
            .map(|l| l.name.clone())
            .unwrap_or_else(|| format!("<leaf {i}>")),
        LeafTree::Branch(l, r) => {
            format!(
                "branch({}, {})",
                render_tree(l, leaves),
                render_tree(r, leaves)
            )
        }
    }
}

/// Canonical value rendering: deterministic, human-auditable.
fn render_value(v: &ConstValue) -> String {
    match v {
        ConstValue::Int(i) => i.to_string(),
        ConstValue::Bool(b) => b.to_string(),
        ConstValue::Bytes(b) => format!("0x{}", hex(b)),
        ConstValue::LockAbs(LockAbs::Height(h)) => format!("height {h}"),
        ConstValue::LockAbs(LockAbs::Time(t)) => format!("time {t}"),
        ConstValue::LockRel(LockRel::Blocks(b)) => format!("blocks {b}"),
        ConstValue::LockRel(LockRel::Units(u)) => format!("units {u}"),
        ConstValue::Array(items) => {
            let inner: Vec<String> = items.iter().map(render_value).collect();
            format!("[{}]", inner.join(", "))
        }
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// A tiny deterministic JSON writer: fixed field order, 2-space indent,
/// full string escaping (values are ASCII hex/names today, but escaping
/// correctly is total).
struct Writer {
    out: String,
    indent: usize,
    /// Whether the current container already has an entry (comma logic).
    has_entry: Vec<bool>,
}

impl Writer {
    fn new() -> Writer {
        Writer {
            out: String::new(),
            indent: 0,
            has_entry: Vec::new(),
        }
    }

    fn newline_indent(&mut self) {
        self.out.push('\n');
        for _ in 0..self.indent {
            self.out.push_str("  ");
        }
    }

    fn pre_entry(&mut self) {
        if let Some(has) = self.has_entry.last_mut() {
            if *has {
                self.out.push(',');
            }
            *has = true;
        }
        self.newline_indent();
    }

    fn open(&mut self) {
        self.out.push('{');
        self.indent += 1;
        self.has_entry.push(false);
    }

    fn close(&mut self) {
        self.indent = self.indent.saturating_sub(1);
        self.has_entry.pop();
        self.newline_indent();
        self.out.push('}');
    }

    fn open_array(&mut self) {
        self.out.push('[');
        self.indent += 1;
        self.has_entry.push(false);
    }

    fn close_array(&mut self) {
        self.indent = self.indent.saturating_sub(1);
        self.has_entry.pop();
        self.newline_indent();
        self.out.push(']');
    }

    fn array_item(&mut self) {
        self.pre_entry();
    }

    fn key(&mut self, k: &str) {
        self.pre_entry();
        self.string(k);
        self.out.push_str(": ");
    }

    fn field_str(&mut self, k: &str, v: &str) {
        self.key(k);
        self.string(v);
    }

    fn field_int(&mut self, k: &str, v: i128) {
        self.key(k);
        self.out.push_str(&v.to_string());
    }

    fn string(&mut self, s: &str) {
        self.out.push('"');
        for c in s.chars() {
            match c {
                '"' => self.out.push_str("\\\""),
                '\\' => self.out.push_str("\\\\"),
                '\n' => self.out.push_str("\\n"),
                '\r' => self.out.push_str("\\r"),
                '\t' => self.out.push_str("\\t"),
                c if (c as u32) < 0x20 => {
                    self.out.push_str(&format!("\\u{:04x}", c as u32));
                }
                c => self.out.push(c),
            }
        }
        self.out.push('"');
    }

    fn finish(mut self) -> String {
        self.out.push('\n');
        self.out
    }
}
