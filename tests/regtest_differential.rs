//! Phase 4, the gold standard: real taproot spends through a live `bitcoind`
//! regtest node. Closes T3 (the taproot commitment -- our control block must be
//! the one Core re-derives or the spend is rejected), T5 (a real BIP340
//! signature over the BIP341 sighash), and T4 (tapscript execution under real
//! consensus), all at once via `testmempoolaccept`. Both BIP341 spend shapes
//! are exercised: script-path leaves (single-sig, quorum's CSE leaf, the four
//! timelock forms, and the htlc/vault corpus trees spent leaf-by-leaf) and a
//! key-path spend (a single signature under the tweaked output key).
//!
//! Funding trick (no wallet, no funding-tx signing): mine the coinbase DIRECTLY
//! to the contract's P2TR address, so the only thing we sign is the script-path
//! spend itself.
//!
//! For each case both Core and our own interpreter judge the SAME witness; our
//! interpreter's signature oracle is "valid iff the bytes equal the real
//! signature", which partitions valid vs tampered exactly as Core's
//! cryptographic check does -- so the two verdicts are directly comparable
//! without re-deriving sighashes inside the interpreter.
//!
//! Heavyweight: SKIPS (passing) unless `bitcoind`/`bitcoin-cli` are found
//! (BITCOIN_BUILD/bin). Build per vendor/README.md.

use std::path::PathBuf;
use std::process::{Child, Command, Stdio};

use seal::analysis::consteval::{Env, bind_args, instantiate};
use seal::analysis::intervals;
use seal::analysis::paths;
use seal::analysis::sema;
use seal::analysis::sema::ContractInfo;
use seal::codegen::lower::{LoweredLeaf, lower};
use seal::codegen::optimize::optimize;
use seal::crypto::sha256::{sha256, tagged_hash};
use seal::diagnostics::Severity;
use seal::json;
use seal::output::bech32m;
use seal::output::taproot;
use seal::syntax::parser;
use seal::verify::interp::{Context, execute};
use seal::verify::satisfy::{SatValue, build_witness};

fn manifest() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}
fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}
fn unhex(s: &str) -> Vec<u8> {
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).unwrap())
        .collect()
}
fn cs(n: usize) -> Vec<u8> {
    let n = n as u64;
    if n < 0xfd {
        vec![n as u8]
    } else if n <= 0xffff {
        let mut v = vec![0xfd];
        v.extend((n as u16).to_le_bytes());
        v
    } else if n <= 0xffff_ffff {
        let mut v = vec![0xfe];
        v.extend((n as u32).to_le_bytes());
        v
    } else {
        let mut v = vec![0xff];
        v.extend(n.to_le_bytes());
        v
    }
}

#[test]
fn compact_size_covers_all_ranges() {
    assert_eq!(cs(0), vec![0x00]);
    assert_eq!(cs(0xfc), vec![0xfc]);
    assert_eq!(cs(0xfd), vec![0xfd, 0xfd, 0x00]);
    assert_eq!(cs(0xffff), vec![0xfd, 0xff, 0xff]);
    assert_eq!(cs(0x1_0000), vec![0xfe, 0x00, 0x00, 0x01, 0x00]);
    assert_eq!(cs(0xffff_ffff), vec![0xfe, 0xff, 0xff, 0xff, 0xff]);
    assert_eq!(cs(0x1_0000_0000), vec![0xff, 0, 0, 0, 0, 1, 0, 0, 0]);
}

fn bin(name: &str) -> Option<PathBuf> {
    let cand = std::env::var("BITCOIN_BUILD")
        .map(|b| PathBuf::from(b).join("bin").join(name))
        .ok()
        .into_iter()
        .chain([manifest().join("vendor/bitcoin/build/bin").join(name)]);
    cand.into_iter().find(|p| p.exists())
}

// --- regtest node (killed on drop) ---

struct Node {
    datadir: PathBuf,
    cli: PathBuf,
    child: Child,
    rpcport: u16,
}

impl Node {
    fn start() -> Option<Node> {
        let (bitcoind, cli) = (bin("bitcoind")?, bin("bitcoin-cli")?);
        let datadir = std::env::temp_dir().join(format!("basis_regtest_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&datadir);
        std::fs::create_dir_all(&datadir).ok()?;
        let rpcport = 19531;
        let child = Command::new(&bitcoind)
            .arg("-regtest")
            .arg(format!("-datadir={}", datadir.display()))
            .arg(format!("-rpcport={rpcport}"))
            .arg("-port=19532")
            .args(["-server=1", "-listen=0", "-txindex=1"])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .ok()?;
        let node = Node {
            datadir,
            cli,
            child,
            rpcport,
        };
        for _ in 0..100 {
            if node.try_cli(&["getblockchaininfo"]).is_some() {
                return Some(node);
            }
            std::thread::sleep(std::time::Duration::from_millis(200));
        }
        None
    }
    fn try_cli(&self, args: &[&str]) -> Option<String> {
        let out = Command::new(&self.cli)
            .arg("-regtest")
            .arg(format!("-datadir={}", self.datadir.display()))
            .arg(format!("-rpcport={}", self.rpcport))
            .args(args)
            .output()
            .ok()?;
        out.status
            .success()
            .then(|| String::from_utf8_lossy(&out.stdout).trim().to_string())
    }
    fn cli(&self, args: &[&str]) -> String {
        self.try_cli(args)
            .unwrap_or_else(|| panic!("bitcoin-cli {args:?} failed"))
    }
    /// Mine one coinbase to `addr`; return that coinbase's outpoint (internal
    /// txid, vout 0) once it is queryable.
    fn coinbase_to(&self, addr: &str) -> ([u8; 32], u32) {
        let hashes = self.cli(&["generatetoaddress", "1", addr]);
        let block_hash = json_first_hex(&hashes).expect("block hash");
        let block = self.cli(&["getblock", &block_hash]);
        // First quoted 64-hex run after the "tx" key = the coinbase txid
        // (display/big-endian); tolerant of pretty-printing whitespace.
        let rest = &block[block.find("\"tx\"").expect("tx key")..];
        let rb = rest.as_bytes();
        let disp = (0..rb.len())
            .find_map(|i| {
                (rb[i] == b'"' && i + 65 < rb.len() && rb[i + 65] == b'"')
                    .then(|| &rest[i + 1..i + 65])
                    .filter(|c| c.bytes().all(|b| b.is_ascii_hexdigit()))
            })
            .expect("coinbase txid");
        let mut internal = unhex(disp);
        internal.reverse();
        (internal.try_into().unwrap(), 0)
    }
}
impl Drop for Node {
    fn drop(&mut self) {
        let _ = self.try_cli(&["stop"]);
        std::thread::sleep(std::time::Duration::from_millis(400));
        let _ = self.child.kill();
        let _ = self.child.wait();
        let _ = std::fs::remove_dir_all(&self.datadir);
    }
}

/// First 64-hex run inside a JSON array of strings (`["<hash>", ...]`).
fn json_first_hex(s: &str) -> Option<String> {
    let i = s.find('"')? + 1;
    Some(s[i..i + 64].to_string())
}
fn json_str<'a>(s: &'a str, key: &str) -> Option<&'a str> {
    let pat = format!("\"{key}\"");
    let after = s[s.find(&pat)? + pat.len()..].trim_start();
    let after = after.strip_prefix(':')?.trim_start().strip_prefix('"')?;
    let end = after.find('"')?;
    Some(&after[..end])
}
fn json_num(s: &str, key: &str) -> Option<f64> {
    let pat = format!("\"{key}\"");
    let after = s[s.find(&pat)? + pat.len()..]
        .trim_start()
        .strip_prefix(':')?
        .trim_start();
    let end = after
        .find(|c: char| !(c.is_ascii_digit() || c == '.' || c == '-'))
        .unwrap_or(after.len());
    after[..end].parse::<f64>().ok()
}

// --- BIP341 script-path sighash (SIGHASH_DEFAULT, one input) ---

/// `tapleaf = Some(hash)` is a script-path spend (spend_type 2 + tapscript
/// extension); `None` is a key-path spend (spend_type 0, no extension).
#[allow(clippy::too_many_arguments)]
fn taproot_sighash(
    version: u32,
    locktime: u32,
    prevouts: &[([u8; 32], u32)],
    amounts: &[u64],
    spks: &[Vec<u8>],
    sequences: &[u32],
    outputs: &[(u64, Vec<u8>)],
    input_index: u32,
    tapleaf: Option<&[u8; 32]>,
) -> [u8; 32] {
    let mut m: Vec<u8> = vec![0x00 /* epoch */, 0x00 /* SIGHASH_DEFAULT */];
    m.extend(version.to_le_bytes());
    m.extend(locktime.to_le_bytes());
    let mut pre = Vec::new();
    for (t, v) in prevouts {
        pre.extend(t);
        pre.extend(v.to_le_bytes());
    }
    m.extend(sha256(&pre));
    let mut amt = Vec::new();
    for a in amounts {
        amt.extend(a.to_le_bytes());
    }
    m.extend(sha256(&amt));
    let mut sp = Vec::new();
    for s in spks {
        sp.extend(cs(s.len()));
        sp.extend(s);
    }
    m.extend(sha256(&sp));
    let mut seq = Vec::new();
    for s in sequences {
        seq.extend(s.to_le_bytes());
    }
    m.extend(sha256(&seq));
    let mut outs = Vec::new();
    for (a, spk) in outputs {
        outs.extend(a.to_le_bytes());
        outs.extend(cs(spk.len()));
        outs.extend(spk);
    }
    m.extend(sha256(&outs));
    m.push(if tapleaf.is_some() { 0x02 } else { 0x00 }); // spend_type (ext_flag), no annex
    m.extend(input_index.to_le_bytes());
    if let Some(tl) = tapleaf {
        m.extend(tl);
        m.push(0x00); // key_version
        m.extend(0xffff_ffffu32.to_le_bytes()); // codesep_pos
    }
    tagged_hash("TapSighash", &[&m])
}

fn serialize_tx(
    locktime: u32,
    inputs: &[([u8; 32], u32, u32)],
    outputs: &[(u64, Vec<u8>)],
    witnesses: &[Vec<Vec<u8>>],
) -> Vec<u8> {
    let mut t = Vec::new();
    t.extend(2u32.to_le_bytes());
    t.push(0x00);
    t.push(0x01); // segwit marker+flag
    t.extend(cs(inputs.len()));
    for (txid, vout, seq) in inputs {
        t.extend(txid);
        t.extend(vout.to_le_bytes());
        t.extend(cs(0));
        t.extend(seq.to_le_bytes());
    }
    t.extend(cs(outputs.len()));
    for (a, spk) in outputs {
        t.extend(a.to_le_bytes());
        t.extend(cs(spk.len()));
        t.extend(spk);
    }
    for w in witnesses {
        t.extend(cs(w.len()));
        for item in w {
            t.extend(cs(item.len()));
            t.extend(item);
        }
    }
    t.extend(locktime.to_le_bytes());
    t
}

// --- compile + taproot artifacts ---

fn pipeline(src: &str, args: &str) -> (ContractInfo, Env, Vec<LoweredLeaf>, taproot::Assembled) {
    let (contract, pd) = parser::parse_source(src);
    assert!(pd.is_empty(), "parse: {pd:#?}");
    let c = contract.unwrap();
    let (sd, info) = sema::analyze(&c);
    assert!(
        sd.iter().all(|d| d.severity != Severity::Error),
        "sema: {sd:#?}"
    );
    let mut env = bind_args(&info, &json::parse(args).unwrap()).unwrap();
    let id = instantiate(&c, &mut env);
    assert!(id.iter().all(|d| d.severity != Severity::Error));
    let (b, report) = intervals::analyze(&c, &env);
    assert!(b.is_empty());
    let (pd2, _) = paths::analyze(&c, &info, &env);
    assert!(pd2.iter().all(|d| d.severity != Severity::Error));
    let (ld, leaves) = lower(&c, &info, &env, &report);
    assert!(ld.iter().all(|d| d.severity != Severity::Error));
    let leaves: Vec<_> = leaves.iter().map(optimize).collect();
    let out = taproot::assemble_contract(&c, &env, &leaves).expect("assemble");
    (info, env, leaves, out.assembled)
}

const FEE: u64 = 2_000;
const SECKEY: [u8; 32] = [0x11; 32];
const SEQ: u32 = 0xffff_fffe;
// Two further valid x-only keys (from the vendored example args, so known to
// lift_x cleanly). Used as the non-signed partners in corpus contracts so the
// MuSig2 key-path aggregate is over DISTINCT keys -- only the leaf we actually
// spend is bound to our test key.
const OTHER_A: &str = "5cbdf0646e5db4eaa398f365f2ea7a0e3d419b7e0330e39ce92bddedcac4f9bc";
const OTHER_B: &str = "f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8";

fn pubkey_xonly() -> [u8; 32] {
    use seal::crypto::secp::{U256, generator};
    (generator() * U256::from_be_bytes(&SECKEY))
        .x_bytes()
        .expect("finite")
}

/// Args binding the single extern `k` to our test pubkey.
fn k_args() -> String {
    format!(r#"{{"k": "0x{}"}}"#, hex(&pubkey_xonly()))
}

/// A fixed output (a standard v1 program to a burn key) for every spend tx.
fn out_spk() -> Vec<u8> {
    let mut s = vec![0x51, 0x20];
    s.extend([0u8; 32]);
    s
}

/// (amount in sats, scriptPubKey hex) of an unspent coinbase output, read from
/// the node -- the subsidy halves every 150 regtest blocks, so it must be
/// queried, not assumed.
fn coinbase_amount_and_spk(node: &Node, cb: &([u8; 32], u32)) -> (u64, String) {
    let mut disp = cb.0;
    disp.reverse();
    let utxo = node.cli(&["gettxout", &hex(&disp), &cb.1.to_string()]);
    let spk = json_str(&utxo, "hex").expect("utxo spk").to_string();
    let amount = (json_num(&utxo, "value").expect("utxo value") * 1e8).round() as u64;
    (amount, spk)
}

struct Tcase {
    name: &'static str,
    plan: Vec<(String, SatValue)>,
    tamper_sig: bool,
    expect: bool,
}

fn run_contract(node: &Node, src: &str, args: &str, spend: &str, cases: &[Tcase]) {
    let (info, env, leaves, asm) = pipeline(src, args);
    let li = leaves.iter().position(|l| l.name == spend).unwrap();
    let leaf = &leaves[li];
    let sig = info.spends.iter().find(|s| s.name == spend).unwrap();

    let mut p2tr = vec![0x51, 0x20];
    p2tr.extend(asm.output_key);
    let address = bech32m::encode_p2tr("bcrt", &asm.output_key);
    let cb = node.coinbase_to(&address);
    node.cli(&["generatetoaddress", "100", &address]); // mature it

    // Cross-check T3: Core's coinbase scriptPubKey == our P2TR, and read the
    // real subsidy (it halves every 150 blocks).
    let (amount, spk_hex) = coinbase_amount_and_spk(node, &cb);
    assert_eq!(spk_hex, hex(&p2tr), "P2TR scriptPubKey mismatch");

    let outputs = [(amount - FEE, out_spk())];
    let sighash = taproot_sighash(
        2,
        0,
        &[(cb.0, cb.1)],
        &[amount],
        &[p2tr.clone()],
        &[SEQ],
        &outputs,
        0,
        Some(&leaf_hash(&asm, li)),
    );
    let valid_sig = seal::crypto::schnorr::sign(&SECKEY, &sighash, &[0u8; 32]).expect("sign");

    for tc in cases {
        let sig_bytes: Vec<u8> = if tc.tamper_sig {
            let mut s = valid_sig.to_vec();
            s[10] ^= 0x01;
            s
        } else {
            valid_sig.to_vec()
        };
        let stack = build_witness(leaf, sig, &env, &tc.plan, &sig_bytes).expect("witness");

        // Our interpreter's verdict (oracle: valid iff the real signature).
        let vsig = valid_sig.to_vec();
        let oracle = |_pk: &[u8], s: &[u8]| s == vsig.as_slice();
        let ctx = Context {
            locktime: 0,
            sequence: SEQ,
            tx_version: 2,
            verify_sig: &oracle,
        };
        let ours = execute(&leaf.script, &stack, &ctx).is_ok();

        // Core's verdict via testmempoolaccept on the real spend.
        let mut wit = stack;
        wit.push(leaf.script.clone());
        wit.push(asm.leaves[li].control_block.clone());
        let tx = serialize_tx(0, &[(cb.0, cb.1, SEQ)], &outputs, &[wit]);
        let res = node.cli(&["testmempoolaccept", &format!("[\"{}\"]", hex(&tx))]);
        let compact: String = res.split_whitespace().collect();
        let core = compact.contains("\"allowed\":true");
        if !core {
            eprintln!(
                "  {} [{}]: reject-reason {}",
                spend,
                tc.name,
                json_str(&res, "reject-reason").unwrap_or("?")
            );
        }

        assert_eq!(
            core, tc.expect,
            "{spend} [{}]: real bitcoind verdict",
            tc.name
        );
        assert_eq!(
            ours, core,
            "{spend} [{}]: our interpreter vs real bitcoind",
            tc.name
        );
    }
}

fn leaf_hash(asm: &taproot::Assembled, i: usize) -> [u8; 32] {
    asm.leaves[i].hash
}

/// How to advance the chain so a timelock is satisfiable when it should be:
/// to an absolute HEIGHT (CLTV height / CSV blocks just need maturity), to an
/// absolute median-time (CLTV time), or by a relative median-time delta past
/// the coinbase (CSV time / BIP68). The time modes drive `setmocktime` so the
/// median-time-past actually reaches the target.
enum TimeMode {
    Height(u32),
    Depth(u32),
    AbsTime(u64),
    RelTime(u64),
}

/// A timelocked single-sig contract: each case fixes the spend's nLockTime and
/// the input's nSequence, so we exercise OP_CHECKLOCKTIMEVERIFY /
/// OP_CHECKSEQUENCEVERIFY against a real node at and across the boundary. The
/// sighash commits to nLockTime and nSequence, so each case is re-signed.
#[allow(clippy::too_many_arguments)]
fn run_timelock(
    node: &Node,
    src: &str,
    args: &str,
    spend: &str,
    mode: TimeMode,
    plan: &[(String, SatValue)],
    cases: &[(u32, u32, &str, bool)], // (nLockTime, nSequence, label, expect)
) {
    let (info, env, leaves, asm) = pipeline(src, args);
    let li = leaves.iter().position(|l| l.name == spend).unwrap();
    let leaf = &leaves[li];
    let sig = info.spends.iter().find(|s| s.name == spend).unwrap();

    let mut p2tr = vec![0x51, 0x20];
    p2tr.extend(asm.output_key);
    let address = bech32m::encode_p2tr("bcrt", &asm.output_key);
    let cb = node.coinbase_to(&address);
    // Mature the coinbase, and make the timelock satisfiable for the cases that
    // should pass.
    match mode {
        TimeMode::Height(h) => {
            node.cli(&["generatetoaddress", "110", &address]); // maturity (+ small CSV depth)
            let height: u32 = node.cli(&["getblockcount"]).trim().parse().unwrap();
            if height < h {
                node.cli(&["generatetoaddress", &(h - height + 1).to_string(), &address]);
            }
        }
        TimeMode::Depth(d) => {
            // CSV by blocks needs the coinbase >= d deep (also covers maturity).
            node.cli(&["generatetoaddress", &(d + 1).max(110).to_string(), &address]);
        }
        TimeMode::AbsTime(target) => {
            // Push the median-time-past to `target` by mining at that mocktime.
            node.cli(&["setmocktime", &target.to_string()]);
            node.cli(&["generatetoaddress", "110", &address]);
        }
        TimeMode::RelTime(delta) => {
            // Advance the median-time-past by `delta` seconds past the coinbase,
            // so the relative (BIP68) lock is satisfied.
            let now = json_num(&node.cli(&["getblockchaininfo"]), "mediantime").unwrap() as u64;
            node.cli(&["setmocktime", &(now + delta).to_string()]);
            node.cli(&["generatetoaddress", "110", &address]);
        }
    }

    let (amount, spk_hex) = coinbase_amount_and_spk(node, &cb);
    assert_eq!(spk_hex, hex(&p2tr), "P2TR scriptPubKey mismatch");
    let outputs = [(amount - FEE, out_spk())];

    for &(nlocktime, nsequence, label, expect) in cases {
        let sighash = taproot_sighash(
            2,
            nlocktime,
            &[(cb.0, cb.1)],
            &[amount],
            &[p2tr.clone()],
            &[nsequence],
            &outputs,
            0,
            Some(&leaf_hash(&asm, li)),
        );
        let valid_sig = seal::crypto::schnorr::sign(&SECKEY, &sighash, &[0u8; 32]).expect("sign");
        let stack = build_witness(leaf, sig, &env, plan, &valid_sig).expect("witness");

        // Our interpreter judges the same context (CLTV/CSV check ctx).
        let vsig = valid_sig.to_vec();
        let oracle = |_pk: &[u8], s: &[u8]| s == vsig.as_slice();
        let ctx = Context {
            locktime: nlocktime,
            sequence: nsequence,
            tx_version: 2,
            verify_sig: &oracle,
        };
        let ours = execute(&leaf.script, &stack, &ctx).is_ok();

        let mut wit = stack;
        wit.push(leaf.script.clone());
        wit.push(asm.leaves[li].control_block.clone());
        let tx = serialize_tx(nlocktime, &[(cb.0, cb.1, nsequence)], &outputs, &[wit]);
        let res = node.cli(&["testmempoolaccept", &format!("[\"{}\"]", hex(&tx))]);
        let core = res
            .split_whitespace()
            .collect::<String>()
            .contains("\"allowed\":true");
        if !core {
            eprintln!(
                "  {spend} [{label}]: reject-reason {}",
                json_str(&res, "reject-reason").unwrap_or("?")
            );
        }
        assert_eq!(core, expect, "{spend} [{label}]: real bitcoind verdict");
        assert_eq!(
            ours, core,
            "{spend} [{label}]: our interpreter vs real bitcoind"
        );
    }
}

/// A key-path spend: the witness is a single BIP340 signature under the
/// TWEAKED output key (no script, no control block). This exercises the OTHER
/// half of BIP341 -- the key-path sighash (spend_type 0, no tapleaf extension)
/// and the taproot tweak `Q = P + t*G` -- which the script-path harness never
/// touches. Our tapscript interpreter has no role here (key-path validation is
/// pure consensus signature-checking against the output key), so this asserts
/// Core's verdict only: the real tweaked-key signature is accepted, a tampered
/// one rejected.
fn run_keypath(node: &Node, src: &str, args: &str) {
    use seal::crypto::secp::{U256, add_mod_n, generator, neg_scalar, scalar_mod_n};

    let (_info, _env, _leaves, asm) = pipeline(src, args);

    let mut p2tr = vec![0x51, 0x20];
    p2tr.extend(asm.output_key);
    let address = bech32m::encode_p2tr("bcrt", &asm.output_key);
    let cb = node.coinbase_to(&address);
    node.cli(&["generatetoaddress", "100", &address]); // mature it

    let (amount, spk_hex) = coinbase_amount_and_spk(node, &cb);
    assert_eq!(spk_hex, hex(&p2tr), "P2TR scriptPubKey mismatch");

    let outputs = [(amount - FEE, out_spk())];
    // Key-path sighash: spend_type 0, no tapleaf extension (tapleaf = None).
    let sighash = taproot_sighash(
        2,
        0,
        &[(cb.0, cb.1)],
        &[amount],
        &[p2tr.clone()],
        &[SEQ],
        &outputs,
        0,
        None,
    );

    // Tweaked secret: e = d' + t (mod n), where d' is SECKEY in the even-y
    // convention of the LIFTED internal key (lift_x always picks even y, so the
    // matching secret negates when SECKEY*G is odd-y), and t is the BIP341 tap
    // tweak the assembler already committed to. sign() recomputes Q = e*G and
    // re-applies the even-y convention, so the sig verifies against output_key.
    let d0 = U256::from_be_bytes(&SECKEY);
    let p_internal = generator() * d0;
    let d_adj = if p_internal.has_even_y() {
        d0
    } else {
        neg_scalar(d0)
    };
    assert_eq!(
        p_internal.x_bytes(),
        Some(asm.internal_key),
        "internal key is k"
    );
    let t = scalar_mod_n(U256::from_be_bytes(&asm.tweak));
    let e = add_mod_n(d_adj, t);
    let valid_sig =
        seal::crypto::schnorr::sign(&e.to_be_bytes(), &sighash, &[0u8; 32]).expect("sign");

    for (label, tamper, expect) in [
        ("valid key-path sig", false, true),
        ("tampered key-path sig", true, false),
    ] {
        let mut sigv = valid_sig.to_vec();
        if tamper {
            sigv[10] ^= 0x01;
        }
        let tx = serialize_tx(0, &[(cb.0, cb.1, SEQ)], &outputs, &[vec![sigv]]);
        let res = node.cli(&["testmempoolaccept", &format!("[\"{}\"]", hex(&tx))]);
        let core = res
            .split_whitespace()
            .collect::<String>()
            .contains("\"allowed\":true");
        if !core {
            eprintln!(
                "  keypath [{label}]: reject-reason {}",
                json_str(&res, "reject-reason").unwrap_or("?")
            );
        }
        assert_eq!(core, expect, "keypath [{label}]: real bitcoind verdict");
    }
}

fn votes(true_count: usize) -> SatValue {
    SatValue::Array((0..8).map(|i| SatValue::Bool(i < true_count)).collect())
}

#[test]
fn real_bitcoind_accepts_and_rejects_our_taproot_spends() {
    let Some(node) = Node::start() else {
        // In CI the gold-standard check is mandatory: a missing node is a
        // failure, never a silent skip-as-pass.
        assert!(
            std::env::var("BASIS_REQUIRE_CORE").is_err(),
            "BASIS_REQUIRE_CORE is set but bitcoind/bitcoin-cli was not found (build per vendor/README.md)"
        );
        eprintln!(
            "SKIP: bitcoind/bitcoin-cli not found (set BITCOIN_BUILD; build per vendor/README.md)."
        );
        return;
    };

    // Single signature: the minimal real script-path spend.
    run_contract(
        &node,
        "contract T { extern const k: PublicKey;
            spend f(s: Signature) { require { k.check(s) } } keypath None; }",
        &k_args(),
        "f",
        &[
            Tcase {
                name: "valid sig",
                plan: vec![("s".into(), SatValue::Sig(true))],
                tamper_sig: false,
                expect: true,
            },
            Tcase {
                name: "tampered sig",
                plan: vec![("s".into(), SatValue::Sig(true))],
                tamper_sig: true,
                expect: false,
            },
        ],
    );

    // quorum: the CSE-optimized tally, through real consensus.
    run_contract(
        &node,
        "contract T { extern const k: PublicKey;
            spend act(relaxed votes: [Bool; 8], s: Signature) {
                require {
                    count(v in votes where v => true) >= 3,
                    count(v in votes where v => true) <= 6,
                    k.check(s)
                }
            } keypath None; }",
        &k_args(),
        "act",
        &[
            Tcase {
                name: "4 votes, valid",
                plan: vec![
                    ("votes".into(), votes(4)),
                    ("s".into(), SatValue::Sig(true)),
                ],
                tamper_sig: false,
                expect: true,
            },
            Tcase {
                name: "2 votes (too few)",
                plan: vec![
                    ("votes".into(), votes(2)),
                    ("s".into(), SatValue::Sig(true)),
                ],
                tamper_sig: false,
                expect: false,
            },
            Tcase {
                name: "7 votes (too many)",
                plan: vec![
                    ("votes".into(), votes(7)),
                    ("s".into(), SatValue::Sig(true)),
                ],
                tamper_sig: false,
                expect: false,
            },
            Tcase {
                name: "4 votes, tampered sig",
                plan: vec![
                    ("votes".into(), votes(4)),
                    ("s".into(), SatValue::Sig(true)),
                ],
                tamper_sig: true,
                expect: false,
            },
        ],
    );

    // CLTV (absolute height 150): nLockTime at the boundary accepts, below it
    // the OP_CHECKLOCKTIMEVERIFY fails. nSequence stays non-final so the lock
    // is enforced. Mine to height >= 150 so the at-boundary tx is final.
    run_timelock(
        &node,
        "contract T { extern const k: PublicKey;
            spend f(s: Signature) { require { after(LockTime.Absolute(height: 150)), k.check(s) } } keypath None; }",
        &k_args(),
        "f",
        TimeMode::Height(150),
        &[("s".into(), SatValue::Sig(true))],
        &[
            (150, SEQ, "nLockTime == 150", true),
            (149, SEQ, "nLockTime == 149 (too early)", false),
            (200, SEQ, "nLockTime == 200 (later, still ok)", true),
        ],
    );

    // CSV (relative 10 blocks): the input is ~110 deep, so the relative lock is
    // satisfiable; nSequence at/above the operand accepts, below it the
    // OP_CHECKSEQUENCEVERIFY fails. (Our interpreter checks the script-level
    // sequence rule; BIP68 input-age is a tx rule Core also enforces, and the
    // deep coinbase satisfies it.)
    run_timelock(
        &node,
        "contract T { extern const k: PublicKey;
            spend f(s: Signature) { require { after(LockTime.Relative(blocks: 10)), k.check(s) } } keypath None; }",
        &k_args(),
        "f",
        TimeMode::Height(0),
        &[("s".into(), SatValue::Sig(true))],
        &[
            (0, 10, "nSequence == 10", true),
            (0, 11, "nSequence == 11 (older, still ok)", true),
            (0, 9, "nSequence == 9 (too soon)", false),
        ],
    );

    // CLTV by TIME (absolute, ISO-8601 -> unix seconds, MTP-evaluated). Operand
    // 2051222400 (2035-01-01Z). Mine the median-time-past past it so an
    // at-boundary nLockTime is final; below the boundary CLTV fails.
    const T_ABS: u32 = 2_051_222_400;
    run_timelock(
        &node,
        "contract T { extern const k: PublicKey;
            spend f(s: Signature) { require { after(LockTime.Absolute(time: \"2035-01-01T00:00:00Z\")), k.check(s) } } keypath None; }",
        &k_args(),
        "f",
        TimeMode::AbsTime(T_ABS as u64 + 100_000),
        &[("s".into(), SatValue::Sig(true))],
        &[
            (T_ABS, SEQ, "nLockTime == operand", true),
            (T_ABS - 1, SEQ, "nLockTime == operand-1 (too early)", false),
            (T_ABS + 600, SEQ, "nLockTime later (still ok)", true),
        ],
    );

    // CSV by TIME (relative, ISO-8601 duration -> 512s units, BIP68). "PT1H" =
    // 1h -> 8 units (rounded up) -> operand 0x400008 (time-type bit 22 set).
    // Advance the median-time-past by 8*512 s past the coinbase so BIP68 is
    // satisfied; nSequence at/above the operand accepts, below it CSV fails.
    const CSV_T: u32 = 0x0040_0008; // 8 units, time-type
    run_timelock(
        &node,
        "contract T { extern const k: PublicKey;
            spend f(s: Signature) { require { after(LockTime.Relative(time: \"PT1H\")), k.check(s) } } keypath None; }",
        &k_args(),
        "f",
        TimeMode::RelTime(8 * 512 + 20_000),
        &[("s".into(), SatValue::Sig(true))],
        &[
            (0, CSV_T, "nSequence == operand", true),
            (0, CSV_T + 1, "nSequence one unit older (still ok)", true),
            (0, CSV_T - 1, "nSequence one unit short (too soon)", false),
        ],
    );

    // --- Key-path spend: the BIP341 half the script-path harness never reaches.
    // A single-key internal key (keypath k), spent by a signature under the
    // TWEAKED output key, witness = [sig], no script reveal.
    run_keypath(
        &node,
        "contract T { extern const k: PublicKey;
            spend f(s: Signature) { require { k.check(s) } } keypath k; }",
        &k_args(),
    );

    // --- Corpus contracts, spent leaf-by-leaf through real consensus. Each
    // multi-leaf tree's control block must commit to the sibling leaves or Core
    // rejects the taproot path; the signed leaf is bound to our test key, the
    // key-path MuSig2 partner is a distinct key (never spent here).
    let htlc = std::fs::read_to_string(manifest().join("tests/corpus/htlc.sl")).expect("htlc.sl");
    let vault =
        std::fs::read_to_string(manifest().join("tests/corpus/vault.sl")).expect("vault.sl");
    let me = hex(&pubkey_xonly());

    // htlc.swap: hashlock + sig. The preimage is a real 32-byte secret whose
    // sha256 is the committed hashlock; a wrong preimage fails the hash check.
    let preimage = vec![0x42u8; 32];
    let hashlock = hex(&sha256(&preimage));
    let swap_args = format!(
        r#"{{"swap_key":"0x{me}","refund_key":"0x{OTHER_A}","timelock":{{"height":150}},"hashlock":"0x{hashlock}"}}"#
    );
    run_contract(
        &node,
        &htlc,
        &swap_args,
        "swap",
        &[
            Tcase {
                name: "preimage + valid sig",
                plan: vec![
                    ("preimage".into(), SatValue::Bytes(preimage.clone())),
                    ("signature".into(), SatValue::Sig(true)),
                ],
                tamper_sig: false,
                expect: true,
            },
            Tcase {
                name: "wrong preimage",
                plan: vec![
                    ("preimage".into(), SatValue::Bytes(vec![0x43u8; 32])),
                    ("signature".into(), SatValue::Sig(true)),
                ],
                tamper_sig: false,
                expect: false,
            },
            Tcase {
                name: "right preimage, tampered sig",
                plan: vec![
                    ("preimage".into(), SatValue::Bytes(preimage.clone())),
                    ("signature".into(), SatValue::Sig(true)),
                ],
                tamper_sig: true,
                expect: false,
            },
        ],
    );

    // htlc.refund: CLTV by absolute height (operand 150). The chain is already
    // well past 150 here, so the boundary is probed by the CLTV operand check
    // (nLockTime >= 150), not by finality.
    let refund_args = format!(
        r#"{{"swap_key":"0x{OTHER_A}","refund_key":"0x{me}","timelock":{{"height":150}},"hashlock":"0x{}"}}"#,
        "ab".repeat(32)
    );
    run_timelock(
        &node,
        &htlc,
        &refund_args,
        "refund",
        TimeMode::Height(150),
        &[("signature".into(), SatValue::Sig(true))],
        &[
            (150, SEQ, "nLockTime == 150", true),
            (149, SEQ, "nLockTime == 149 (too early)", false),
            (200, SEQ, "nLockTime == 200 (later, still ok)", true),
        ],
    );

    // vault.fallback: CSV by relative blocks (operand 4320). Mine the coinbase
    // >= 4320 deep so BIP68 is satisfied; nSequence at/above the operand
    // accepts, below it OP_CHECKSEQUENCEVERIFY fails.
    let vault_args = format!(r#"{{"hot":"0x{me}","cosigner":"0x{OTHER_A}","cold":"0x{OTHER_B}"}}"#);
    run_timelock(
        &node,
        &vault,
        &vault_args,
        "fallback",
        TimeMode::Depth(4320),
        &[("signature".into(), SatValue::Sig(true))],
        &[
            (0, 4320, "nSequence == 4320", true),
            (0, 4321, "nSequence == 4321 (older, still ok)", true),
            (0, 4319, "nSequence == 4319 (too soon)", false),
        ],
    );

    eprintln!(
        "regtest: real bitcoind accepted/rejected every case in agreement with our interpreter"
    );
}
