//! Phase 4, the faithful check: run OUR generated tapscript leaves + witnesses
//! through Bitcoin Core's REAL script interpreter (vendor/bitcoin) and require
//! accept/reject parity with our own interpreter, on the scripts the compiler
//! actually emits. Where `tests/core_differential.rs` validates our opcode
//! engine against Core's static corpus, this validates Core against OUR output.
//!
//! Heavyweight integration: it SKIPS (passing) unless Bitcoin Core is built.
//! Point it at the cmake build dir with BITCOIN_BUILD, or build into
//! vendor/bitcoin/build (see vendor/README.md). It compiles tests/core_eval.cpp
//! against Core's consensus libraries, then differentials in one batch.
//!
//! Scope: tapscript leaves WITHOUT timelocks (the harness's mock checker does
//! not carry a spend context); signatures use the shared 64x0xAA marker so the
//! crypto (T5) is isolated from the execution semantics (T4) under test.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use seal::analysis::consteval::{Env, bind_args, instantiate};
use seal::analysis::intervals;
use seal::analysis::paths;
use seal::analysis::sema;
use seal::analysis::sema::{ContractInfo, SpendSig};
use seal::codegen::lower::{LoweredLeaf, lower};
use seal::codegen::optimize::optimize;
use seal::diagnostics::Severity;
use seal::json;
use seal::syntax::parser;
use seal::verify::interp::{Context, execute};
use seal::verify::satisfy::{SatValue, build_witness};

const MARKER: [u8; 64] = [0xAA; 64];
const KEY: &str = "0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c";

fn manifest() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// Locate a Bitcoin Core cmake build dir (with the consensus static lib), or
/// None to skip the differential.
fn core_build_dir() -> Option<PathBuf> {
    let mut candidates: Vec<PathBuf> = Vec::new();
    if let Ok(p) = std::env::var("BITCOIN_BUILD") {
        candidates.push(PathBuf::from(p));
    }
    candidates.push(manifest().join("vendor/bitcoin/build"));
    candidates
        .into_iter()
        .find(|c| c.join("lib/libbitcoin_consensus.a").exists())
}

/// Compile tests/core_eval.cpp against Core's consensus libraries.
fn compile_harness(build: &Path) -> Option<PathBuf> {
    let out = std::env::temp_dir().join("basis_core_eval");
    let inc_src = manifest().join("vendor/bitcoin/src");
    let inc_build = build.join("src");
    let status = Command::new("clang++")
        .args(["-std=c++20", "-O1"])
        .arg("-I")
        .arg(&inc_src)
        .arg("-I")
        .arg(&inc_build)
        .arg(manifest().join("tests/core_eval.cpp"))
        .arg(build.join("lib/libbitcoin_consensus.a"))
        .arg(build.join("lib/libbitcoin_crypto.a"))
        .arg(build.join("lib/libbitcoin_util.a"))
        .arg(build.join("src/secp256k1/lib/libsecp256k1.a"))
        .arg("-o")
        .arg(&out)
        .status()
        .ok()?;
    status.success().then_some(out)
}

/// Run the harness on a batch of `<leaf>|<wit..>` lines; one bool per line.
fn run_core(bin: &Path, lines: &[String]) -> Vec<bool> {
    let mut child = Command::new(bin)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("spawn harness");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(lines.join("\n").as_bytes())
        .unwrap();
    let out = child.wait_with_output().expect("harness output");
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(|l| l.trim() == "1")
        .collect()
}

/// One witness line for the harness: leaf script, then each stack element.
fn line_for(leaf: &LoweredLeaf, stack: &[Vec<u8>]) -> String {
    let mut s = hex(&leaf.script);
    for e in stack {
        s.push('|');
        s.push_str(&hex(e));
    }
    s
}

fn pipeline(src: &str, args: &str) -> (ContractInfo, Env, Vec<LoweredLeaf>) {
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
    (info, env, leaves)
}

fn load(name: &str) -> (ContractInfo, Env, Vec<LoweredLeaf>) {
    let dir = manifest().join("tests/corpus");
    let src = std::fs::read_to_string(dir.join(format!("{name}.sl"))).unwrap();
    let args = std::fs::read_to_string(dir.join(format!("{name}.args.json"))).unwrap();
    pipeline(&src, &args)
}

fn sig_of<'a>(info: &'a ContractInfo, name: &str) -> &'a SpendSig {
    info.spends.iter().find(|s| s.name == name).unwrap()
}

/// Differential one leaf over a set of plans: our interpreter vs Core's, in one
/// harness batch. Returns the number of cases checked.
fn diff(
    bin: &Path,
    info: &ContractInfo,
    env: &Env,
    leaf: &LoweredLeaf,
    plans: &[Vec<(String, SatValue)>],
) -> usize {
    let opt = optimize(leaf);
    let sig = sig_of(info, &leaf.name);
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };

    let mut lines = Vec::with_capacity(plans.len());
    let mut ours = Vec::with_capacity(plans.len());
    for plan in plans {
        let stack = build_witness(&opt, sig, env, plan, &MARKER).expect("witness");
        ours.push(execute(&opt.script, &stack, &ctx).is_ok());
        lines.push(line_for(&opt, &stack));
    }
    let core = run_core(bin, &lines);
    assert_eq!(
        core.len(),
        plans.len(),
        "harness returned {} of {} results",
        core.len(),
        plans.len()
    );
    for (i, (o, c)) in ours.iter().zip(&core).enumerate() {
        assert_eq!(
            o, c,
            "leaf `{}` case {i}: ours={o} core={c}\n  {}",
            leaf.name, lines[i]
        );
    }
    plans.len()
}

fn leaf<'a>(leaves: &'a [LoweredLeaf], name: &str) -> &'a LoweredLeaf {
    leaves.iter().find(|l| l.name == name).unwrap()
}

#[test]
fn our_leaves_match_bitcoin_core_interpreter() {
    let require = std::env::var("BASIS_REQUIRE_CORE").is_ok();
    let Some(build) = core_build_dir() else {
        assert!(
            !require,
            "BASIS_REQUIRE_CORE is set but Bitcoin Core is not built (set BITCOIN_BUILD)"
        );
        eprintln!(
            "SKIP: Bitcoin Core not built. Set BITCOIN_BUILD=<cmake build dir> \
             or build into vendor/bitcoin/build (see vendor/README.md)."
        );
        return;
    };
    let Some(bin) = compile_harness(&build) else {
        assert!(
            !require,
            "BASIS_REQUIRE_CORE is set but tests/core_eval.cpp could not be compiled"
        );
        eprintln!("SKIP: could not compile tests/core_eval.cpp (clang++ / Core libs).");
        return;
    };

    let mut total = 0;

    // quorum: the CSE-optimized leaf, EXHAUSTIVELY -- every one of the 512
    // witnesses (2^8 votes x present/declined sig) run through Core's real
    // tapscript interpreter and required to agree with ours.
    {
        let (info, env, leaves) = load("quorum");
        let votes = |mask: usize| {
            SatValue::Array(
                (0..8)
                    .map(|i| SatValue::Bool((mask >> i) & 1 == 1))
                    .collect(),
            )
        };
        let mut plans = Vec::new();
        for mask in 0..256usize {
            for sig in [true, false] {
                plans.push(vec![
                    ("votes".to_string(), votes(mask)),
                    ("s".to_string(), SatValue::Sig(sig)),
                ]);
            }
        }
        total += diff(&bin, &info, &env, leaf(&leaves, "act"), &plans);
    }

    // multisig: the threshold chain over every signature combination.
    {
        let (info, env, leaves) = load("multisig");
        let l = leaf(&leaves, "fallback");
        let n = sig_of(&info, "fallback")
            .params
            .iter()
            .find(|p| matches!(&p.ty, seal::analysis::sema::Ty::Array(e, _) if **e == seal::analysis::sema::Ty::Signature))
            .map(|p| match &p.ty {
                seal::analysis::sema::Ty::Array(_, seal::analysis::sema::Len::Lit(k)) => *k as usize,
                _ => 0,
            })
            .unwrap_or(0);
        let pname = sig_of(&info, "fallback").params[0].name.clone();
        if n > 0 && n <= 12 {
            let mut plans = Vec::new();
            for mask in 0..(1usize << n) {
                let sigs = SatValue::Array(
                    (0..n)
                        .map(|i| SatValue::Sig((mask >> i) & 1 == 1))
                        .collect(),
                );
                plans.push(vec![(pname.clone(), sigs)]);
            }
            total += diff(&bin, &info, &env, l, &plans);
        }
    }

    // An inline SHA-256 hashlock + signature: exercises HASH/EQUAL/CHECKSIG end
    // to end through Core (accept with the preimage, reject without).
    {
        let preimage = vec![0x42u8; 32];
        let digest = seal::crypto::sha256::sha256(&preimage);
        let src = "contract T { extern const k: PublicKey; extern const h: Bytes<32>;
            spend f(p: Bytes<32>, s: Signature) { require { sha256(p) == h, k.check(s) } } keypath None; }";
        let args = format!(r#"{{"k": "{KEY}", "h": "0x{}"}}"#, hex(&digest));
        let (info, env, leaves) = pipeline(src, &args);
        let plans = vec![
            vec![
                ("p".to_string(), SatValue::Bytes(preimage.clone())),
                ("s".to_string(), SatValue::Sig(true)),
            ],
            vec![
                ("p".to_string(), SatValue::Bytes(vec![0x99u8; 32])),
                ("s".to_string(), SatValue::Sig(true)),
            ],
            vec![
                ("p".to_string(), SatValue::Bytes(preimage)),
                ("s".to_string(), SatValue::Sig(false)),
            ],
        ];
        total += diff(&bin, &info, &env, leaf(&leaves, "f"), &plans);
    }

    // The CSE three-item run (>=3, <=6, !=4): every witness through Core.
    {
        let src = "contract T { extern const k: PublicKey;
            spend f(relaxed votes: [Bool; 8], s: Signature) {
                require {
                    count(v in votes where v => true) >= 3,
                    count(v in votes where v => true) <= 6,
                    count(v in votes where v => true) != 4,
                    k.check(s)
                }
            } keypath None; }";
        let args = format!(r#"{{"k": "{KEY}"}}"#);
        let (info, env, leaves) = pipeline(src, &args);
        let votes = |mask: usize| {
            SatValue::Array(
                (0..8)
                    .map(|i| SatValue::Bool((mask >> i) & 1 == 1))
                    .collect(),
            )
        };
        let mut plans = Vec::new();
        for mask in 0..256usize {
            plans.push(vec![
                ("votes".to_string(), votes(mask)),
                ("s".to_string(), SatValue::Sig(true)),
            ]);
        }
        total += diff(&bin, &info, &env, leaf(&leaves, "f"), &plans);
    }

    // cat_bounty: the SWAP-fold weighted-sum leaf with its 37 zero-weight pixels
    // ELIMINATED from script and witness. Runs the reduced 748-element witness
    // (and OP_SWAP in the fold) through Core's real interpreter -- the only place
    // either the SWAP fold or the dead-witness reduction reaches a Core node.
    // An above-threshold drawing accepts; an all-clear drawing (score == bias)
    // and a declined signature reject. We require agreement, not a fixed verdict.
    {
        let (info, env, leaves) = load("cat_bounty");
        // weights cycle -10..=10 (period 21); positive-weight pixels score high.
        let weight = |i: usize| -10 + (i % 21) as i64;
        let pass = SatValue::Array((0..784).map(|i| SatValue::Bool(weight(i) > 0)).collect());
        let clear = SatValue::Array((0..784).map(|_| SatValue::Bool(false)).collect());
        let plans = vec![
            vec![
                ("drawing".to_string(), pass.clone()),
                ("signature".to_string(), SatValue::Sig(true)),
            ],
            vec![
                ("drawing".to_string(), clear),
                ("signature".to_string(), SatValue::Sig(true)),
            ],
            vec![
                ("drawing".to_string(), pass),
                ("signature".to_string(), SatValue::Sig(false)),
            ],
        ];
        total += diff(&bin, &info, &env, leaf(&leaves, "claim"), &plans);
    }

    eprintln!(
        "core consensus differential: {total} cases, our interpreter == Bitcoin Core, 0 mismatches"
    );
    assert!(
        total >= 700,
        "expected a meaningful number of cases, got {total}"
    );
}
