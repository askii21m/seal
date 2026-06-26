//! Breakpoint-completeness fuzz for the Phase 3 symbolic prover (`src/decide.rs`,
//! Engine A). For a wide family of single-Int affine contracts (varied bounding
//! range x dead/live clauses, exercising within/min/max/abs/widened-arithmetic/
//! negation), whenever `certify` returns `Proven(FullInt)` we re-execute naive
//! vs optimized over a dense range PLUS deep-tail samples up to +/-(2^31-1). A
//! single naive != opt at any point would be a false Proven. This is the
//! empirical backstop behind the structural soundness argument: if the symbolic
//! pass ever missed a breakpoint, a Proven leaf would diverge here.
//!
//! Heavier than the focused `tests/decide.rs` (hundreds of leaves x thousands of
//! points); run it as its own binary.

use seal::analysis::consteval::{Env, bind_args, instantiate};
use seal::analysis::intervals;
use seal::analysis::paths;
use seal::analysis::sema;
use seal::analysis::sema::{ContractInfo, SpendSig};
use seal::codegen::lower::{LoweredLeaf, lower};
use seal::codegen::optimize::optimize;
use seal::diagnostics::Severity;
use seal::json;
use seal::syntax::ast::Contract;
use seal::syntax::parser;
use seal::verify::certify::{CertStatus, LeafReport, ProvenKind, certify};
use seal::verify::interp::{Context, execute};
use seal::verify::satisfy::{SatValue, build_witness};

const MARKER: [u8; 64] = [0xAA; 64];
const KEY: &str = "0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c";

fn pipeline(src: &str, args: &str) -> Option<(Contract, ContractInfo, Env, Vec<LoweredLeaf>)> {
    let (contract, pd) = parser::parse_source(src);
    if !pd.is_empty() {
        return None;
    }
    let c = contract?;
    let (sd, info) = sema::analyze(&c);
    if !sd.is_empty() {
        return None;
    }
    let mut env = bind_args(&info, &json::parse(args).ok()?).ok()?;
    if instantiate(&c, &mut env)
        .iter()
        .any(|d| d.severity == Severity::Error)
    {
        return None;
    }
    let (b, report) = intervals::analyze(&c, &env);
    if !b.is_empty() {
        return None;
    }
    let (pd2, _) = paths::analyze(&c, &info, &env);
    if pd2.iter().any(|d| d.severity == Severity::Error) {
        return None;
    }
    let (ld, leaves) = lower(&c, &info, &env, &report);
    if ld.iter().any(|d| d.severity == Severity::Error) {
        return None;
    }
    Some((c, info, env, leaves))
}

fn ctx<'a>(o: &'a dyn Fn(&[u8], &[u8]) -> bool) -> Context<'a> {
    Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: o,
    }
}

fn run_certify(
    c: &Contract,
    info: &ContractInfo,
    env: &Env,
    n: &[LoweredLeaf],
    o: &[LoweredLeaf],
) -> Vec<LeafReport> {
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    certify(c, info, env, n, o, &MARKER, &ctx(&oracle))
}

fn accepts(
    leaf: &LoweredLeaf,
    sig: &SpendSig,
    env: &Env,
    name: &str,
    x: i64,
    present: bool,
) -> bool {
    let plan = vec![
        (name.to_string(), SatValue::Int(x)),
        ("s".to_string(), SatValue::Sig(present)),
    ];
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    match build_witness(leaf, sig, env, &plan, &MARKER) {
        Ok(st) => execute(&leaf.script, &st, &ctx(&oracle)).is_ok(),
        Err(_) => false,
    }
}

/// Certify `src`; for every Proven(FullInt) leaf, brute-force T2 over a dense
/// range and deep-tail samples. Returns the number of Proven leaves verified.
fn verify_proven(src: &str) -> u32 {
    let args = format!("{{\"k\":\"{KEY}\"}}");
    let Some((c, info, env, naive)) = pipeline(src, &args) else {
        return 0;
    };
    let opt: Vec<LoweredLeaf> = naive.iter().map(optimize).collect();
    let rs = run_certify(&c, &info, &env, &naive, &opt);

    // Dense near every breakpoint, plus tail samples spanning the machine domain.
    let mut xs: Vec<i64> = (-1500..=1500).collect();
    for k in 0..48 {
        let v = (1i64 << 24).wrapping_mul(k);
        xs.push(v);
        xs.push(-v);
    }
    for v in [
        i32::MAX as i64,
        i32::MIN as i64 + 1,
        1_073_741_823,
        1_073_741_824,
        536_870_911,
    ] {
        xs.push(v);
        xs.push(-v);
    }

    let mut proven = 0;
    for r in &rs {
        let CertStatus::Proven {
            kind: ProvenKind::FullInt { var, .. },
        } = &r.status
        else {
            continue;
        };
        proven += 1;
        let nl = naive.iter().find(|l| l.name == r.name).unwrap();
        let ol = opt.iter().find(|l| l.name == r.name).unwrap();
        let sig = info.spends.iter().find(|s| s.name == r.name).unwrap();
        for present in [false, true] {
            for &x in &xs {
                assert_eq!(
                    accepts(nl, sig, &env, var, x, present),
                    accepts(ol, sig, &env, var, x, present),
                    "FALSE PROVEN (T2): leaf {} diverges at x={x} present={present}\nsrc={src}",
                    r.name
                );
            }
        }
    }
    proven
}

#[test]
fn audit_faithfulness_fuzz() {
    let bounds = [(0i64, 1000i64), (-500, 500), (0, 100), (-1000, 0), (1, 2)];
    let clauses = [
        "x >= 0",
        "x < 5000",
        "x + x < 3000",
        "min(x, 9999) <= 1000",
        "max(x, -10) >= -50",
        "abs(x) < 4000",
        "x - 1 < 4999",
        "x != -77",
        "2000 > x",
        "x + 3 - 3 < 9999",
        "min(x, x) < 9000",
        "x <= 999",
    ];
    let mut total_proven = 0u32;
    for (lo, hi) in bounds {
        for c0 in 0..clauses.len() {
            for c1 in c0..clauses.len() {
                let src = format!(
                    "contract F {{ extern const k: PublicKey;
                       spend claim(relaxed x: Int, s: Signature) {{
                         require {{ x in {lo}..{hi}, {}, {}, k.check(s) }} }}
                       keypath None; }}",
                    clauses[c0], clauses[c1]
                );
                total_proven += verify_proven(&src);
            }
        }
    }
    eprintln!("decide fuzz: {total_proven} Proven(FullInt) leaves verified clean");
    assert!(
        total_proven > 0,
        "fuzz never reached a Proven verdict; test is vacuous"
    );
}
