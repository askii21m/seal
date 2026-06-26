//! The fuzzer: model-based property testing over thousands of randomized
//! contracts. The generator picks the honest parameter values FIRST, then
//! synthesizes constraints those values satisfy, so the money-property is
//! mechanically checkable end to end:
//!
//!   - TOTALITY: no random source/args ever panics the compiler.
//!   - COMPILES implies SPENDABLE: a clean compile means the honest plan, run
//!     through the real interpreter, ACCEPTS.
//!   - NON-MALLEABILITY: every tampered plan (declined sig, out-of-range
//!     value, flipped hint bit) is REJECTED.
//!   - DETERMINISM: the same source+args compiles to identical bytes.
//!
//! Everything is SEEDED (a deterministic in-process PRNG: no `rand`, no
//! clock, no OS entropy), so a failure prints a seed that reproduces it
//! exactly. Bounds are deliberately small (the parser's MAX_NESTING_DEPTH
//! and forward-progress guards already make pathological input safe;
//! generated sources stay tiny so a CI run is fast and never OOMs).

use std::panic::{AssertUnwindSafe, catch_unwind};

use seal::analysis::consteval::{Env, bind_args, instantiate};
use seal::analysis::intervals;
use seal::analysis::paths;
use seal::analysis::sema;
use seal::analysis::sema::{ContractInfo, SpendSig};
use seal::codegen::lower::{LoweredLeaf, lower};
use seal::codegen::optimize::optimize;
use seal::diagnostics::{Diagnostic, Severity};
use seal::json;
use seal::syntax::parser;
use seal::verify::interp::{Context, execute};
use seal::verify::satisfy::{SatValue, build_witness};

/// A valid on-curve x-only key (lift_x succeeds), reused for every extern.
const KEY: &str = "0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c";
const MARKER: [u8; 64] = [0xAA; 64];

// --- deterministic PRNG (SplitMix64) ---

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed ^ 0x123456789abcdef)
    }
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    /// Uniform in `[0, n)` (n >= 1).
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
    /// Uniform in `[lo, hi]`.
    fn between(&mut self, lo: i64, hi: i64) -> i64 {
        debug_assert!(lo <= hi);
        lo + self.below((hi - lo + 1) as u64) as i64
    }
}

// --- the compile pipeline (graceful: no asserts; returns the leaves or why) ---

struct Compiled {
    info: ContractInfo,
    env: Env,
    leaves: Vec<LoweredLeaf>,
}

fn errors(ds: &[Diagnostic]) -> Vec<String> {
    ds.iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| format!("{}: {}", d.code, d.message))
        .collect()
}

/// Run the whole front-to-back pipeline. `Ok(Some)` is compiled clean,
/// `Ok(None)` is rejected with errors (a valid outcome), `Err` is the
/// pipeline producing something internally inconsistent (a real bug).
fn compile(src: &str, args: &str) -> Result<Option<Compiled>, String> {
    let (contract, pd) = parser::parse_source(src);
    if !errors(&pd).is_empty() {
        return Ok(None);
    }
    let Some(c) = contract else { return Ok(None) };
    let (sd, info) = sema::analyze(&c);
    if !errors(&sd).is_empty() {
        return Ok(None);
    }
    let parsed = json::parse(args).map_err(|e| format!("args json: {e:?}"))?;
    let mut env = match bind_args(&info, &parsed) {
        Ok(e) => e,
        Err(_) => return Ok(None),
    };
    let id = instantiate(&c, &mut env);
    if !errors(&id).is_empty() {
        return Ok(None);
    }
    // Resource limits gate the interval engine and lowering (the OOM guard).
    if !errors(&seal::analysis::limits::analyze(&c, &info, &env)).is_empty() {
        return Ok(None);
    }
    let (g1, report) = intervals::analyze(&c, &env);
    if !errors(&g1).is_empty() {
        return Ok(None);
    }
    let (pd2, _) = paths::analyze(&c, &info, &env);
    if !errors(&pd2).is_empty() {
        return Ok(None);
    }
    let (ld, leaves) = lower(&c, &info, &env, &report);
    if !errors(&ld).is_empty() {
        return Ok(None);
    }
    Ok(Some(Compiled { info, env, leaves }))
}

fn sig_of<'a>(info: &'a ContractInfo, name: &str) -> &'a SpendSig {
    info.spends
        .iter()
        .find(|s| s.name == name)
        .expect("spendable sig")
}

/// Build a witness for `leaf` from a plan and execute it.
fn spend(
    c: &Compiled,
    leaf: &LoweredLeaf,
    plan: &[(&str, SatValue)],
    seq: u32,
    lt: u32,
) -> Result<(), String> {
    let sig = sig_of(&c.info, &leaf.name);
    let owned: Vec<(String, SatValue)> = plan
        .iter()
        .map(|(n, v)| (n.to_string(), v.clone()))
        .collect();
    let stack = build_witness(leaf, sig, &c.env, &owned, &MARKER)?;
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: lt,
        sequence: seq,
        tx_version: 2,
        verify_sig: &oracle,
    };
    execute(&leaf.script, &stack, &ctx)
}

// --- Stage 1 generator: sig + bounded int + a `>=` threshold ---

struct Gen {
    src: String,
    args: String,
    /// Honest plan and its tamper variants are derived from these.
    x: i64,
    lo: i64,
    hi: i64,
}

fn gen_stage1(seed: u64) -> Gen {
    let mut rng = Rng::new(seed);
    let x = rng.between(20, 1000); // honest value
    let lo = x - rng.below(20) as i64; // lo <= x, kept >= 0 (x >= 20)
    let hi = x + 1 + rng.below(20) as i64; // hi > x (range is half-open [lo, hi))
    let t = rng.between(lo, x); // lo <= t <= x implies honest x satisfies `x >= t`
    let src = format!(
        "contract Fuzz {{ extern const k: PublicKey;\n\
            spend s(relaxed x: Int, sig: Signature) {{\n\
                require {{ x in {lo}..{hi}, x >= {t}, k.check(sig) }}\n\
            }} keypath None; }}"
    );
    let args = format!(r#"{{"k": "{KEY}"}}"#);
    Gen {
        src,
        args,
        x,
        lo,
        hi,
    }
}

/// The differential for one generated contract: compile (no panic), then,
/// if it compiled, honest spends, declined sig fails, out-of-range fails.
fn check_stage1(seed: u64) -> Result<(), String> {
    let g = gen_stage1(seed);
    let compiled = compile(&g.src, &g.args)?;
    let Some(c) = compiled else {
        return Err(format!("generated contract failed to compile:\n{}", g.src));
    };
    let leaf = c
        .leaves
        .iter()
        .find(|l| l.name == "s")
        .ok_or("no leaf `s`")?;

    // Honest plan spends.
    let honest = [("x", SatValue::Int(g.x)), ("sig", SatValue::Sig(true))];
    spend(&c, leaf, &honest, 0xffff_fffe, 0)
        .map_err(|e| format!("honest plan rejected (x={}): {e}\n{}", g.x, g.src))?;

    // Declined signature is not spendable.
    let no_sig = [("x", SatValue::Int(g.x)), ("sig", SatValue::Sig(false))];
    if spend(&c, leaf, &no_sig, 0xffff_fffe, 0).is_ok() {
        return Err(format!("declined-sig plan WRONGLY spent:\n{}", g.src));
    }

    // Out-of-range value (x = hi, excluded) is not spendable.
    let oor = [("x", SatValue::Int(g.hi)), ("sig", SatValue::Sig(true))];
    if spend(&c, leaf, &oor, 0xffff_fffe, 0).is_ok() {
        return Err(format!("out-of-range x={} WRONGLY spent:\n{}", g.hi, g.src));
    }

    // Below-range value (x = lo - 1, excluded) is not spendable.
    let below = [("x", SatValue::Int(g.lo - 1)), ("sig", SatValue::Sig(true))];
    if spend(&c, leaf, &below, 0xffff_fffe, 0).is_ok() {
        return Err(format!(
            "below-range x={} WRONGLY spent:\n{}",
            g.lo - 1,
            g.src
        ));
    }

    // Determinism: recompiling yields identical leaf bytes.
    let again = compile(&g.src, &g.args)?.ok_or("re-compile failed")?;
    let leaf2 = again.leaves.iter().find(|l| l.name == "s").unwrap();
    if leaf.script != leaf2.script {
        return Err(format!("non-deterministic script bytes:\n{}", g.src));
    }
    Ok(())
}

/// Iteration scale: `BASIS_FUZZ=N` multiplies every stage's seed count (so CI
/// or a nightly run can hammer far harder than the fast default dev loop).
fn scale() -> u64 {
    std::env::var("BASIS_FUZZ")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(1)
}

/// Run `n * scale()` seeds through `check`, converting any panic into a
/// reproducible failure (prints the seed). One bad seed fails loudly.
fn run(label: &str, base_n: u64, base: u64, check: fn(u64) -> Result<(), String>) {
    let n = base_n.saturating_mul(scale());
    for i in 0..n {
        let seed = base.wrapping_add(i);
        let outcome = catch_unwind(AssertUnwindSafe(|| check(seed)));
        match outcome {
            Ok(Ok(())) => {}
            Ok(Err(msg)) => panic!("[{label}] seed {seed} FAILED:\n{msg}"),
            Err(_) => panic!("[{label}] seed {seed} PANICKED the compiler (totality violation)"),
        }
    }
}

#[test]
fn stage1_sig_and_bounded_int() {
    run("stage1", 1500, 0x5eed_0001, check_stage1);
}

// --- Stage 2: multi-constraint, multi-spend contracts ---

/// The x-only key `d*G`, a real public key, so `lift_x` always succeeds
/// (sema rejects off-curve keys). Distinct small `d` give distinct keys
/// (no `d`/`N-d` x-collision for small `d`).
fn nth_key(d: u64) -> String {
    use seal::crypto::secp::{U256, generator};
    let p = generator() * U256([d, 0, 0, 0]);
    let xb = p.x_bytes().expect("a generator multiple is finite");
    let hex: String = xb.iter().map(|b| format!("{b:02x}")).collect();
    format!("0x{hex}")
}

#[derive(Clone)]
struct Extern {
    name: String,
    ty: String,
    json: String,
}

/// One conjunct of a spend's `require`, with the witness values that satisfy
/// it (`honest`) and the overrides that must make it FAIL (`tampers`).
struct Clause {
    externs: Vec<Extern>,
    params: Vec<String>,
    text: String,
    honest: Vec<(String, SatValue)>,
    tampers: Vec<(String, Vec<(String, SatValue)>)>,
}

struct Builder {
    rng: Rng,
    ctr: usize,
    key_d: u64,
}

impl Builder {
    fn fresh(&mut self, prefix: &str) -> String {
        let n = self.ctr;
        self.ctr += 1;
        format!("{prefix}{n}")
    }
    fn key(&mut self) -> String {
        self.key_d += 1;
        nth_key(self.key_d)
    }

    /// `k.check(sig)`: a single signature gate.
    fn c_sig(&mut self) -> Clause {
        let k = self.fresh("k");
        let s = self.fresh("sig");
        Clause {
            externs: vec![Extern {
                name: k.clone(),
                ty: "PublicKey".into(),
                json: format!("\"{}\"", self.key()),
            }],
            params: vec![format!("{s}: Signature")],
            text: format!("{k}.check({s})"),
            honest: vec![(s.clone(), SatValue::Sig(true))],
            tampers: vec![(format!("decline {s}"), vec![(s, SatValue::Sig(false))])],
        }
    }

    /// `x in lo..hi`: a half-open range on a relaxed int.
    fn c_range(&mut self) -> Clause {
        let x = self.rng.between(20, 1000);
        let lo = x - self.rng.below(20) as i64; // >= 0 (x >= 20)
        let hi = x + 1 + self.rng.below(20) as i64; // > x
        let name = self.fresh("r");
        Clause {
            externs: vec![],
            params: vec![format!("relaxed {name}: Int")],
            text: format!("{name} in {lo}..{hi}"),
            honest: vec![(name.clone(), SatValue::Int(x))],
            tampers: vec![
                (
                    format!("{name}=hi"),
                    vec![(name.clone(), SatValue::Int(hi))],
                ),
                (format!("{name}=lo-1"), vec![(name, SatValue::Int(lo - 1))]),
            ],
        }
    }

    /// `a + b >= c`: checked addition compared to a threshold.
    fn c_arith(&mut self) -> Clause {
        let x = self.rng.between(1, 500);
        let y = self.rng.between(1, 500);
        let c = self.rng.between(1, x + y); // honest sum >= c
        let xn = self.fresh("a");
        let yn = self.fresh("b");
        let xhi = x + 1 + self.rng.below(50) as i64;
        let yhi = y + 1 + self.rng.below(50) as i64;
        Clause {
            externs: vec![],
            params: vec![format!("relaxed {xn}: Int"), format!("relaxed {yn}: Int")],
            text: format!("{xn} in 0..{xhi}, {yn} in 0..{yhi}, {xn} + {yn} >= {c}"),
            honest: vec![
                (xn.clone(), SatValue::Int(x)),
                (yn.clone(), SatValue::Int(y)),
            ],
            // Both at 0 gives sum 0 < c (c >= 1), so it fails.
            tampers: vec![(
                "sum->0".into(),
                vec![(xn, SatValue::Int(0)), (yn, SatValue::Int(0))],
            )],
        }
    }

    /// `sha256(p) == h`: a hashlock against a committed digest.
    fn c_hashlock(&mut self) -> Clause {
        let preimage: Vec<u8> = (0..32).map(|_| self.rng.below(256) as u8).collect();
        let digest = seal::crypto::sha256::sha256(&preimage);
        let hhex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
        let wrong: Vec<u8> = preimage.iter().map(|b| b ^ 0x5a).collect();
        let p = self.fresh("p");
        let h = self.fresh("h");
        Clause {
            externs: vec![Extern {
                name: h.clone(),
                ty: "Bytes<32>".into(),
                json: format!("\"0x{hhex}\""),
            }],
            params: vec![format!("{p}: Bytes<32>")],
            text: format!("sha256({p}) == {h}"),
            honest: vec![(p.clone(), SatValue::Bytes(preimage))],
            tampers: vec![(format!("wrong {p}"), vec![(p, SatValue::Bytes(wrong))])],
        }
    }

    /// `k0.check(s0) + k1.check(s1) + ... >= t`: an n-of-m threshold.
    fn c_threshold(&mut self) -> Clause {
        let n = self.rng.between(2, 4) as usize;
        let t = self.rng.between(1, n as i64);
        let mut externs = Vec::new();
        let mut params = Vec::new();
        let mut checks = Vec::new();
        let mut honest = Vec::new();
        let mut names = Vec::new();
        for i in 0..n {
            let k = self.fresh("tk");
            let s = self.fresh("ts");
            externs.push(Extern {
                name: k.clone(),
                ty: "PublicKey".into(),
                json: format!("\"{}\"", self.key()),
            });
            params.push(format!("{s}: Signature"));
            checks.push(format!("{k}.check({s})"));
            honest.push((s.clone(), SatValue::Sig(i < t as usize))); // first t present
            names.push(s);
        }
        // Tamper: flip one present signature off, giving t-1 < t, so it fails.
        let tampers = vec![(
            format!("{t}-1 sigs"),
            vec![(names[0].clone(), SatValue::Sig(false))],
        )];
        Clause {
            externs,
            params,
            text: format!("{} >= {t}", checks.join(" + ")),
            honest,
            tampers,
        }
    }

    fn clause(&mut self, kind: u64) -> Clause {
        match kind % 5 {
            0 => self.c_range(),
            1 => self.c_arith(),
            2 => self.c_hashlock(),
            3 => self.c_threshold(),
            _ => self.c_sig(),
        }
    }
}

struct SpendPlan {
    name: String,
    honest: Vec<(String, SatValue)>,
    tampers: Vec<(String, Vec<(String, SatValue)>)>,
}

struct Gen2 {
    src: String,
    args: String,
    spends: Vec<SpendPlan>,
}

fn gen_stage2(seed: u64) -> Gen2 {
    let mut b = Builder {
        rng: Rng::new(seed),
        ctr: 0,
        key_d: 0,
    };
    let n_spends = b.rng.between(1, 3) as usize;
    let mut all_externs: Vec<Extern> = Vec::new();
    let mut spend_srcs: Vec<String> = Vec::new();
    let mut spends: Vec<SpendPlan> = Vec::new();

    for si in 0..n_spends {
        // Always one signature gate (avoids a theft-open sig-less leaf), plus
        // 0 to 3 further clauses.
        let mut clauses = vec![b.c_sig()];
        let extra = b.rng.below(4);
        for _ in 0..extra {
            let kind = b.rng.next();
            clauses.push(b.clause(kind));
        }

        let mut params = Vec::new();
        let mut texts = Vec::new();
        let mut honest = Vec::new();
        let mut tampers = Vec::new();
        for cl in clauses {
            all_externs.extend(cl.externs);
            params.extend(cl.params);
            texts.push(cl.text);
            honest.extend(cl.honest);
            tampers.extend(cl.tampers);
        }
        let name = format!("s{si}");
        spend_srcs.push(format!(
            "spend {name}({}) {{ require {{ {} }} }}",
            params.join(", "),
            texts.join(", ")
        ));
        spends.push(SpendPlan {
            name,
            honest,
            tampers,
        });
    }

    let extern_src: String = all_externs
        .iter()
        .map(|e| format!("extern const {}: {};\n", e.name, e.ty))
        .collect();
    let args_body: String = all_externs
        .iter()
        .map(|e| format!("\"{}\": {}", e.name, e.json))
        .collect::<Vec<_>>()
        .join(", ");
    let src = format!(
        "contract Fuzz {{\n{extern_src}{}\nkeypath None; }}",
        spend_srcs.join("\n")
    );
    Gen2 {
        src,
        args: format!("{{{args_body}}}"),
        spends,
    }
}

fn check_stage2(seed: u64) -> Result<(), String> {
    let g = gen_stage2(seed);
    let Some(c) = compile(&g.src, &g.args)? else {
        return Err(format!(
            "generated contract failed to compile:\n{}\nargs: {}",
            g.src, g.args
        ));
    };
    for sp in &g.spends {
        let leaf = c
            .leaves
            .iter()
            .find(|l| l.name == sp.name)
            .ok_or_else(|| format!("no leaf `{}`:\n{}", sp.name, g.src))?;
        let honest: Vec<(&str, SatValue)> = sp
            .honest
            .iter()
            .map(|(n, v)| (n.as_str(), v.clone()))
            .collect();
        spend(&c, leaf, &honest, 0xffff_fffe, 0)
            .map_err(|e| format!("honest plan rejected for `{}`: {e}\n{}", sp.name, g.src))?;

        // Each tamper, applied atop the honest plan, must abort.
        for (label, overrides) in &sp.tampers {
            let mut plan = sp.honest.clone();
            for (on, ov) in overrides {
                if let Some(slot) = plan.iter_mut().find(|(n, _)| n == on) {
                    slot.1 = ov.clone();
                }
            }
            let plan_ref: Vec<(&str, SatValue)> =
                plan.iter().map(|(n, v)| (n.as_str(), v.clone())).collect();
            if spend(&c, leaf, &plan_ref, 0xffff_fffe, 0).is_ok() {
                return Err(format!(
                    "tamper `{label}` on `{}` WRONGLY spent:\n{}",
                    sp.name, g.src
                ));
            }
        }
    }
    Ok(())
}

/// The optimizer must be behavior-preserving: for every generated leaf, the
/// optimized form accepts and rejects exactly what the naive form does, on
/// the honest plan and every tamper, and never grows. Lowering is the oracle.
fn check_optimize(seed: u64) -> Result<(), String> {
    let g = gen_stage2(seed);
    let Some(c) = compile(&g.src, &g.args)? else {
        return Ok(()); // a rejected contract has nothing to optimize
    };
    for sp in &g.spends {
        let leaf = c
            .leaves
            .iter()
            .find(|l| l.name == sp.name)
            .ok_or("no leaf")?;
        let opt = optimize(leaf);
        if opt.script.len() > leaf.script.len() {
            return Err(format!("optimize grew `{}`:\n{}", sp.name, g.src));
        }
        let sig = sig_of(&c.info, &leaf.name);

        let mut plans: Vec<Vec<(String, SatValue)>> = vec![sp.honest.clone()];
        for (_label, overrides) in &sp.tampers {
            let mut p = sp.honest.clone();
            for (on, ov) in overrides {
                if let Some(slot) = p.iter_mut().find(|(n, _)| n == on) {
                    slot.1 = ov.clone();
                }
            }
            plans.push(p);
        }

        let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
        let ctx = Context {
            locktime: 0,
            sequence: 0xffff_fffe,
            tx_version: 2,
            verify_sig: &oracle,
        };
        for plan in plans {
            let ns = build_witness(leaf, sig, &c.env, &plan, &MARKER)
                .map_err(|e| format!("naive witness: {e}\n{}", g.src))?;
            let os = build_witness(&opt, sig, &c.env, &plan, &MARKER)
                .map_err(|e| format!("opt witness: {e}\n{}", g.src))?;
            if ns != os {
                return Err(format!(
                    "witness order changed for `{}`:\n{}",
                    sp.name, g.src
                ));
            }
            let n = execute(&leaf.script, &ns, &ctx).is_ok();
            let o = execute(&opt.script, &os, &ctx).is_ok();
            if n != o {
                return Err(format!("naive/opt disagree on `{}`:\n{}", sp.name, g.src));
            }
        }
    }
    Ok(())
}

#[test]
fn stage4_optimizer_preserves_behavior() {
    run("stage4", 2000, 0x0971_0001, check_optimize);
}

/// The optimizer on a comprehension (IF) leaf must stay behavior-preserving:
/// a `sum(... where b => 1) >= t` threshold over a bool array, where the
/// optimizer consumes flags and the running count through balanced IF blocks.
fn check_optimize_if(seed: u64) -> Result<(), String> {
    let mut rng = Rng::new(seed);
    let n = rng.between(2, 12) as usize;
    let t = rng.between(1, n as i64);
    // Both forms equal the count of set flags; count nests IF blocks.
    let agg = if rng.below(2) == 0 {
        "sum(b in flags where b => 1)"
    } else {
        "count(b in flags where b => true)"
    };
    let src = format!(
        "contract Fuzz {{ extern const k: PublicKey;
            spend s(relaxed flags: [Bool; {n}], sig: Signature) {{
                require {{ {agg} >= {t}, k.check(sig) }}
            }} keypath None; }}"
    );
    let args = format!(r#"{{"k": "{KEY}"}}"#);
    let Some(c) = compile(&src, &args)? else {
        return Err(format!("comprehension contract failed to compile:\n{src}"));
    };
    let leaf = c.leaves.iter().find(|l| l.name == "s").ok_or("no leaf s")?;
    let opt = optimize(leaf);
    if opt.script.len() > leaf.script.len() {
        return Err(format!("optimize grew the IF leaf:\n{src}"));
    }
    let sig = sig_of(&c.info, "s");
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    let probe = |true_count: i64, sig_ok: bool, expect: bool| -> Result<(), String> {
        let flags = SatValue::Array(
            (0..n)
                .map(|i| SatValue::Bool((i as i64) < true_count))
                .collect(),
        );
        let plan: Vec<(String, SatValue)> = vec![
            ("flags".into(), flags),
            ("sig".into(), SatValue::Sig(sig_ok)),
        ];
        let ns =
            build_witness(leaf, sig, &c.env, &plan, &MARKER).map_err(|e| format!("naive: {e}"))?;
        let os =
            build_witness(&opt, sig, &c.env, &plan, &MARKER).map_err(|e| format!("opt: {e}"))?;
        if ns != os {
            return Err(format!("witness order changed:\n{src}"));
        }
        let nr = execute(&leaf.script, &ns, &ctx).is_ok();
        let or = execute(&opt.script, &os, &ctx).is_ok();
        if nr != or {
            return Err(format!(
                "naive/opt disagree (count={true_count}, sig={sig_ok}):\n{src}"
            ));
        }
        if nr != expect {
            return Err(format!("wrong result (count={true_count}):\n{src}"));
        }
        Ok(())
    };
    probe(t, true, true)?; // exactly t set, signed -> spends
    probe(t - 1, true, false)?; // one short -> fails
    probe(t, false, false)?; // declined sig -> fails
    Ok(())
}

#[test]
fn stage5_optimizer_preserves_if_leaves() {
    run("stage5", 1500, 0x1f1f_0001, check_optimize_if);
}

/// Dead-constraint elimination: stack always-true clauses on a bounded `x`.
/// The optimizer must drop exactly the dead ones (so the leaf shrinks), keep
/// the real range (so an out-of-range value still fails), and agree with naive.
fn check_optimize_dead(seed: u64) -> Result<(), String> {
    let mut rng = Rng::new(seed);
    let hi = rng.between(2, 1000);
    let n_dead = rng.between(1, 4);
    let mut clauses = vec![format!("x in 0..{hi}")];
    for _ in 0..n_dead {
        // Each clause is always-true given x in [0, hi).
        clauses.push(match rng.below(4) {
            0 => "x >= 0".to_string(),
            1 => format!("x < {}", hi + 1 + rng.below(1000) as i64),
            2 => format!("x <= {}", hi - 1 + rng.below(1000) as i64),
            _ => format!("x + x < {}", 2 * hi + 1 + rng.below(1000) as i64),
        });
    }
    clauses.push("k.check(sig)".to_string());
    let src = format!(
        "contract Fuzz {{ extern const k: PublicKey;
            spend s(relaxed x: Int, sig: Signature) {{ require {{ {} }} }} keypath None; }}",
        clauses.join(", ")
    );
    let args = format!(r#"{{"k": "{KEY}"}}"#);
    let Some(c) = compile(&src, &args)? else {
        return Err(format!("dead-clause contract failed to compile:\n{src}"));
    };
    let leaf = c.leaves.iter().find(|l| l.name == "s").ok_or("no leaf s")?;
    let opt = optimize(leaf);
    if opt.script.len() >= leaf.script.len() {
        return Err(format!(
            "dead-constraint elimination did not shrink:\n{src}"
        ));
    }
    let sig = sig_of(&c.info, "s");
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    let probe = |x: i64, sig_ok: bool, expect: bool| -> Result<(), String> {
        let plan: Vec<(String, SatValue)> = vec![
            ("x".into(), SatValue::Int(x)),
            ("sig".into(), SatValue::Sig(sig_ok)),
        ];
        let ns =
            build_witness(leaf, sig, &c.env, &plan, &MARKER).map_err(|e| format!("naive: {e}"))?;
        let os =
            build_witness(&opt, sig, &c.env, &plan, &MARKER).map_err(|e| format!("opt: {e}"))?;
        if ns != os {
            return Err(format!("witness order changed:\n{src}"));
        }
        let nr = execute(&leaf.script, &ns, &ctx).is_ok();
        let or = execute(&opt.script, &os, &ctx).is_ok();
        if nr != or {
            return Err(format!("naive/opt disagree (x={x}, sig={sig_ok}):\n{src}"));
        }
        if nr != expect {
            return Err(format!("wrong result (x={x}):\n{src}"));
        }
        Ok(())
    };
    probe(hi - 1, true, true)?; // max in range, signed: spends
    probe(0, true, true)?; // min in range
    probe(hi, true, false)?; // out of range: the surviving real range rejects
    probe(hi - 1, false, false)?; // declined sig
    Ok(())
}

#[test]
fn stage6_optimizer_eliminates_dead_constraints() {
    run("stage6", 1500, 0xdead_0001, check_optimize_dead);
}

/// Common-subexpression elimination: two adjacent comparison items share one
/// subject (a `count`/`sum` tally over a bool array). With constant bounds the
/// optimizer computes the tally once and DUPs it (must shrink); with a
/// witness-dependent bound the pick-in-predicate guard makes it decline (the
/// kept copy would shift a depth-based read). Either way the optimized leaf
/// must accept and reject exactly as the naive leaf, on every probe.
fn check_optimize_cse(seed: u64) -> Result<(), String> {
    let mut rng = Rng::new(seed);
    let n = rng.between(2, 10) as usize;
    let subj = if rng.below(2) == 0 {
        "count(b in flags where b => true)"
    } else {
        "sum(b in flags where b => 1)"
    };
    // Accept window [a, z] strictly inside [0, n]: both bounds stay live (a
    // const `>= 0` or `<= n` would be dead-eliminated, leaving one subject).
    let a = rng.between(1, (n - 1) as i64);
    let z = rng.between(a, (n - 1) as i64);
    let witness_bound = rng.below(2) == 0;

    // Constant bounds let CSE fire; witness-param bounds make the predicate
    // read the stack by depth, so the guard must skip the share.
    let (extra_params, lo_t, hi_t, extra_plan): (String, String, String, Vec<(String, SatValue)>) =
        if witness_bound {
            (
                ", relaxed lo: Int, relaxed hi: Int".to_string(),
                "lo".to_string(),
                "hi".to_string(),
                vec![
                    ("lo".into(), SatValue::Int(a)),
                    ("hi".into(), SatValue::Int(z)),
                ],
            )
        } else {
            (String::new(), a.to_string(), z.to_string(), Vec::new())
        };

    let src = format!(
        "contract Fuzz {{ extern const k: PublicKey;
            spend s(relaxed flags: [Bool; {n}]{extra_params}, sig: Signature) {{
                require {{ {subj} >= {lo_t}, {subj} <= {hi_t}, k.check(sig) }}
            }} keypath None; }}"
    );
    let args = format!(r#"{{"k": "{KEY}"}}"#);
    let Some(c) = compile(&src, &args)? else {
        return Err(format!("CSE contract failed to compile:\n{src}"));
    };
    let leaf = c.leaves.iter().find(|l| l.name == "s").ok_or("no leaf s")?;
    let opt = optimize(leaf);
    if opt.script.len() > leaf.script.len() {
        return Err(format!("optimize grew the CSE leaf:\n{src}"));
    }
    if !witness_bound && opt.script.len() >= leaf.script.len() {
        return Err(format!("CSE did not shrink a shared-subject leaf:\n{src}"));
    }
    let sig = sig_of(&c.info, "s");
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    let probe = |true_count: i64, sig_ok: bool, expect: bool| -> Result<(), String> {
        let flags = SatValue::Array(
            (0..n)
                .map(|i| SatValue::Bool((i as i64) < true_count))
                .collect(),
        );
        let mut plan: Vec<(String, SatValue)> = vec![
            ("flags".into(), flags),
            ("sig".into(), SatValue::Sig(sig_ok)),
        ];
        plan.extend(extra_plan.iter().cloned());
        let ns =
            build_witness(leaf, sig, &c.env, &plan, &MARKER).map_err(|e| format!("naive: {e}"))?;
        let os =
            build_witness(&opt, sig, &c.env, &plan, &MARKER).map_err(|e| format!("opt: {e}"))?;
        if ns != os {
            return Err(format!("witness order changed:\n{src}"));
        }
        let nr = execute(&leaf.script, &ns, &ctx).is_ok();
        let or = execute(&opt.script, &os, &ctx).is_ok();
        if nr != or {
            return Err(format!(
                "naive/opt disagree (count={true_count}, sig={sig_ok}):\n{src}"
            ));
        }
        if nr != expect {
            return Err(format!(
                "wrong result (count={true_count}, window [{a},{z}]):\n{src}"
            ));
        }
        Ok(())
    };
    probe(a, true, true)?; // lower edge accepts
    probe(z, true, true)?; // upper edge accepts
    if a > 0 {
        probe(a - 1, true, false)?; // below the window: the kept `>=` rejects
    }
    if z < n as i64 {
        probe(z + 1, true, false)?; // above the window: the kept `<=` rejects
    }
    probe(a, false, false)?; // declined signature
    Ok(())
}

#[test]
fn stage7_optimizer_shares_common_subexpressions() {
    run("stage7", 2000, 0xc5e0_0001, check_optimize_cse);
}

#[test]
fn stage2_multi_constraint_multi_spend() {
    run("stage2", 2000, 0xbee5_0001, check_stage2);
}

// --- Stage 3b: TOTALITY on adversarial input (the compiler must never panic) ---

/// A pool of source tokens to splice into garbage: keywords, punctuation,
/// numbers, and identifiers that exercise the lexer/parser/sema paths.
const TOKENS: &[&str] = &[
    "contract",
    "spend",
    "extern",
    "const",
    "require",
    "keypath",
    "relaxed",
    "select",
    "PublicKey",
    "Signature",
    "Bytes",
    "Hash",
    "Int",
    "Bool",
    "None",
    "check",
    "sha256",
    "mul",
    "div",
    "mod",
    "sum",
    "all",
    "any",
    "in",
    "for",
    "where",
    "{",
    "}",
    "(",
    ")",
    "[",
    "]",
    "<",
    ">",
    ";",
    ",",
    ":",
    ".",
    "+",
    "-",
    "==",
    ">=",
    "<=",
    "..",
    "0",
    "1",
    "16",
    "0x",
    "0xdead",
    "999999999999999999999999",
    "k",
    "x",
    "s",
    "T",
    "\"",
    "P2",
    "@depth",
    "@weight",
    "older_than",
    "after",
    "\n",
    " ",
];

fn gen_garbage(seed: u64) -> String {
    let mut rng = Rng::new(seed);
    let n = rng.between(0, 60) as usize; // tiny, bounded by design
    let mut s = String::new();
    // Half the time, start from the real contract keyword to get deeper.
    if rng.below(2) == 0 {
        s.push_str("contract Fuzz { ");
    }
    for _ in 0..n {
        s.push_str(TOKENS[rng.below(TOKENS.len() as u64) as usize]);
        s.push(' ');
    }
    s
}

fn check_totality(seed: u64) -> Result<(), String> {
    // ANY string must compile-or-reject, never panic, never hang. (The args
    // are well-formed-but-empty; bind_args rejects unknown externs.)
    let _ = compile(&gen_garbage(seed), "{}")?;
    Ok(())
}

#[test]
fn stage3b_totality_on_garbage() {
    run("stage3b", 12000, 0x6a46_0001, check_totality);
}

// --- Stage 3c: MUTATION totality: corrupt a valid source, never panic ---
//
// Near-valid input reaches deeper (sema, intervals, lowering) than pure
// garbage, where a panic is likelier to hide. Mutating a rich Stage-2
// source and keeping its real args lets lightly-broken variants still run
// the whole pipeline.

fn mutate(src: &str, rng: &mut Rng) -> String {
    let mut bytes: Vec<u8> = src.bytes().collect();
    let muts = rng.between(1, 6);
    for _ in 0..muts {
        if bytes.is_empty() {
            break;
        }
        match rng.below(4) {
            0 => {
                let i = rng.below(bytes.len() as u64) as usize;
                bytes.remove(i);
            }
            1 => {
                let i = rng.below(bytes.len() as u64) as usize;
                let b = bytes[i];
                bytes.insert(i, b);
            }
            2 => {
                let i = rng.below(bytes.len() as u64) as usize;
                bytes.truncate(i);
            }
            _ => {
                let i = rng.below(bytes.len() as u64 + 1) as usize;
                let tok = TOKENS[rng.below(TOKENS.len() as u64) as usize];
                for (j, tb) in tok.bytes().enumerate() {
                    bytes.insert(i + j, tb);
                }
            }
        }
    }
    String::from_utf8_lossy(&bytes).into_owned()
}

fn check_mutation(seed: u64) -> Result<(), String> {
    let g = gen_stage2(seed);
    let mut rng = Rng::new(seed ^ 0xdead_beef);
    let mutated = mutate(&g.src, &mut rng);
    // Must compile-or-reject, never panic.
    let _ = compile(&mutated, &g.args)?;
    Ok(())
}

#[test]
fn stage3c_totality_on_mutations() {
    run("stage3c", 6000, 0xf00d_0001, check_mutation);
}

// --- Adversarial stage: malformed / deeply-nested / mutated input; TOTALITY ---
//
// The other stages generate WELL-FORMED contracts; this one attacks the front
// end with garbage, deeply-nested constructs, and byte-mutated templates -- the
// class that produced a real rust-miniscript stack-overflow CVE. The only
// property is TOTALITY: parser, JSON parser, and the whole pipeline must never
// panic or crash on any input.
//
// SAFETY: every generated number is clamped to <= 3 digits (`clamp_numbers`), so
// the fuzzer can never emit a huge array length (`[T; 2e9]`) or huge
// comprehension range -- the compiler has no resource cap today, so an
// unclamped fuzzer could OOM the machine. Nesting depth is bounded to ~600,
// comfortably above the parser/JSON depth guard (64) yet far below any
// stack-overflow threshold, so the depth GUARDS are exercised without risk.

const ADV_TEMPLATE: &str = "contract C { extern const k: PublicKey;\n  spend s(relaxed x: Int, sig: Signature) {\n    require { x in 0..100, x >= 0, k.check(sig) }\n  } keypath None; }";

const ADV_TOKENS: &[&str] = &[
    "contract",
    "spend",
    "require",
    "keypath",
    "extern",
    "const",
    "let",
    "if",
    "else",
    "{",
    "}",
    "(",
    ")",
    "[",
    "]",
    "<",
    ">",
    ",",
    ";",
    ":",
    "=",
    "+",
    "-",
    "*",
    ".",
    "..",
    "..=",
    "=>",
    ">=",
    "<=",
    "==",
    "!=",
    "&&",
    "||",
    "0",
    "1",
    "2",
    "100",
    "x",
    "k",
    "sig",
    "v",
    "w",
    "PublicKey",
    "Int",
    "Bool",
    "Signature",
    "Bytes",
    "Hash",
    "LockTime",
    "Absolute",
    "Relative",
    "sha256",
    "hash160",
    "check",
    "after",
    "min",
    "max",
    "abs",
    "sum",
    "count",
    "all",
    "any",
    "where",
    "select",
    "relaxed",
    "open",
    "None",
    "MuSig2",
    "true",
    "false",
    "\"0x01\"",
    "\"abcd\"",
    "// c\n",
];

/// Keep at most 3 consecutive digits, so no number exceeds 999 -- the safety net
/// that prevents a fuzzed huge array length / range from OOMing the compiler.
fn clamp_numbers(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut run = 0u32;
    for ch in s.chars() {
        if ch.is_ascii_digit() {
            run += 1;
            if run <= 3 {
                out.push(ch);
            }
        } else {
            run = 0;
            out.push(ch);
        }
    }
    out
}

/// Random byte-soup from a contract-flavoured charset (no `[`/`]`: array syntax
/// is covered by the token salad with bounded lengths).
fn adv_soup(rng: &mut Rng) -> String {
    const CS: &[u8] = b"contract spend require keypath extern const let{}()<>,;:=+-*.!&|0123456789 xkvw\"\\\n\t PublicKeyIntBoolSig";
    let n = rng.below(300) + 1;
    (0..n)
        .map(|_| CS[rng.below(CS.len() as u64) as usize] as char)
        .collect()
}

fn adv_tokens(rng: &mut Rng) -> String {
    let n = rng.below(80) + 1;
    (0..n)
        .map(|_| ADV_TOKENS[rng.below(ADV_TOKENS.len() as u64) as usize])
        .collect::<Vec<_>>()
        .join(" ")
}

/// Deeply-nested `open`/`close` (e.g. `((((1))))`) inside a real-ish contract:
/// depth 20..600, well above the parser's depth-64 guard, well below overflow.
fn adv_deep(rng: &mut Rng, open: char, close: char) -> String {
    let d = (rng.below(580) + 20) as usize;
    let mut s = String::from(
        "contract C { extern const k: PublicKey; spend s(relaxed x: Int, sig: Signature) { require { ",
    );
    for _ in 0..d {
        s.push(open);
    }
    s.push('1');
    for _ in 0..d {
        s.push(close);
    }
    s.push_str(" >= 0, k.check(sig) } } keypath None; }");
    s
}

/// Deeply-nested call expression `select(true, select(true, ... , 0), 0)`.
fn adv_deep_select(rng: &mut Rng) -> String {
    let d = (rng.below(580) + 20) as usize;
    let mut e = String::from("x");
    for _ in 0..d {
        e = format!("select(true, {e}, 0)");
    }
    format!(
        "contract C {{ extern const k: PublicKey; spend s(relaxed x: Int, sig: Signature) {{ require {{ {e} >= 0, k.check(sig) }} }} keypath None; }}"
    )
}

fn adv_mutate(rng: &mut Rng) -> String {
    let mut b = ADV_TEMPLATE.as_bytes().to_vec();
    for _ in 0..(rng.below(24) + 1) {
        if b.is_empty() {
            break;
        }
        match rng.below(3) {
            0 => {
                let i = rng.below(b.len() as u64) as usize;
                b.remove(i);
            }
            1 => {
                let i = rng.below(b.len() as u64 + 1) as usize;
                b.insert(i, (rng.below(94) + 32) as u8);
            }
            _ => {
                let i = rng.below(b.len() as u64) as usize;
                b[i] = (rng.below(94) + 32) as u8;
            }
        }
    }
    String::from_utf8_lossy(&b).into_owned()
}

/// Deeply-nested JSON array `[[[...1...]]]`: depth 10..130, above the JSON
/// depth-64 guard, below overflow.
fn adv_deep_json(rng: &mut Rng) -> String {
    let d = (rng.below(120) + 10) as usize;
    let mut s = String::new();
    for _ in 0..d {
        s.push('[');
    }
    s.push('1');
    for _ in 0..d {
        s.push(']');
    }
    s
}

fn gen_adversarial(seed: u64) -> (String, String) {
    let mut rng = Rng::new(seed);
    let src = match rng.below(6) {
        0 => adv_soup(&mut rng),
        1 => adv_tokens(&mut rng),
        2 => adv_deep(&mut rng, '(', ')'),
        3 => adv_deep(&mut rng, '[', ']'),
        4 => adv_deep_select(&mut rng),
        _ => adv_mutate(&mut rng),
    };
    let args = match rng.below(3) {
        0 => adv_deep_json(&mut rng),
        1 => format!(r#"{{"k": "{KEY}"}}"#),
        _ => adv_soup(&mut rng),
    };
    (clamp_numbers(&src), clamp_numbers(&args))
}

/// Totality only: parser, JSON parser, and the full pipeline must not panic or
/// crash on adversarial input (any outcome -- reject or compile -- is fine).
fn check_adversarial(seed: u64) -> Result<(), String> {
    let (src, args) = gen_adversarial(seed);
    let _ = parser::parse_source(&src);
    let _ = json::parse(&args);
    let _ = compile(&src, &args);
    Ok(())
}

#[test]
fn adversarial_totality() {
    run("adversarial", 4000, 0xADADAD01, check_adversarial);
}
