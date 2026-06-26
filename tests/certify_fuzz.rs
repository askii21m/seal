//! Generative certification harness: the certifier (and the optimizer it
//! vouches for) run against thousands of randomized, well-formed contracts --
//! not just the six-example corpus. The aim is BREADTH: surface where the
//! certifier reaches a strong verdict, where it honestly falls back, and -- the
//! point of the whole thing -- whether any strong verdict is ever WRONG.
//!
//! For every generated contract we (1) compile the full pipeline (no panic --
//! TOTALITY at scale), (2) run `certify` exactly as `seal --certify` does, (3)
//! INDEPENDENTLY cross-check each leaf by EXECUTION over its witness domain, and
//! (4) tally the verdict distribution and the optimizer's shrink ratio.
//!
//! The cross-check asserts two properties at every probed witness `w`: T1, that
//! `execute(naive, w)` equals a ground-truth predicate written HERE in the test
//! (not the compiler's `eval_predicate`); and T2, that `execute(naive, w)`
//! equals `execute(optimized, w)`. A divergence inside a domain the certifier
//! claimed to have proven (Certified / Proven / BoundedChecked) is a FALSE
//! VERDICT -- the worst possible bug, the certifier vouching for a wrong
//! compile. A divergence anywhere is a compiler bug regardless of verdict.
//!
//! The ground-truth `eval` closures are authored independently of `src/`, so
//! `execute(script) == eval(assignment)` is a genuine cross-check, not the
//! certifier grading its own homework.
//!
//! Coverage caveat: a leaf whose witness domain fits under `ENUM_CAP` is
//! enumerated EXHAUSTIVELY (every witness executed); a larger domain is randomly
//! SAMPLED (falsification, not a proof -- a divergence in the unsampled region
//! could be missed here, though `Certified` leaves additionally get their
//! claimed `checked` count validated against the true domain size, and the
//! corpus tests in `tests/certify.rs` / `tests/decide_fuzz.rs` cover their
//! domains exhaustively). The telemetry line reports the enumerated/sampled
//! split so the strength of a given run is visible.
//!
//! Everything is SEEDED (the same SplitMix64 the other fuzzers use): a failure
//! prints a reproducing seed. Domains are kept small so a default run is fast
//! and never OOMs; `BASIS_FUZZ=N` scales the seed counts for a nightly hammer.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Mutex;

use seal::analysis::consteval::{Env, bind_args, instantiate};
use seal::analysis::intervals;
use seal::analysis::paths;
use seal::analysis::sema;
use seal::analysis::sema::ContractInfo;
use seal::codegen::lower::{LoweredLeaf, lower};
use seal::codegen::optimize::optimize;
use seal::diagnostics::{Diagnostic, Severity};
use seal::json;
use seal::syntax::ast::Contract;
use seal::syntax::parser;
use seal::verify::certify::{CertStatus, certify};
use seal::verify::interp::{Context, execute};
use seal::verify::satisfy::{SatValue, build_witness};

const MARKER: [u8; 64] = [0xAA; 64];

// --- deterministic PRNG (SplitMix64), identical to the other fuzz binaries ---

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
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
    fn between(&mut self, lo: i64, hi: i64) -> i64 {
        debug_assert!(lo <= hi);
        lo + self.below((hi - lo + 1) as u64) as i64
    }
}

/// A real on-curve x-only key `d*G` (distinct small `d` give distinct keys).
fn nth_key(d: u64) -> String {
    use seal::crypto::secp::{U256, generator};
    let p = generator() * U256([d, 0, 0, 0]);
    let xb = p.x_bytes().expect("a generator multiple is finite");
    let hex: String = xb.iter().map(|b| format!("{b:02x}")).collect();
    format!("0x{hex}")
}

// --- the compile pipeline (graceful: returns the pieces certify needs) ---

struct Compiled {
    contract: Contract,
    info: ContractInfo,
    env: Env,
    naive: Vec<LoweredLeaf>,
}

fn errors(ds: &[Diagnostic]) -> bool {
    ds.iter().any(|d| d.severity == Severity::Error)
}

/// `Ok(Some)` compiled clean; `Ok(None)` rejected (a valid outcome); `Err` is
/// the pipeline producing something internally inconsistent (a real bug).
fn compile(src: &str, args: &str) -> Result<Option<Compiled>, String> {
    let (contract, pd) = parser::parse_source(src);
    if errors(&pd) {
        return Ok(None);
    }
    let Some(c) = contract else { return Ok(None) };
    let (sd, info) = sema::analyze(&c);
    if errors(&sd) {
        return Ok(None);
    }
    let parsed = json::parse(args).map_err(|e| format!("args json: {e:?}"))?;
    let mut env = match bind_args(&info, &parsed) {
        Ok(e) => e,
        Err(_) => return Ok(None),
    };
    if errors(&instantiate(&c, &mut env)) {
        return Ok(None);
    }
    if errors(&seal::analysis::limits::analyze(&c, &info, &env)) {
        return Ok(None);
    }
    let (g1, report) = intervals::analyze(&c, &env);
    if errors(&g1) {
        return Ok(None);
    }
    let (pd2, _) = paths::analyze(&c, &info, &env);
    if errors(&pd2) {
        return Ok(None);
    }
    let (ld, naive) = lower(&c, &info, &env, &report);
    if errors(&ld) {
        return Ok(None);
    }
    Ok(Some(Compiled {
        contract: c,
        info,
        env,
        naive,
    }))
}

// --- the independent ground-truth model -------------------------------------
//
// Each generated clause carries (a) its `.sl` source text, (b) the externs and
// witness params it introduces, (c) the finite candidate values of each param
// for domain enumeration, and (d) an `eval` closure -- the predicate's truth on
// any assignment, written here independently of the compiler. A contract's
// predicate is the AND of its clauses (params are disjoint across clauses).

/// A witness value in the test's own model (maps 1:1 onto `SatValue`).
#[derive(Clone, Debug)]
enum PVal {
    Int(i64),
    Bool(bool),
    Sig(bool),
    Bytes(Vec<u8>),
    Bools(Vec<bool>),
}

fn to_sat(p: &PVal) -> SatValue {
    match p {
        PVal::Int(v) => SatValue::Int(*v),
        PVal::Bool(b) => SatValue::Bool(*b),
        PVal::Sig(b) => SatValue::Sig(*b),
        PVal::Bytes(b) => SatValue::Bytes(b.clone()),
        PVal::Bools(bs) => SatValue::Array(bs.iter().map(|&b| SatValue::Bool(b)).collect()),
    }
}

type Assign = Vec<(String, PVal)>;

fn gi(a: &Assign, n: &str) -> i64 {
    for (k, v) in a {
        if k == n
            && let PVal::Int(x) = v
        {
            return *x;
        }
    }
    panic!("no int param {n}")
}
fn gsig(a: &Assign, n: &str) -> bool {
    for (k, v) in a {
        if k == n
            && let PVal::Sig(b) = v
        {
            return *b;
        }
    }
    panic!("no sig param {n}")
}
fn gbool(a: &Assign, n: &str) -> bool {
    for (k, v) in a {
        if k == n
            && let PVal::Bool(b) = v
        {
            return *b;
        }
    }
    panic!("no bool param {n}")
}
fn gbytes<'x>(a: &'x Assign, n: &str) -> &'x [u8] {
    for (k, v) in a {
        if k == n
            && let PVal::Bytes(b) = v
        {
            return b;
        }
    }
    panic!("no bytes param {n}")
}
fn gbools(a: &Assign, n: &str) -> Vec<bool> {
    for (k, v) in a {
        if k == n
            && let PVal::Bools(bs) = v
        {
            return bs.clone();
        }
    }
    panic!("no bool-array param {n}")
}

/// What kind of finite domain a param spans -- governs whether the certifier's
/// `Certified{checked}` count can be compared to our enumeration size.
#[derive(Clone, Copy, PartialEq)]
enum DomainKind {
    /// Our candidate set IS the complete domain (Bool/Sig/[Bool;n]).
    Exhaustive,
    /// Our candidates are a proper sample of an infinite domain (Int/Bytes).
    Sampled,
}

struct Param {
    name: String,
    /// (witness encoding, model value) candidate pairs for enumeration.
    candidates: Vec<(SatValue, PVal)>,
    kind: DomainKind,
}

struct Clause {
    externs: Vec<(String, String, String)>, // (name, type, json value)
    param_src: Vec<String>,                 // spend-signature fragments
    params: Vec<Param>,
    text: String,   // require-clause source
    honest: Assign, // a satisfying fragment
    eval: Box<dyn Fn(&Assign) -> bool>,
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

    /// Int probe set straddling the clause's key constants, plus tails out to
    /// the CScriptNum 4-byte limit, so a FullInt proof's breakpoints are
    /// stressed. Bounded (~20 values) to keep domain products tractable.
    fn int_probes(consts: &[i64], honest: i64) -> Vec<(SatValue, PVal)> {
        let mut vs: Vec<i64> = vec![
            honest,
            0,
            1,
            -1,
            1000,
            -1000,
            100_000,
            -100_000,
            2_147_483_647,
            -2_147_483_647,
        ];
        for &c in consts {
            for d in -1..=1 {
                if let Some(v) = c.checked_add(d)
                    && v.abs() <= 2_147_483_647
                {
                    vs.push(v);
                }
            }
        }
        vs.sort_unstable();
        vs.dedup();
        vs.into_iter()
            .map(|v| (SatValue::Int(v), PVal::Int(v)))
            .collect()
    }

    /// `k.check(s)` -- a single signature gate.
    fn c_sig(&mut self) -> Clause {
        let k = self.fresh("k");
        let s = self.fresh("sig");
        let sn = s.clone();
        Clause {
            externs: vec![(k.clone(), "PublicKey".into(), format!("\"{}\"", self.key()))],
            param_src: vec![format!("{s}: Signature")],
            params: vec![Param {
                name: s.clone(),
                candidates: vec![
                    (SatValue::Sig(false), PVal::Sig(false)),
                    (SatValue::Sig(true), PVal::Sig(true)),
                ],
                kind: DomainKind::Exhaustive,
            }],
            text: format!("{k}.check({s})"),
            honest: vec![(s.clone(), PVal::Sig(true))],
            eval: Box::new(move |a| gsig(a, &sn)),
        }
    }

    /// `r in lo..hi` -- a half-open range on a relaxed int.
    fn c_range(&mut self) -> Clause {
        let x = self.rng.between(20, 1000);
        let lo = x - self.rng.below(20) as i64;
        let hi = x + 1 + self.rng.below(20) as i64;
        let r = self.fresh("r");
        let rn = r.clone();
        Clause {
            externs: vec![],
            param_src: vec![format!("relaxed {r}: Int")],
            params: vec![Param {
                name: r.clone(),
                candidates: Self::int_probes(&[lo, hi], x),
                kind: DomainKind::Sampled,
            }],
            text: format!("{r} in {lo}..{hi}"),
            honest: vec![(r.clone(), PVal::Int(x))],
            eval: Box::new(move |a| {
                let v = gi(a, &rn);
                lo <= v && v < hi
            }),
        }
    }

    /// `r OP c` -- a single comparison against a constant.
    fn c_cmp(&mut self) -> Clause {
        let c = self.rng.between(0, 1000);
        let op = self.rng.below(6);
        let r = self.fresh("c");
        let rn = r.clone();
        // An honest value that satisfies the chosen operator.
        let honest = match op {
            0 => c + 1, // >=  (use c+1, also satisfies >)
            1 => c,     // <=
            2 => c + 1, // >
            3 => c - 1, // <
            4 => c,     // ==
            _ => c + 7, // !=
        };
        let (sym, f): (&str, fn(i64, i64) -> bool) = match op {
            0 => (">=", |v, c| v >= c),
            1 => ("<=", |v, c| v <= c),
            2 => (">", |v, c| v > c),
            3 => ("<", |v, c| v < c),
            4 => ("==", |v, c| v == c),
            _ => ("!=", |v, c| v != c),
        };
        Clause {
            externs: vec![],
            param_src: vec![format!("relaxed {r}: Int")],
            params: vec![Param {
                name: r.clone(),
                candidates: Self::int_probes(&[c], honest),
                kind: DomainKind::Sampled,
            }],
            text: format!("{r} {sym} {c}"),
            honest: vec![(r.clone(), PVal::Int(honest))],
            eval: Box::new(move |a| f(gi(a, &rn), c)),
        }
    }

    /// A [Bool;n] array param with all 2^n candidates (n small).
    fn bool_array(&mut self, prefix: &str, n: usize) -> Param {
        let mut candidates = Vec::with_capacity(1 << n);
        for mask in 0u32..(1 << n) {
            let bits: Vec<bool> = (0..n).map(|i| (mask >> i) & 1 == 1).collect();
            candidates.push((
                SatValue::Array(bits.iter().map(|&b| SatValue::Bool(b)).collect()),
                PVal::Bools(bits),
            ));
        }
        let _ = prefix;
        Param {
            name: String::new(),
            candidates,
            kind: DomainKind::Exhaustive,
        }
    }

    /// `count(b in flags where b => true) >= t` (or the `sum(.. => 1)` form):
    /// an n-of-m threshold over a bool array. Pure bool/sig -> Certified;
    /// exercises the comprehension lowering and Engine B.
    fn c_bool_threshold(&mut self) -> Clause {
        let n = self.rng.between(2, 8) as usize;
        let t = self.rng.between(1, n as i64);
        let use_sum = self.rng.below(2) == 0;
        let f = self.fresh("flags");
        let agg = if use_sum {
            format!("sum(b in {f} where b => 1)")
        } else {
            format!("count(b in {f} where b => true)")
        };
        let mut p = self.bool_array("flags", n);
        p.name = f.clone();
        let fn_ = f.clone();
        let honest_bits: Vec<bool> = (0..n).map(|i| (i as i64) < t).collect();
        Clause {
            externs: vec![],
            param_src: vec![format!("relaxed {f}: [Bool; {n}]")],
            params: vec![p],
            text: format!("{agg} >= {t}"),
            honest: vec![(f.clone(), PVal::Bools(honest_bits))],
            eval: Box::new(move |a| {
                let bits = gbools(a, &fn_);
                (bits.iter().filter(|&&b| b).count() as i64) >= t
            }),
        }
    }

    /// `S >= a, S <= z` for a shared tally `S` over a bool array: a window whose
    /// two comparisons share one subexpression (the CSE path), and both bounds
    /// stay live (strictly inside [0, n]).
    fn c_bool_window(&mut self) -> Clause {
        let n = self.rng.between(3, 8) as usize;
        let a = self.rng.between(1, (n - 1) as i64);
        let z = self.rng.between(a, (n - 1) as i64);
        let f = self.fresh("win");
        let subj = if self.rng.below(2) == 0 {
            format!("count(b in {f} where b => true)")
        } else {
            format!("sum(b in {f} where b => 1)")
        };
        let mut p = self.bool_array("win", n);
        p.name = f.clone();
        let fn_ = f.clone();
        let honest_bits: Vec<bool> = (0..n).map(|i| (i as i64) < a).collect();
        Clause {
            externs: vec![],
            param_src: vec![format!("relaxed {f}: [Bool; {n}]")],
            params: vec![p],
            text: format!("{subj} >= {a}, {subj} <= {z}"),
            honest: vec![(f.clone(), PVal::Bools(honest_bits))],
            eval: Box::new(move |aa| {
                let c = gbools(aa, &fn_).iter().filter(|&&b| b).count() as i64;
                a <= c && c <= z
            }),
        }
    }

    /// `sha256(p) == h` -- a hashlock; Bytes domain is infinite, so candidates
    /// are {correct preimage, two wrong ones}. Routes to Engine B.
    fn c_hashlock(&mut self) -> Clause {
        let preimage: Vec<u8> = (0..32).map(|_| self.rng.below(256) as u8).collect();
        let digest = seal::crypto::sha256::sha256(&preimage);
        let hhex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
        let wrong1: Vec<u8> = preimage.iter().map(|b| b ^ 0x5a).collect();
        let wrong2: Vec<u8> = preimage.iter().rev().cloned().collect();
        let p = self.fresh("p");
        let h = self.fresh("h");
        let correct = preimage.clone();
        let pn = p.clone();
        Clause {
            externs: vec![(h.clone(), "Bytes<32>".into(), format!("\"0x{hhex}\""))],
            param_src: vec![format!("{p}: Bytes<32>")],
            params: vec![Param {
                name: p.clone(),
                candidates: vec![
                    (
                        SatValue::Bytes(preimage.clone()),
                        PVal::Bytes(preimage.clone()),
                    ),
                    (SatValue::Bytes(wrong1.clone()), PVal::Bytes(wrong1)),
                    (SatValue::Bytes(wrong2.clone()), PVal::Bytes(wrong2)),
                ],
                kind: DomainKind::Sampled,
            }],
            text: format!("sha256({p}) == {h}"),
            honest: vec![(p.clone(), PVal::Bytes(preimage))],
            eval: Box::new(move |a| gbytes(a, &pn) == correct.as_slice()),
        }
    }

    /// `select(c, then: x, else: y) >= t`: a conditional with a witness bool
    /// condition and two witness-Int branches. Exercises the select/IF-ELSE
    /// lowering and the certifier's `Select` node. Ground truth is
    /// `(c ? x : y) >= t`.
    fn c_select(&mut self) -> Clause {
        let t = self.rng.between(0, 500);
        let c = self.fresh("sc");
        let x = self.fresh("sx");
        let y = self.fresh("sy");
        let (cn, xn, yn) = (c.clone(), x.clone(), y.clone());
        Clause {
            externs: vec![],
            param_src: vec![
                format!("relaxed {c}: Bool"),
                format!("relaxed {x}: Int"),
                format!("relaxed {y}: Int"),
            ],
            params: vec![
                Param {
                    name: c.clone(),
                    candidates: vec![
                        (SatValue::Bool(false), PVal::Bool(false)),
                        (SatValue::Bool(true), PVal::Bool(true)),
                    ],
                    kind: DomainKind::Exhaustive,
                },
                Param {
                    name: x.clone(),
                    candidates: Self::int_probes(&[t], t + 3),
                    kind: DomainKind::Sampled,
                },
                Param {
                    name: y.clone(),
                    candidates: Self::int_probes(&[t], t - 3),
                    kind: DomainKind::Sampled,
                },
            ],
            text: format!("select({c}, then: {x}, else: {y}) >= {t}"),
            // honest: c=true, x just above t.
            honest: vec![
                (c, PVal::Bool(true)),
                (x, PVal::Int(t + 3)),
                (y, PVal::Int(0)),
            ],
            eval: Box::new(move |a| {
                let branch = if gbool(a, &cn) {
                    gi(a, &xn)
                } else {
                    gi(a, &yn)
                };
                branch >= t
            }),
        }
    }

    /// `a in lo1..hi1, b in lo2..hi2` -- TWO independent ranges on two relaxed
    /// ints in ONE clause, so a spend carrying it (plus the sig gate) is a
    /// DECOUPLED 2-Int leaf that Engine A2's grid proves. The only coupling source
    /// would be a cross-axis atom, which this never emits, so it stays a grid.
    fn c_two_decoupled(&mut self) -> Clause {
        let xa = self.rng.between(20, 800);
        let loa = xa - self.rng.below(15) as i64;
        let hia = xa + 1 + self.rng.below(15) as i64;
        let xb = self.rng.between(20, 800);
        let lob = xb - self.rng.below(15) as i64;
        let hib = xb + 1 + self.rng.below(15) as i64;
        let a = self.fresh("da");
        let b = self.fresh("db");
        let (an, bn) = (a.clone(), b.clone());
        Clause {
            externs: vec![],
            param_src: vec![format!("relaxed {a}: Int"), format!("relaxed {b}: Int")],
            params: vec![
                Param {
                    name: a.clone(),
                    candidates: Self::int_probes(&[loa, hia], xa),
                    kind: DomainKind::Sampled,
                },
                Param {
                    name: b.clone(),
                    candidates: Self::int_probes(&[lob, hib], xb),
                    kind: DomainKind::Sampled,
                },
            ],
            text: format!("{a} in {loa}..{hia}, {b} in {lob}..{hib}"),
            honest: vec![(a.clone(), PVal::Int(xa)), (b.clone(), PVal::Int(xb))],
            eval: Box::new(move |asn| {
                let va = gi(asn, &an);
                let vb = gi(asn, &bn);
                loa <= va && va < hia && lob <= vb && vb < hib
            }),
        }
    }

    /// `a in la..ha, b in lb..hb, select(b > m, then: b, else: v) >= thr` -- a
    /// DECOUPLED 2-Int leaf with a BRANCH (OP_IF) on the b-axis (Phase 3). Both
    /// ints carry a range, so each is `num`'d regardless of the branch (no
    /// dead-axis out-of-M abstain); engine_an proves it through the branch.
    fn c_select_bounded(&mut self) -> Clause {
        let xa = self.rng.between(20, 500);
        let loa = xa - self.rng.below(15) as i64;
        let hia = xa + 1 + self.rng.below(15) as i64;
        let lob = self.rng.between(0, 50);
        let hib = lob + self.rng.between(40, 100);
        let m = self.rng.between(lob + 5, hib - 5); // guard threshold inside b's range
        let v = self.rng.between(0, 30); // else constant
        let thr = self.rng.between(0, m); // >= threshold (<= m so the honest b=m+1 satisfies)
        let a = self.fresh("qa");
        let b = self.fresh("qb");
        let (an, bn) = (a.clone(), b.clone());
        Clause {
            externs: vec![],
            param_src: vec![format!("relaxed {a}: Int"), format!("relaxed {b}: Int")],
            params: vec![
                Param {
                    name: a.clone(),
                    candidates: Self::int_probes(&[loa, hia], xa),
                    kind: DomainKind::Sampled,
                },
                Param {
                    name: b.clone(),
                    candidates: Self::int_probes(&[lob, hib, m, thr], m + 1),
                    kind: DomainKind::Sampled,
                },
            ],
            text: format!(
                "{a} in {loa}..{hia}, {b} in {lob}..{hib}, select({b} > {m}, then: {b}, else: {v}) >= {thr}"
            ),
            honest: vec![(a.clone(), PVal::Int(xa)), (b.clone(), PVal::Int(m + 1))],
            eval: Box::new(move |asn| {
                let va = gi(asn, &an);
                let vb = gi(asn, &bn);
                let sel = if vb > m { vb } else { v };
                loa <= va && va < hia && lob <= vb && vb < hib && sel >= thr
            }),
        }
    }

    fn clause(&mut self, kind: u64) -> Clause {
        match kind % 8 {
            0 => self.c_range(),
            1 => self.c_cmp(),
            2 => self.c_bool_threshold(),
            3 => self.c_bool_window(),
            4 => self.c_select(),
            5 => self.c_two_decoupled(),
            6 => self.c_select_bounded(),
            _ => self.c_hashlock(),
        }
    }
}

struct SpendGen {
    name: String,
    clauses: Vec<Clause>,
    /// Absolute-height timelock threshold (`after(...)`), if the spend has one.
    min_locktime: Option<u32>,
}

struct Gen {
    src: String,
    args: String,
    spends: Vec<SpendGen>,
}

/// 1..=3 spends, each a `sig` gate plus 0..3 further clauses. Multiple spends
/// assemble into a multi-leaf taproot tree, exercising the certifier and
/// optimizer per leaf across a tree; diversity comes from many seeds. Fresh
/// names are globally unique (the Builder counter), so externs and params never
/// collide across spends.
fn gen_contract(seed: u64) -> Gen {
    let mut b = Builder {
        rng: Rng::new(seed),
        ctr: 0,
        key_d: 0,
    };
    let n_spends = 1 + b.rng.below(3) as usize; // 1..=3
    let mut spends: Vec<SpendGen> = Vec::new();
    let mut externs: Vec<(String, String, String)> = Vec::new();
    let mut spend_srcs: Vec<String> = Vec::new();
    for si in 0..n_spends {
        let mut clauses = vec![b.c_sig()];
        let extra = b.rng.below(4);
        for _ in 0..extra {
            let kind = b.rng.next();
            clauses.push(b.clause(kind));
        }
        let mut param_src: Vec<String> = Vec::new();
        let mut texts: Vec<String> = Vec::new();
        for cl in &clauses {
            externs.extend(cl.externs.iter().cloned());
            param_src.extend(cl.param_src.iter().cloned());
            texts.push(cl.text.clone());
        }
        // ~1/3 of spends carry an absolute-height timelock (CLTV); the height
        // stays well below 500,000,000 so it shares the block-height domain.
        let min_locktime = if b.rng.below(3) == 0 {
            let h = b.rng.between(1, 400_000) as u32;
            texts.insert(0, format!("after(LockTime.Absolute(height: {h}))"));
            Some(h)
        } else {
            None
        };
        let name = format!("s{si}");
        spend_srcs.push(format!(
            "spend {name}({}) {{ require {{ {} }} }}",
            param_src.join(", "),
            texts.join(", ")
        ));
        spends.push(SpendGen {
            name,
            clauses,
            min_locktime,
        });
    }
    let extern_src: String = externs
        .iter()
        .map(|(n, t, _)| format!("extern const {n}: {t};\n"))
        .collect();
    let args_body: String = externs
        .iter()
        .map(|(n, _, j)| format!("\"{n}\": {j}"))
        .collect::<Vec<_>>()
        .join(", ");
    let src = format!(
        "contract Fuzz {{\n{extern_src}{}\nkeypath None; }}",
        spend_srcs.join("\n")
    );
    Gen {
        src,
        args: format!("{{{args_body}}}"),
        spends,
    }
}

// --- verdict + optimizer telemetry ------------------------------------------

#[derive(Default)]
struct Stats {
    contracts: u64,
    rejected: u64,
    leaves: u64,
    certified: u64,
    proven_int: u64,
    /// Of `proven_int`, the multi-variable (>=2, decoupled-grid, Engine A_n)
    /// proofs -- a `var` with a comma (e.g. "a,b" or "a,b,c").
    proven_int2: u64,
    proven_sym: u64,
    t2only: u64,
    bounded: u64,
    differential: u64,
    unbounded: u64,
    failed: u64,
    fully_enumerated: u64,
    sampled: u64,
    naive_bytes: u64,
    opt_bytes: u64,
    shrunk_leaves: u64,
}

static STATS: Mutex<Option<Stats>> = Mutex::new(None);

fn record<F: FnOnce(&mut Stats)>(f: F) {
    let mut g = STATS.lock().unwrap();
    f(g.get_or_insert_with(Stats::default));
}

// --- the cross-check --------------------------------------------------------

const ENUM_CAP: usize = 4096;
const SAMPLE: usize = 512;

fn mixed_radix(radix: &[usize], mut n: usize) -> Vec<usize> {
    radix
        .iter()
        .map(|&r| {
            let d = n % r;
            n /= r;
            d
        })
        .collect()
}

/// Independently validate one leaf by executing the real naive and optimized
/// scripts over the witness domain and comparing to the ground-truth predicate.
fn validate(
    g: &Gen,
    spend: &SpendGen,
    c: &Compiled,
    status: &CertStatus,
    stats_buf: &mut Stats,
) -> Result<(), String> {
    let naive = c
        .naive
        .iter()
        .find(|l| l.name == spend.name)
        .ok_or("no leaf")?;
    let opt = optimize(naive);

    // Verdict-independent invariant: the optimizer never grows a leaf.
    if opt.script.len() > naive.script.len() {
        return Err(format!(
            "optimizer GREW the leaf ({} -> {}):\n{}",
            naive.script.len(),
            opt.script.len(),
            g.src
        ));
    }
    stats_buf.naive_bytes += naive.script.len() as u64;
    stats_buf.opt_bytes += opt.script.len() as u64;
    if opt.script.len() < naive.script.len() {
        stats_buf.shrunk_leaves += 1;
    }

    // A Failed verdict on a clean compile is always a P0: the certifier found a
    // three-way divergence the pipeline should never have produced.
    if let CertStatus::Failed { detail } = status {
        return Err(format!(
            "certify FAILED on a clean compile - {detail}:\n{}",
            g.src
        ));
    }

    let sig = c
        .info
        .spends
        .iter()
        .find(|x| x.name == spend.name)
        .ok_or("no sig")?;
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    // Timelock cross-check: a spend's `after(LockTime.Absolute(height: H))`
    // lowers to CLTV (active because nSequence is non-final). Vary nLockTime
    // around the threshold; ground truth ANDs `locktime >= min_lt` onto the
    // witness-clause predicate. No timelock => a single nLockTime of 0.
    let min_lt = spend.min_locktime.unwrap_or(0);
    let locktimes: Vec<u32> = match spend.min_locktime {
        None => vec![0],
        Some(h) => vec![0, h.saturating_sub(1), h, h.saturating_add(1)],
    };

    // Collect the flat param list across all clauses (params are disjoint).
    let params: Vec<&Param> = spend
        .clauses
        .iter()
        .flat_map(|cl| cl.params.iter())
        .collect();
    let radix: Vec<usize> = params.iter().map(|p| p.candidates.len()).collect();
    let total: u128 = radix
        .iter()
        .fold(1u128, |acc, &r| acc.saturating_mul(r as u128));

    // Whether our candidate domain is the COMPLETE finite domain (so its size
    // can be checked against a Certified{checked} claim): every param exhaustive.
    let exhaustive_domain = params.iter().all(|p| p.kind == DomainKind::Exhaustive);

    let (full, points): (bool, usize) = if total <= ENUM_CAP as u128 {
        (true, total as usize)
    } else {
        (false, SAMPLE)
    };
    if full {
        stats_buf.fully_enumerated += 1;
    } else {
        stats_buf.sampled += 1;
    }

    // If the certifier claims exhaustive finite coverage and we hold the true
    // finite domain, its count must equal the domain size.
    if let CertStatus::Certified { checked } = status
        && exhaustive_domain
        && full
        && *checked as u128 != total
    {
        return Err(format!(
            "Certified count {checked} != true domain size {total}:\n{}",
            g.src
        ));
    }

    let strong = matches!(
        status,
        CertStatus::Certified { .. }
            | CertStatus::BoundedChecked { .. }
            | CertStatus::Proven { .. }
    );

    let mut rng = Rng::new(0x5ce0_face ^ g.src.len() as u64);
    for i in 0..points {
        let idx = if full {
            mixed_radix(&radix, i)
        } else {
            radix
                .iter()
                .map(|&r| rng.below(r as u64) as usize)
                .collect()
        };
        let mut plan: Vec<(String, SatValue)> = Vec::with_capacity(params.len());
        let mut assign: Assign = Vec::with_capacity(params.len());
        for (p, &ci) in params.iter().zip(&idx) {
            let (sv, pv) = &p.candidates[ci];
            plan.push((p.name.clone(), sv.clone()));
            assign.push((p.name.clone(), pv.clone()));
        }

        let witness_truth = spend.clauses.iter().all(|cl| (cl.eval)(&assign));

        let nw = build_witness(naive, sig, &c.env, &plan, &MARKER)
            .map_err(|e| format!("naive witness: {e}\n{}", g.src))?;
        let ow = build_witness(&opt, sig, &c.env, &plan, &MARKER)
            .map_err(|e| format!("opt witness: {e}\n{}", g.src))?;
        if nw != ow {
            return Err(format!("witness order diverged:\n{}", g.src));
        }
        for &lt in &locktimes {
            let truth = witness_truth && lt >= min_lt;
            let ctx = Context {
                locktime: lt,
                sequence: 0xffff_fffe,
                tx_version: 2,
                verify_sig: &oracle,
            };
            let nr = execute(&naive.script, &nw, &ctx).is_ok();
            let or = execute(&opt.script, &ow, &ctx).is_ok();

            // T2 (optimizer == naive) -- always required.
            if nr != or {
                return Err(format!(
                    "naive/opt DISAGREE (assign {assign:?}, locktime {lt}, verdict {status:?}):\n{}",
                    g.src
                ));
            }
            // T1 (naive == ground-truth predicate) -- always required.
            if nr != truth {
                let band = if strong {
                    "FALSE VERDICT"
                } else {
                    "compiler bug"
                };
                return Err(format!(
                    "{band}: naive script={nr} but ground-truth={truth} (assign {assign:?}, locktime {lt}, verdict {status:?}):\n{}",
                    g.src
                ));
            }
        }
    }

    // The honest plan must always spend (and must agree with our model).
    let mut honest_plan: Vec<(String, SatValue)> = Vec::new();
    let mut honest_assign: Assign = Vec::new();
    for cl in &spend.clauses {
        for (n, pv) in &cl.honest {
            honest_plan.push((n.clone(), to_sat(pv)));
            honest_assign.push((n.clone(), pv.clone()));
        }
    }
    if !spend.clauses.iter().all(|cl| (cl.eval)(&honest_assign)) {
        return Err(format!(
            "generator BUG: honest assignment fails our own model:\n{}",
            g.src
        ));
    }
    let hw = build_witness(naive, sig, &c.env, &honest_plan, &MARKER)
        .map_err(|e| format!("honest witness: {e}\n{}", g.src))?;
    // An nLockTime at the threshold satisfies the timelock (CLTV is `>=`).
    let honest_ctx = Context {
        locktime: min_lt,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    if execute(&naive.script, &hw, &honest_ctx).is_err() {
        return Err(format!("honest plan REJECTED by naive script:\n{}", g.src));
    }
    Ok(())
}

fn classify(status: &CertStatus, s: &mut Stats) {
    use seal::verify::certify::ProvenKind;
    match status {
        CertStatus::Certified { .. } => s.certified += 1,
        CertStatus::BoundedChecked { .. } => s.bounded += 1,
        CertStatus::Differential { .. } => s.differential += 1,
        CertStatus::Unbounded { .. } => s.unbounded += 1,
        CertStatus::Failed { .. } => s.failed += 1,
        CertStatus::Proven { kind } => match kind {
            ProvenKind::FullInt { var, .. } => {
                s.proven_int += 1;
                // A multi-var (>=2) verdict joins the names with a comma (A_n).
                if var.contains(',') {
                    s.proven_int2 += 1;
                }
            }
            ProvenKind::FullSymbolic { .. } => s.proven_sym += 1,
            ProvenKind::T2OnlySymbolic { .. } => s.t2only += 1,
        },
    }
}

fn check(seed: u64) -> Result<(), String> {
    let g = gen_contract(seed);
    let compiled = compile(&g.src, &g.args)?;
    let Some(c) = compiled else {
        record(|s| {
            s.contracts += 1;
            s.rejected += 1;
        });
        // A clause-built contract should always compile; a rejection is a
        // generator defect worth surfacing, not a silent skip.
        return Err(format!(
            "clause-built contract was REJECTED:\n{}\nargs: {}",
            g.src, g.args
        ));
    };

    let opt: Vec<LoweredLeaf> = c.naive.iter().map(optimize).collect();
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    let reports = certify(&c.contract, &c.info, &c.env, &c.naive, &opt, &MARKER, &ctx);

    let mut local = Stats::default();
    local.contracts += 1;
    for r in &reports {
        local.leaves += 1;
        classify(&r.status, &mut local);
    }
    // Cross-check EVERY generated leaf (the contract is a multi-leaf tree).
    let mut result = Ok(());
    for spend in &g.spends {
        match reports.iter().find(|r| r.name == spend.name) {
            Some(r) => {
                if let Err(e) = validate(&g, spend, &c, &r.status, &mut local) {
                    result = Err(e);
                    break;
                }
            }
            None => {
                result = Err(format!(
                    "no certify report for leaf `{}`:\n{}",
                    spend.name, g.src
                ));
                break;
            }
        }
    }

    // Fold local telemetry into the shared accumulator regardless of outcome.
    record(|s| {
        s.contracts += local.contracts;
        s.leaves += local.leaves;
        s.certified += local.certified;
        s.proven_int += local.proven_int;
        s.proven_int2 += local.proven_int2;
        s.proven_sym += local.proven_sym;
        s.t2only += local.t2only;
        s.bounded += local.bounded;
        s.differential += local.differential;
        s.unbounded += local.unbounded;
        s.failed += local.failed;
        s.fully_enumerated += local.fully_enumerated;
        s.sampled += local.sampled;
        s.naive_bytes += local.naive_bytes;
        s.opt_bytes += local.opt_bytes;
        s.shrunk_leaves += local.shrunk_leaves;
    });
    result
}

fn scale() -> u64 {
    std::env::var("BASIS_FUZZ")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(1)
}

#[test]
fn certify_fuzz_distribution_and_soundness() {
    // Each contract is a 1..=3-leaf tree, each leaf cross-checked over its
    // (sampled) witness domain -- far heavier than a plain fuzz seed. 70 keeps
    // the default run under a minute yet hits every verdict class; CI scales it
    // up via `BASIS_FUZZ`.
    let n = 70u64.saturating_mul(scale());
    let base = 0xce47_0001u64;
    for i in 0..n {
        let seed = base.wrapping_add(i);
        match catch_unwind(AssertUnwindSafe(|| check(seed))) {
            Ok(Ok(())) => {}
            Ok(Err(msg)) => panic!("[certify_fuzz] seed {seed} FAILED:\n{msg}"),
            Err(_) => panic!("[certify_fuzz] seed {seed} PANICKED the compiler"),
        }
    }

    let s = STATS.lock().unwrap().take().unwrap_or_default();
    let shrink = if s.naive_bytes > 0 {
        100.0 * (s.naive_bytes - s.opt_bytes) as f64 / s.naive_bytes as f64
    } else {
        0.0
    };
    // Telemetry (visible with `--nocapture`): where the certifier lands and how
    // much the optimizer saves across diverse contracts.
    eprintln!(
        "\n=== certify_fuzz: {} contracts, {} leaves ===\n\
         verdicts: Certified={} Proven(Int)={} [of which multi-var(>=2)={}] Proven(Sym)={} T2Only={} Bounded={} Differential={} Unbounded={} Failed={}\n\
         cross-check: {} leaves fully enumerated, {} sampled\n\
         optimizer: {} -> {} bytes ({:.1}% smaller), {} of {} leaves shrank\n",
        s.contracts,
        s.leaves,
        s.certified,
        s.proven_int,
        s.proven_int2,
        s.proven_sym,
        s.t2only,
        s.bounded,
        s.differential,
        s.unbounded,
        s.failed,
        s.fully_enumerated,
        s.sampled,
        s.naive_bytes,
        s.opt_bytes,
        shrink,
        s.shrunk_leaves,
        s.leaves,
    );

    // The harness has teeth as a regression guard: a refactor that silently
    // collapsed the certifier to a single weak verdict would trip these.
    assert_eq!(s.failed, 0, "a clean compile produced a Failed verdict");
    assert!(
        s.certified > 0,
        "no Certified leaves -- finite-domain path regressed"
    );
    assert!(s.proven_int > 0, "no Proven(FullInt) -- Engine A regressed");
    assert!(
        s.proven_int2 > 0,
        "no multi-var Proven(FullInt) -- Engine A_n (decoupled grid) regressed or the \
         generator stopped producing decoupled multi-Int leaves"
    );
    assert!(
        s.proven_sym > 0,
        "no Proven(FullSymbolic) -- Engine B regressed"
    );
}

// --- Engine B mixed Int x structural (Phase 4) deterministic teeth ----------
//
// The exhaustive gate cannot enumerate a Bytes/hash domain, so these tests are
// the soundness teeth for the composed case: a known mixed leaf proves over BOTH
// parts and brute-forces clean (with the real preimage), and a planted divergence
// inside either part is never certified Proven.

fn mixed_src(bidhi: i64, hhex: &str, key: &str) -> (String, String) {
    let src = format!(
        "contract M {{ extern const k: PublicKey; extern const h: Bytes<32>;
            spend f(relaxed bid: Int, p: Bytes<32>, s: Signature) {{
                require {{ bid in 0..{bidhi}, sha256(p) == h, k.check(s) }}
            }} keypath None; }}"
    );
    let args = format!(r#"{{"k": "{key}", "h": "0x{hhex}"}}"#);
    (src, args)
}

/// A mixed leaf (a bounded Int range ANDed with a hashlock) certifies
/// `Proven(FullSymbolic)` -- BOTH the affine-Int part and the structural hash part
/// proven over their complete domains -- and the real naive/opt scripts agree with
/// the ground-truth predicate at every (bid, preimage, sig) probe.
#[test]
fn mixed_int_hashlock_certifies_full_and_brute_forces_clean() {
    use seal::verify::certify::{CertStatus, ProvenKind};
    let preimage: Vec<u8> = (0..32).map(|i| (i * 7 + 1) as u8).collect();
    let digest = seal::crypto::sha256::sha256(&preimage);
    let hhex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
    let key = nth_key(1);
    let (src, args) = mixed_src(100, &hhex, &key);
    let c = compile(&src, &args)
        .expect("compile")
        .expect("not rejected");
    let opt: Vec<LoweredLeaf> = c.naive.iter().map(optimize).collect();
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    let reports =
        seal::verify::certify::certify(&c.contract, &c.info, &c.env, &c.naive, &opt, &MARKER, &ctx);
    let r = reports.iter().find(|r| r.name == "f").unwrap();
    match &r.status {
        CertStatus::Proven {
            kind: ProvenKind::FullSymbolic { .. },
        } => {}
        other => {
            panic!("expected Proven(FullSymbolic) for a bounded-Int + hashlock leaf, got {other:?}")
        }
    }

    // Brute-force: bid in [-5, 105], p in {correct, two wrong}, sig in {0,1}.
    let naive = c.naive.iter().find(|l| l.name == "f").unwrap();
    let optl = opt.iter().find(|l| l.name == "f").unwrap();
    let sig = c.info.spends.iter().find(|x| x.name == "f").unwrap();
    let wrong1: Vec<u8> = preimage.iter().map(|b| b ^ 0x5a).collect();
    let wrong2: Vec<u8> = (0..32).map(|i| (i * 3) as u8).collect();
    let preimages = [preimage.clone(), wrong1, wrong2];
    for bid in -5i64..=105 {
        for pre in &preimages {
            for &sg in &[false, true] {
                let plan = vec![
                    ("bid".to_string(), SatValue::Int(bid)),
                    ("p".to_string(), SatValue::Bytes(pre.clone())),
                    ("s".to_string(), SatValue::Sig(sg)),
                ];
                let nw = build_witness(naive, sig, &c.env, &plan, &MARKER).unwrap();
                let ow = build_witness(optl, sig, &c.env, &plan, &MARKER).unwrap();
                let nr = execute(&naive.script, &nw, &ctx).is_ok();
                let or = execute(&optl.script, &ow, &ctx).is_ok();
                let truth = (0..100).contains(&bid)
                    && seal::crypto::sha256::sha256(pre) == digest.as_slice()
                    && sg;
                assert_eq!(nr, or, "naive/opt disagree at bid={bid} sig={sg}");
                assert_eq!(
                    nr, truth,
                    "FALSE PROOF: naive={nr} truth={truth} at bid={bid} sig={sg}"
                );
            }
        }
    }
}

/// A `count` threshold ANDed with a bounded Int range proves FullSymbolic via
/// Engine B (Phase 4 + count support in pred_to_sym): the count's OP_IF chain
/// matches the predicate's `Select` chain, and the bounded range makes the Int
/// sound. Brute-forced over all 2^5 flag assignments x Int probes x sig.
#[test]
fn count_threshold_plus_int_certifies_full_and_brute_forces_clean() {
    use seal::verify::certify::{CertStatus, ProvenKind};
    let key = nth_key(1);
    let src = "contract CT { extern const k: PublicKey;
        spend f(relaxed flags: [Bool; 5], relaxed r: Int, s: Signature) {
            require { count(b in flags where b => true) >= 2, r in 0..50, k.check(s) }
        } keypath None; }";
    let args = format!(r#"{{"k": "{key}"}}"#);
    let c = compile(src, &args).expect("compile").expect("not rejected");
    let opt: Vec<LoweredLeaf> = c.naive.iter().map(optimize).collect();
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    let reports =
        seal::verify::certify::certify(&c.contract, &c.info, &c.env, &c.naive, &opt, &MARKER, &ctx);
    let r = reports.iter().find(|r| r.name == "f").unwrap();
    match &r.status {
        CertStatus::Proven {
            kind: ProvenKind::FullSymbolic { .. },
        } => {}
        other => panic!("expected FullSymbolic for count + bounded Int, got {other:?}"),
    }
    let naive = c.naive.iter().find(|l| l.name == "f").unwrap();
    let optl = opt.iter().find(|l| l.name == "f").unwrap();
    let sig = c.info.spends.iter().find(|x| x.name == "f").unwrap();
    for mask in 0u32..32 {
        let bits: Vec<bool> = (0..5).map(|i| (mask >> i) & 1 == 1).collect();
        let cnt = bits.iter().filter(|&&b| b).count() as i64;
        for rr in -3i64..=53 {
            for &sg in &[false, true] {
                let plan = vec![
                    (
                        "flags".to_string(),
                        SatValue::Array(bits.iter().map(|&b| SatValue::Bool(b)).collect()),
                    ),
                    ("r".to_string(), SatValue::Int(rr)),
                    ("s".to_string(), SatValue::Sig(sg)),
                ];
                let nw = build_witness(naive, sig, &c.env, &plan, &MARKER).unwrap();
                let ow = build_witness(optl, sig, &c.env, &plan, &MARKER).unwrap();
                let nr = execute(&naive.script, &nw, &ctx).is_ok();
                let or = execute(&optl.script, &ow, &ctx).is_ok();
                let truth = cnt >= 2 && (0..50).contains(&rr) && sg;
                assert_eq!(nr, or, "naive/opt disagree mask={mask} r={rr} sig={sg}");
                assert_eq!(
                    nr, truth,
                    "FALSE PROOF count: naive={nr} truth={truth} mask={mask} r={rr} sig={sg}"
                );
            }
        }
    }
}

/// `fold` lowering coverage (audit finding): the fold aggregator was implemented
/// but had no execution test. A bool-array fold has a finite domain, so certify
/// enumerates it exhaustively; this also brute-forces lowering->execution against
/// ground truth over all 2^6 flag masks x sig, validating the fold OP_NIP
/// accumulator pattern end-to-end.
#[test]
fn fold_lowers_and_brute_forces_clean() {
    use seal::verify::certify::CertStatus;
    let key = nth_key(1);
    let src = "contract FD { extern const k: PublicKey;
        spend f(relaxed flags: [Bool; 6], s: Signature) {
            require { fold(acc = 0, b in flags => acc + select(b, then: 1, else: 0)) >= 3, k.check(s) }
        } keypath None; }";
    let args = format!(r#"{{"k": "{key}"}}"#);
    let c = compile(src, &args).expect("compile").expect("not rejected");
    let opt: Vec<LoweredLeaf> = c.naive.iter().map(optimize).collect();
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    let reports =
        seal::verify::certify::certify(&c.contract, &c.info, &c.env, &c.naive, &opt, &MARKER, &ctx);
    let r = reports.iter().find(|r| r.name == "f").unwrap();
    assert!(
        !matches!(r.status, CertStatus::Failed { .. }),
        "fold leaf must not be Failed: {:?}",
        r.status
    );
    let naive = c.naive.iter().find(|l| l.name == "f").unwrap();
    let optl = opt.iter().find(|l| l.name == "f").unwrap();
    let sig = c.info.spends.iter().find(|x| x.name == "f").unwrap();
    for mask in 0u32..64 {
        let bits: Vec<bool> = (0..6).map(|i| (mask >> i) & 1 == 1).collect();
        let cnt = bits.iter().filter(|&&b| b).count() as i64;
        for &sg in &[false, true] {
            let plan = vec![
                (
                    "flags".to_string(),
                    SatValue::Array(bits.iter().map(|&b| SatValue::Bool(b)).collect()),
                ),
                ("s".to_string(), SatValue::Sig(sg)),
            ];
            let nw = build_witness(naive, sig, &c.env, &plan, &MARKER).unwrap();
            let ow = build_witness(optl, sig, &c.env, &plan, &MARKER).unwrap();
            let nr = execute(&naive.script, &nw, &ctx).is_ok();
            let or = execute(&optl.script, &ow, &ctx).is_ok();
            let truth = cnt >= 3 && sg;
            assert_eq!(nr, or, "fold naive/opt disagree mask={mask} sig={sg}");
            assert_eq!(
                nr, truth,
                "fold FALSE: naive={nr} truth={truth} mask={mask} sig={sg}"
            );
        }
    }
}

/// Phase 5: the enumeration cap is RETIRED where the procedure subsumes it. A
/// finite witness domain that exceeds DEFAULT_DOMAIN_CAP (2^20) no longer forces
/// `Unbounded`; the symbolic procedure (Engine B) proves it over the FULL domain.
/// A `[Bool; 21]` threshold is 2^21 combos (> 2^20): `param_domain` declines
/// before building it (no OOM), so `certify_leaf` routes to the decide upgrade,
/// which proves `FullSymbolic`. (The procedure stays strictly ADDITIVE -- for
/// domains UNDER the cap, the exhaustive enumeration remains the bedrock and
/// decide only upgrades; this test pins the OVER-cap subsumption.)
#[test]
fn over_cap_domain_is_subsumed_by_decide() {
    use seal::verify::certify::{CertStatus, ProvenKind};
    let key = nth_key(1);
    let src = "contract Big { extern const k: PublicKey;
        spend f(relaxed flags: [Bool; 21], s: Signature) {
            require { count(b in flags where b => true) >= 11, k.check(s) }
        } keypath None; }";
    let args = format!(r#"{{"k": "{key}"}}"#);
    let c = compile(src, &args).expect("compile").expect("not rejected");
    let opt: Vec<LoweredLeaf> = c.naive.iter().map(optimize).collect();
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    let reports =
        seal::verify::certify::certify(&c.contract, &c.info, &c.env, &c.naive, &opt, &MARKER, &ctx);
    let r = reports.iter().find(|r| r.name == "f").unwrap();
    match &r.status {
        CertStatus::Proven {
            kind: ProvenKind::FullSymbolic { .. },
        } => {}
        other => panic!(
            "an over-cap [Bool;21] threshold should be FullSymbolic (cap subsumed by decide), got {other:?}"
        ),
    }
}

/// A planted divergence in the Int part of a mixed leaf (naive `bid<100` vs opt
/// `bid<101`, accepts bid=100 the naive rejects) must NEVER be certified Proven --
/// Engine B's structural equality refuses the mismatched `Within` node.
#[test]
fn planted_mixed_int_divergence_is_not_proven() {
    use seal::verify::certify::Assurance;
    let preimage: Vec<u8> = (0..32).map(|i| (i * 7 + 1) as u8).collect();
    let digest = seal::crypto::sha256::sha256(&preimage);
    let hhex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
    let key = nth_key(1);
    let (src_a, args) = mixed_src(100, &hhex, &key);
    let (src_b, _) = mixed_src(101, &hhex, &key);
    let ca = compile(&src_a, &args)
        .expect("compile A")
        .expect("not rejected");
    let cb = compile(&src_b, &args)
        .expect("compile B")
        .expect("not rejected");
    let opt_b: Vec<LoweredLeaf> = cb.naive.iter().map(optimize).collect(); // the bid<101 leaf
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };
    let reports = seal::verify::certify::certify(
        &ca.contract,
        &ca.info,
        &ca.env,
        &ca.naive,
        &opt_b,
        &MARKER,
        &ctx,
    );
    let r = reports.iter().find(|r| r.name == "f").unwrap();
    assert_ne!(
        r.status.assurance(),
        Assurance::Proven,
        "a planted mixed Int divergence was falsely certified Proven: {:?}",
        r.status
    );
}

// --- Engine A2 (decoupled grid) deterministic teeth ------------------------
//
// The random fuzz above gives BREADTH (it now generates decoupled-2-Int leaves
// via `c_two_decoupled`, and `validate` re-executes every strong verdict against
// the independent ground truth -- so a 2-Int false proof would surface as a
// FALSE VERDICT there). These two tests give the DEPTH/teeth: one pins that a
// known decoupled contract is actually proven `FullInt` over two vars AND agrees
// with brute force over a box; the other pins that a planted cross-axis
// divergence is never proven (the money-safety invariant).

fn decoupled_src(ahi: i64, blo: i64, bhi: i64) -> String {
    format!(
        "contract D {{ extern const k: PublicKey;
            spend f(relaxed a: Int, relaxed b: Int, s: Signature) {{
                require {{ a in 0..{ahi}, b in {blo}..{bhi}, k.check(s) }}
            }} keypath None; }}"
    )
}

/// A decoupled 2-Int contract certifies as `Proven(FullInt)` over BOTH vars, and
/// the optimized + naive scripts agree with the ground-truth predicate at every
/// point of a box that straddles all four range bounds (and the negative tail).
#[test]
fn decoupled_two_int_certifies_full_and_brute_forces_clean() {
    use seal::verify::certify::{CertStatus, ProvenKind};
    let src = decoupled_src(50, 10, 70);
    let args = format!(r#"{{"k": {:?}}}"#, nth_key(1));
    let c = compile(&src, &args)
        .expect("compile ok")
        .expect("not rejected");
    let opt: Vec<LoweredLeaf> = c.naive.iter().map(optimize).collect();
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };

    let reports =
        seal::verify::certify::certify(&c.contract, &c.info, &c.env, &c.naive, &opt, &MARKER, &ctx);
    let r = reports.iter().find(|r| r.name == "f").expect("leaf f");
    match &r.status {
        CertStatus::Proven {
            kind: ProvenKind::FullInt { var, .. },
        } => {
            assert!(
                var.contains(','),
                "expected a two-var FullInt proof, got var={var}"
            );
        }
        other => panic!("expected Proven(FullInt) over two decoupled ints, got {other:?}"),
    }

    // Brute-force the box: every (a, b, sig) with a in [-5, 55], b in [5, 75].
    let naive = c.naive.iter().find(|l| l.name == "f").unwrap();
    let optl = opt.iter().find(|l| l.name == "f").unwrap();
    let sig = c.info.spends.iter().find(|x| x.name == "f").unwrap();
    for a in -5i64..=55 {
        for b in 5i64..=75 {
            for &sg in &[false, true] {
                let plan = vec![
                    ("a".to_string(), SatValue::Int(a)),
                    ("b".to_string(), SatValue::Int(b)),
                    ("s".to_string(), SatValue::Sig(sg)),
                ];
                let nw = build_witness(naive, sig, &c.env, &plan, &MARKER).unwrap();
                let ow = build_witness(optl, sig, &c.env, &plan, &MARKER).unwrap();
                let nr = execute(&naive.script, &nw, &ctx).is_ok();
                let or = execute(&optl.script, &ow, &ctx).is_ok();
                let truth = (0..50).contains(&a) && (10..70).contains(&b) && sg;
                assert_eq!(nr, or, "naive/opt disagree at a={a} b={b} sig={sg}");
                assert_eq!(
                    nr, truth,
                    "FALSE PROOF: naive={nr} truth={truth} at a={a} b={b} sig={sg}"
                );
            }
        }
    }
}

/// Teeth: a planted CROSS-AXIS divergence -- the same decoupled shape but with an
/// optimized leaf whose `a` bound is off by one (accepts a=50 the naive rejects)
/// -- must NEVER be certified `Proven`. (A2 refuses it at try_prove; the windowed
/// enumeration additionally catches the divergence, so the verdict is a
/// Divergence, never a fundable Proven.)
#[test]
fn planted_cross_axis_divergence_is_not_proven() {
    use seal::verify::certify::Assurance;
    let mk = |ahi: i64| {
        format!(
            "contract T {{ extern const k: PublicKey;
                spend f(relaxed a: Int, relaxed b: Int, s: Signature) {{
                    require {{ a >= 0, a < {ahi}, b >= 0, b < 60, k.check(s) }}
                }} keypath None; }}"
        )
    };
    let args = format!(r#"{{"k": {:?}}}"#, nth_key(1));
    let ca = compile(&mk(50), &args)
        .expect("compile A")
        .expect("not rejected");
    let cb = compile(&mk(51), &args)
        .expect("compile B")
        .expect("not rejected");
    let opt_b: Vec<LoweredLeaf> = cb.naive.iter().map(optimize).collect(); // the a<51 leaf
    let oracle = |_pk: &[u8], s: &[u8]| s == MARKER;
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_fffe,
        tx_version: 2,
        verify_sig: &oracle,
    };

    // Certify contract A's predicate+naive against contract B's optimized leaf
    // (paired by name "f"): a planted naive(a<50) vs opt(a<51) divergence at a=50.
    let reports = seal::verify::certify::certify(
        &ca.contract,
        &ca.info,
        &ca.env,
        &ca.naive,
        &opt_b,
        &MARKER,
        &ctx,
    );
    let r = reports.iter().find(|r| r.name == "f").expect("leaf f");
    assert_ne!(
        r.status.assurance(),
        Assurance::Proven,
        "a planted cross-axis divergence was falsely certified Proven: {:?}",
        r.status
    );
    assert_eq!(
        r.status.assurance(),
        Assurance::Divergence,
        "the planted cross-axis divergence should be CAUGHT (Failed), got {:?}",
        r.status
    );
}
