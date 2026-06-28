//! Const evaluation and extern injection.
//!
//! Injection precedes instantiation: the args binder converts a
//! strict-JSON-subset document into typed [`ConstValue`]s for every extern,
//! then [`instantiate`] folds `const` items and evaluates template
//! preconditions with real values: `require 1 <= M <= N` either holds or
//! fails with the numbers shown.
//!
//! Const arithmetic is checked 128-bit, a range of about +/-1.7x10^38, beyond
//! any materializable value by roughly 28 orders of magnitude; exceeding it is
//! a compile error, never wraparound.
//!
//! Semantics mirror the checker exactly (sema validated everything first; the
//! evaluator computes). Deliberate strictness:
//! - `div`/`mod` require `a >= 0`, `b > 0`; for const operands the proof is
//!   the value check.
//! - `select` evaluates both arms (preconditions hold per node,
//!   branch-independent); comprehension elements all evaluate (no
//!   short-circuit `any`).
//! - Comprehension folds are capped (compile-time DoS guard).
//! - Hash intrinsics and `PublicKey.MuSig2` const-evaluate. Deprecated `sha1`
//!   alone stays unevaluated: a teaching diagnostic, not silence.
//!
//! Timelock values are validated on construction: heights < 500,000,000;
//! ISO-8601 timestamps (strict `YYYY-MM-DDThh:mm:ssZ`, UTC only) >=
//! 500,000,000 and <= u32::MAX; relative blocks/512-second units <= 65,535;
//! span literals round UP to 512-second units with a warning when inexact.

use std::collections::BTreeMap;

use crate::analysis::sema::{ContractInfo, HashAlg, Len, Ty, parse_int_text};
use crate::diagnostics::Diagnostic;
use crate::json::Json;
use crate::syntax::ast::*;
use crate::syntax::span::Span;

/// The machine domain bound: +/-(2^31 - 1).
pub const MACHINE_MAX: i128 = 2_147_483_647;
/// Comprehension fold cap, a compile-time-DoS guard, far beyond real use.
pub const MAX_FOLD_ITERATIONS: usize = 10_000;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstValue {
    Int(i128),
    Bool(bool),
    /// Raw bytes: `Bytes<N>`, `Hash<Alg>`, and `PublicKey` values alike
    /// (the type system distinguishes; values are bytes).
    Bytes(Vec<u8>),
    LockAbs(LockAbs),
    LockRel(LockRel),
    Array(Vec<ConstValue>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LockAbs {
    Height(u32),
    /// Unix seconds (MTP-evaluated on chain).
    Time(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LockRel {
    Blocks(u16),
    /// 512-second units (BIP68 granularity).
    Units(u16),
}

impl ConstValue {
    fn describe(&self) -> String {
        match self {
            ConstValue::Int(v) => v.to_string(),
            ConstValue::Bool(b) => b.to_string(),
            ConstValue::Bytes(b) => format!("0x{}", hex(b)),
            ConstValue::LockAbs(LockAbs::Height(h)) => format!("height {h}"),
            ConstValue::LockAbs(LockAbs::Time(t)) => format!("unix time {t}"),
            ConstValue::LockRel(LockRel::Blocks(b)) => format!("{b} blocks"),
            ConstValue::LockRel(LockRel::Units(u)) => format!("{u}*512s"),
            ConstValue::Array(items) => format!("[{} elements]", items.len()),
        }
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Bound constant environment: name to value, deterministic order.
pub type Env = BTreeMap<String, ConstValue>;

// --- args binding ---

/// Bind a parsed args document against the contract's extern signatures.
/// Errors are plain strings (they belong to the args file, not to `.sl`
/// spans); they name the extern and teach the expected encoding.
pub fn bind_args(info: &ContractInfo, args: &Json) -> Result<Env, Vec<String>> {
    let Json::Object(fields) = args else {
        return Err(vec![
            "the args document must be a JSON object of extern values".into(),
        ]);
    };
    let mut errors = Vec::new();
    let mut env = Env::new();

    // Typo protection: every key must be a declared extern.
    for (key, _) in fields {
        if !info.externs.iter().any(|(n, _)| n == key) {
            errors.push(format!("`{key}` is not an extern of this contract"));
        }
    }

    // Bind in declaration order so named lengths ([T; N]) can resolve.
    for (name, ty) in &info.externs {
        let Some((_, value)) = fields.iter().find(|(k, _)| k == name) else {
            errors.push(format!(
                "missing extern `{name}` (declared `{name}: ...` in the contract)"
            ));
            continue;
        };
        match bind_value(name, ty, value, &env) {
            Ok(v) => {
                env.insert(name.clone(), v);
            }
            Err(e) => errors.push(e),
        }
    }

    if errors.is_empty() {
        Ok(env)
    } else {
        Err(errors)
    }
}

fn bind_value(name: &str, ty: &Ty, json: &Json, env: &Env) -> Result<ConstValue, String> {
    match ty {
        Ty::Int => match json {
            Json::Int(v) if v.unsigned_abs() <= MACHINE_MAX as u128 => Ok(ConstValue::Int(*v)),
            Json::Int(v) => Err(format!(
                "`{name}`: {v} does not fit the 4-byte CScriptNum domain +/-{MACHINE_MAX}"
            )),
            other => Err(type_err(name, "an integer", other)),
        },
        Ty::Bool => match json {
            Json::Bool(b) => Ok(ConstValue::Bool(*b)),
            other => Err(type_err(name, "true or false", other)),
        },
        Ty::PublicKey => {
            let v = bind_hex(name, json, 32)?;
            validate_pubkey(name, &v)?;
            Ok(v)
        }
        Ty::Bytes(len) => {
            let n = resolve_len(name, len, env)?;
            bind_hex(name, json, n)
        }
        Ty::Hash(alg) => bind_hex(name, json, alg_len(*alg)),
        Ty::LockTimeAbs => match json {
            Json::Object(fields) => match fields.as_slice() {
                [(k, Json::Int(h))] if k == "height" => {
                    let h = u32::try_from(*h)
                        .ok()
                        .filter(|h| *h < 500_000_000)
                        .ok_or_else(|| format!("`{name}`: a height is 0 <= h < 500,000,000"))?;
                    Ok(ConstValue::LockAbs(LockAbs::Height(h)))
                }
                [(k, Json::Str(iso))] if k == "time" => {
                    let t = parse_iso8601(iso).map_err(|e| format!("`{name}`: {e}"))?;
                    Ok(ConstValue::LockAbs(LockAbs::Time(t)))
                }
                _ => Err(format!(
                    "`{name}`: LockTime.Absolute is {{\"height\": n}} or \
                     {{\"time\": \"YYYY-MM-DDThh:mm:ssZ\"}}"
                )),
            },
            other => Err(type_err(
                name,
                "an object ({\"height\": ...} or {\"time\": ...})",
                other,
            )),
        },
        Ty::LockTimeRel => match json {
            Json::Object(fields) => match fields.as_slice() {
                [(k, Json::Int(b))] if k == "blocks" => {
                    let b = u16::try_from(*b)
                        .map_err(|_| format!("`{name}`: relative blocks are 0 <= n <= 65,535"))?;
                    Ok(ConstValue::LockRel(LockRel::Blocks(b)))
                }
                [(k, Json::Str(span))] if k == "time" => {
                    let (units, _rounded) =
                        iso_duration_to_units(span).map_err(|e| format!("`{name}`: {e}"))?;
                    Ok(ConstValue::LockRel(LockRel::Units(units)))
                }
                _ => Err(format!(
                    "`{name}`: LockTime.Relative is {{\"blocks\": n}} or {{\"time\": \"90d\"}}"
                )),
            },
            other => Err(type_err(
                name,
                "an object ({\"blocks\": ...} or {\"time\": ...})",
                other,
            )),
        },
        Ty::Array(elem, len) => {
            let Json::Array(items) = json else {
                return Err(type_err(name, "an array", json));
            };
            let n = resolve_len(name, len, env)?;
            if items.len() != n {
                return Err(format!(
                    "`{name}`: expected {n} elements (the declared length), found {}",
                    items.len()
                ));
            }
            let mut out = Vec::with_capacity(items.len());
            for (i, item) in items.iter().enumerate() {
                out.push(bind_value(&format!("{name}[{i}]"), elem, item, env)?);
            }
            Ok(ConstValue::Array(out))
        }
        Ty::Signature => Err(format!(
            "`{name}`: Signature is witness-only and can never be bound"
        )),
    }
}

fn type_err(name: &str, expected: &str, got: &Json) -> String {
    let got = match got {
        Json::Object(_) => "an object",
        Json::Array(_) => "an array",
        Json::Str(_) => "a string",
        Json::Int(_) => "an integer",
        Json::Bool(_) => "a boolean",
    };
    format!("`{name}`: expected {expected}, found {got}")
}

/// An off-curve `PublicKey` extern would make every path that pins it
/// permanently unspendable (no such point means no valid signature, ever),
/// a feasibility bug caught at injection time.
fn validate_pubkey(name: &str, v: &ConstValue) -> Result<(), String> {
    let ConstValue::Bytes(b) = v else {
        return Ok(());
    };
    let on_curve = <[u8; 32]>::try_from(b.as_slice())
        .ok()
        .and_then(|k| crate::crypto::secp::Point::lift_x(&k))
        .is_some();
    if on_curve {
        Ok(())
    } else {
        Err(format!(
            "`{name}`: this x-coordinate is not on the secp256k1 curve, no such \
             public key exists, so no signature could ever satisfy a check against it"
        ))
    }
}

fn bind_hex(name: &str, json: &Json, expected_bytes: usize) -> Result<ConstValue, String> {
    let Json::Str(s) = json else {
        return Err(type_err(name, "a \"0x...\" hex string", json));
    };
    let Some(h) = s.strip_prefix("0x") else {
        return Err(format!("`{name}`: hex values start with \"0x\""));
    };
    if h.len() != expected_bytes * 2 || !h.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(format!(
            "`{name}`: expected exactly {} hex digits ({expected_bytes} bytes), found {} characters",
            expected_bytes * 2,
            h.len()
        ));
    }
    let bytes = (0..expected_bytes)
        .map(|i| u8::from_str_radix(&h[i * 2..i * 2 + 2], 16).expect("validated hex"))
        .collect();
    Ok(ConstValue::Bytes(bytes))
}

fn resolve_len(name: &str, len: &Len, env: &Env) -> Result<usize, String> {
    match len {
        Len::Lit(n) => Ok(*n as usize),
        Len::Named(n) => match env.get(n) {
            Some(ConstValue::Int(v)) if *v >= 0 && *v <= MAX_FOLD_ITERATIONS as i128 => {
                Ok(*v as usize)
            }
            Some(ConstValue::Int(v)) => Err(format!(
                "`{name}`: length `{n}` = {v} is out of range (0..={MAX_FOLD_ITERATIONS})"
            )),
            _ => Err(format!(
                "`{name}`: length `{n}` must be bound to an Int before this extern \
                 (externs bind in declaration order)"
            )),
        },
    }
}

fn alg_len(alg: HashAlg) -> usize {
    match alg {
        HashAlg::Sha256 | HashAlg::Hash256 => 32,
        HashAlg::Hash160 | HashAlg::Ripemd160 | HashAlg::Sha1 => 20,
    }
}

// --- timestamps and spans ---

/// Strict `YYYY-MM-DDThh:mm:ssZ` (UTC only) to unix seconds, validated into
/// the CLTV time domain [500,000,000, u32::MAX].
pub fn parse_iso8601(s: &str) -> Result<u32, String> {
    let b = s.as_bytes();
    let shape_ok = b.len() == 20
        && b[4] == b'-'
        && b[7] == b'-'
        && b[10] == b'T'
        && b[13] == b':'
        && b[16] == b':'
        && b[19] == b'Z';
    if !shape_ok {
        return Err("timestamps are strict `YYYY-MM-DDThh:mm:ssZ` (UTC only)".into());
    }
    let num = |range: std::ops::Range<usize>| -> Result<i64, String> {
        let part = &s[range];
        if !part.bytes().all(|b| b.is_ascii_digit()) {
            return Err("timestamps are strict `YYYY-MM-DDThh:mm:ssZ` (UTC only)".into());
        }
        Ok(part.parse::<i64>().expect("digits"))
    };
    let (y, mo, d) = (num(0..4)?, num(5..7)?, num(8..10)?);
    let (h, mi, sec) = (num(11..13)?, num(14..16)?, num(17..19)?);
    let leap = (y % 4 == 0 && y % 100 != 0) || y % 400 == 0;
    let days_in_month = [
        31,
        if leap { 29 } else { 28 },
        31,
        30,
        31,
        30,
        31,
        31,
        30,
        31,
        30,
        31,
    ];
    if !(1..=12).contains(&mo) || d < 1 || d > days_in_month[(mo - 1) as usize] {
        return Err("invalid calendar date".into());
    }
    if h > 23 || mi > 59 || sec > 59 {
        return Err("invalid time of day".into());
    }
    // Howard Hinnant's days-from-civil.
    let yy = y - if mo <= 2 { 1 } else { 0 };
    let era = yy.div_euclid(400);
    let yoe = yy - era * 400;
    let doy = (153 * (mo + if mo > 2 { -3 } else { 9 }) + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    let days = era * 146097 + doe - 719468;
    let unix = days * 86400 + h * 3600 + mi * 60 + sec;
    if unix < 500_000_000 {
        return Err("CLTV time-domain values are >= 500,000,000 (after 1985-11-05); use a height for earlier".into());
    }
    u32::try_from(unix).map_err(|_| "timestamp exceeds the u32 nLockTime domain (year 2106)".into())
}

/// A span literal (`90d`) to 512-second units, rounded UP; reports whether
/// rounding occurred (warn on inexact spans).
/// Strict ISO-8601 duration subset: `"PnW"` (weeks, the exclusive form per
/// the standard) or `"PnDTnHnMnS"` with any subset of components in order,
/// integers only, at least one component. Mirrors the strict ISO-8601
/// TIMESTAMP rule on the absolute axis. Returns (512-second units,
/// rounded-up?).
pub fn iso_duration_to_units(s: &str) -> Result<(u16, bool), String> {
    const TEACH: &str = "ISO-8601 durations are \"PnW\" (weeks) or \"PnDTnHnMnS\" \
         combinations, e.g. \"P90D\", \"PT1H30M\", \"P1DT12H\"";

    fn num(b: &[u8], i: &mut usize) -> Option<i128> {
        let start = *i;
        while *i < b.len() && b[*i].is_ascii_digit() {
            *i += 1;
        }
        if *i == start || *i - start > 12 {
            return None;
        }
        std::str::from_utf8(&b[start..*i])
            .ok()?
            .parse::<i128>()
            .ok()
    }

    let Some(rest) = s.strip_prefix('P') else {
        return Err(TEACH.into());
    };
    let b = rest.as_bytes();
    let mut i = 0usize;
    let mut secs: i128 = 0;
    let mut any = false;

    // Date part: nW (exclusive) or nD; calendar units teach.
    if i < b.len() && b[i].is_ascii_digit() {
        let n = num(b, &mut i).ok_or(TEACH)?;
        match b.get(i) {
            Some(b'W') => {
                i += 1;
                if i != b.len() {
                    return Err(TEACH.into()); // PnW is the exclusive form
                }
                secs += n * 604_800;
                any = true;
            }
            Some(b'D') => {
                i += 1;
                secs += n * 86_400;
                any = true;
            }
            Some(b'Y') | Some(b'M') => {
                return Err("years/months are calendar-dependent; express the span \
                     in weeks or days"
                    .into());
            }
            _ => return Err(TEACH.into()),
        }
    }
    // Time part: T then at least one of nH nM nS, in order.
    if i < b.len() && b[i] == b'T' {
        i += 1;
        let mut time_any = false;
        for (unit, mult) in [(b'H', 3600i128), (b'M', 60), (b'S', 1)] {
            if i < b.len() && b[i].is_ascii_digit() {
                let save = i;
                let Some(n) = num(b, &mut i) else {
                    return Err(TEACH.into());
                };
                if b.get(i) == Some(&unit) {
                    i += 1;
                    secs += n * mult;
                    time_any = true;
                    any = true;
                } else {
                    i = save; // the number belongs to a later unit
                }
            }
        }
        if !time_any {
            return Err(TEACH.into());
        }
    }
    if i != b.len() || !any {
        return Err(TEACH.into());
    }

    let rounded = secs.rem_euclid(512) != 0;
    let units = secs.div_euclid(512) + i128::from(rounded);
    u16::try_from(units)
        .map(|u| (u, rounded))
        .map_err(|_| "relative time-spans cap at 65,535 x 512s, about 388 days".into())
}

// --- instantiation ---

/// Fold `const` items and evaluate template preconditions with the bound
/// extern values. Spend bodies and the layout are NOT evaluated here
/// (witness-dependent / crypto-layer work).
pub fn instantiate(contract: &Contract, env: &mut Env) -> Vec<Diagnostic> {
    let mut ev = Evaluator {
        env,
        diags: Vec::new(),
        scope: Vec::new(),
    };
    for item in &contract.items {
        match item {
            Item::Const { name, value, .. } => {
                if let Ok(v) = ev.eval(value) {
                    ev.env.insert(name.text.clone(), v);
                }
            }
            Item::Precondition(req) => {
                for cond in &req.items {
                    match ev.eval(cond) {
                        Ok(ConstValue::Bool(true)) => {}
                        Ok(ConstValue::Bool(false)) => {
                            let values = ev.free_name_values(cond);
                            ev.diags.push(Diagnostic::error(
                                "inst/precondition",
                                format!(
                                    "template precondition failed at instantiation{}{}",
                                    if values.is_empty() { "" } else { ": " },
                                    values
                                ),
                                cond.span(),
                            ));
                        }
                        Ok(other) => {
                            // sema guarantees Bool; defensive.
                            ev.diags.push(Diagnostic::error(
                                "inst/precondition",
                                format!("precondition evaluated to {}", other.describe()),
                                cond.span(),
                            ));
                        }
                        Err(()) => {}
                    }
                }
            }
            Item::ExternConst { .. } | Item::Spend(_) | Item::Keypath(_) => {}
        }
    }
    ev.diags
}

/// Evaluate one const expression against a bound environment, returning the
/// value and any diagnostics it produced (e.g. locktime validation). Used by
/// the path analyses to evaluate `after(...)` arguments and probe pin values.
pub fn eval_in_env(e: &Expr, env: &Env) -> (Option<ConstValue>, Vec<Diagnostic>) {
    let mut scratch = env.clone();
    let mut ev = Evaluator {
        env: &mut scratch,
        diags: Vec::new(),
        scope: Vec::new(),
    };
    let v = ev.eval(e).ok();
    (v, ev.diags)
}

struct Evaluator<'e> {
    env: &'e mut Env,
    diags: Vec<Diagnostic>,
    /// Comprehension binder/accumulator values, lexical.
    scope: Vec<(String, ConstValue)>,
}

impl<'e> Evaluator<'e> {
    fn error(&mut self, code: &'static str, msg: impl Into<String>, span: Span) {
        self.diags.push(Diagnostic::error(code, msg, span));
    }
    fn warn(&mut self, code: &'static str, msg: impl Into<String>, span: Span) {
        self.diags.push(Diagnostic::warning(code, msg, span));
    }

    /// "M = 5, N = 3": the values of the free names in a failed precondition.
    fn free_name_values(&self, e: &Expr) -> String {
        let mut names: Vec<&Ident> = Vec::new();
        collect_names(e, &mut names);
        let mut parts: Vec<String> = Vec::new();
        for n in names {
            if let Some(v) = self.env.get(&n.text) {
                let part = format!("{} = {}", n.text, v.describe());
                if !parts.contains(&part) {
                    parts.push(part);
                }
            }
        }
        parts.join(", ")
    }

    fn lookup(&self, name: &str) -> Option<&ConstValue> {
        self.scope
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, v)| v)
            .or_else(|| self.env.get(name))
    }

    /// Arithmetic operand: Int, or Bool widened to 0/1.
    fn as_int(&mut self, e: &Expr) -> Result<i128, ()> {
        match self.eval(e)? {
            ConstValue::Int(v) => Ok(v),
            ConstValue::Bool(b) => Ok(b as i128),
            other => {
                let (msg, span) = (
                    format!("expected an integer, found {}", other.describe()),
                    e.span(),
                );
                self.error("inst/type", msg, span);
                Err(())
            }
        }
    }

    fn checked(&mut self, v: Option<i128>, span: Span) -> Result<ConstValue, ()> {
        match v {
            Some(v) => Ok(ConstValue::Int(v)),
            None => {
                self.error(
                    "inst/overflow",
                    "const arithmetic exceeded checked 128-bit precision",
                    span,
                );
                Err(())
            }
        }
    }

    fn eval(&mut self, e: &Expr) -> Result<ConstValue, ()> {
        match e {
            Expr::Int { text, span } => match parse_int_text(text) {
                Some(v) if v <= i128::MAX as u128 => Ok(ConstValue::Int(v as i128)),
                _ => {
                    self.error(
                        "inst/overflow",
                        "integer literal exceeds 128-bit precision",
                        *span,
                    );
                    Err(())
                }
            },
            Expr::Bool { value, .. } => Ok(ConstValue::Bool(*value)),
            Expr::Name(n) => match self.lookup(&n.text) {
                Some(v) => Ok(v.clone()),
                None => {
                    // sema guarantees resolution; defensive.
                    let (msg, span) = (format!("`{}` has no value", n.text), n.span);
                    self.error("inst/unresolved", msg, span);
                    Err(())
                }
            },
            Expr::Unary { op, operand, span } => match op {
                UnaryOp::Not => match self.eval(operand)? {
                    ConstValue::Bool(b) => Ok(ConstValue::Bool(!b)),
                    other => {
                        let msg = format!("`!` takes Bool, found {}", other.describe());
                        self.error("inst/type", msg, operand.span());
                        Err(())
                    }
                },
                UnaryOp::Neg => {
                    let v = self.as_int(operand)?;
                    self.checked(v.checked_neg(), *span)
                }
            },
            Expr::Binary { op, lhs, rhs, span } => {
                let l = self.as_int(lhs)?;
                let r = self.as_int(rhs)?;
                let v = match op {
                    BinaryOp::Add => l.checked_add(r),
                    BinaryOp::Sub => l.checked_sub(r),
                };
                self.checked(v, *span)
            }
            Expr::Compare { first, rest, .. } => {
                // Single == / != may be non-Int (sema dispatched on class).
                if rest.len() == 1 && matches!(rest[0].0, CmpOp::Eq | CmpOp::Ne) {
                    let l = self.eval(first)?;
                    let r = self.eval(&rest[0].1)?;
                    let eq = const_eq(&l, &r);
                    return Ok(ConstValue::Bool(if rest[0].0 == CmpOp::Eq {
                        eq
                    } else {
                        !eq
                    }));
                }
                let mut prev = self.as_int(first)?;
                for (op, e) in rest {
                    let next = self.as_int(e)?;
                    let holds = match op {
                        CmpOp::Lt => prev < next,
                        CmpOp::Le => prev <= next,
                        CmpOp::Gt => prev > next,
                        CmpOp::Ge => prev >= next,
                        CmpOp::Eq | CmpOp::Ne => unreachable!("parser rejects chained =="),
                    };
                    if !holds {
                        return Ok(ConstValue::Bool(false));
                    }
                    prev = next;
                }
                Ok(ConstValue::Bool(true))
            }
            Expr::In {
                value,
                lo,
                hi,
                inclusive,
                ..
            } => {
                let v = self.as_int(value)?;
                let l = self.as_int(lo)?;
                let h = self.as_int(hi)?;
                Ok(ConstValue::Bool(if *inclusive {
                    v >= l && v <= h
                } else {
                    v >= l && v < h
                }))
            }
            Expr::Index { base, index, span } => {
                let arr = self.eval(base)?;
                let idx = self.as_int(index)?;
                let ConstValue::Array(items) = arr else {
                    self.error("inst/type", "only arrays index", *span);
                    return Err(());
                };
                if idx < 0 || idx as usize >= items.len() {
                    let msg = format!("index {idx} out of bounds (length {})", items.len());
                    self.error("inst/index", msg, *span);
                    return Err(());
                }
                Ok(items[idx as usize].clone())
            }
            Expr::ArrayLit { elems, .. } => {
                let mut out = Vec::with_capacity(elems.len());
                for e in elems {
                    out.push(self.eval(e)?);
                }
                Ok(ConstValue::Array(out))
            }
            Expr::TypedCtor { args, span, .. } => {
                // Bytes<N>("0x...") / Hash<A>("0x..."): sema validated shape
                // and hex length; decode.
                match args.first().map(|a| &a.value) {
                    Some(Expr::Str { text, .. }) => match decode_hex(text) {
                        Some(bytes) => Ok(ConstValue::Bytes(bytes)),
                        None => {
                            self.error("inst/hex", "invalid hex literal", *span);
                            Err(())
                        }
                    },
                    _ => {
                        // sema guarantees the single-Str shape; defensive.
                        self.error("inst/position", "malformed typed constructor", *span);
                        Err(())
                    }
                }
            }
            Expr::Call { callee, args, span } => self.call(callee, args, *span),
            Expr::Comprehension {
                callee,
                acc,
                binders,
                where_clauses,
                body,
                span,
            } => {
                let depth = self.scope.len();
                let r =
                    self.comprehension(callee, acc.as_ref(), binders, where_clauses, body, *span);
                self.scope.truncate(depth);
                r
            }
            Expr::Member { span, .. } | Expr::Str { span, .. } | Expr::Duration { span, .. } => {
                // sema rejects these positions; defensive.
                self.error("inst/position", "not a const value position", *span);
                Err(())
            }
        }
    }

    fn call(&mut self, callee: &Expr, args: &[Arg], span: Span) -> Result<ConstValue, ()> {
        if let Expr::Member { base, member, .. } = callee {
            if let Expr::Name(type_name) = base.as_ref() {
                if type_name.text == "LockTime" {
                    return self.locktime(member, args, span);
                }
                if type_name.text == "PublicKey" && member.text == "MuSig2" {
                    return self.musig2(args, span);
                }
            }
            // key.check(sig) is never const (sema); defensive.
            self.error("inst/position", "not const-evaluable", span);
            return Err(());
        }
        let Expr::Name(name) = callee else {
            self.error("inst/position", "not const-evaluable", span);
            return Err(());
        };
        match name.text.as_str() {
            "min" | "max" => {
                let a = self.as_int(&args[0].value)?;
                let b = self.as_int(&args[1].value)?;
                Ok(ConstValue::Int(if name.text == "min" {
                    a.min(b)
                } else {
                    a.max(b)
                }))
            }
            "abs" => {
                let a = self.as_int(&args[0].value)?;
                self.checked(a.checked_abs(), span)
            }
            "int" => {
                let v = self.as_int(&args[0].value)?;
                Ok(ConstValue::Int(v))
            }
            "pow" => {
                let base = self.as_int(&args[0].value)?;
                let exp = self.as_int(&args[1].value)?;
                if !(0..=200).contains(&exp) {
                    self.error("inst/pow-domain", "`pow` exponent must be 0..=200", span);
                    return Err(());
                }
                self.checked(base.checked_pow(exp as u32), span)
            }
            "select" => {
                // Strict: both arms evaluate (preconditions hold per node,
                // branch-independent).
                let ConstValue::Bool(c) = self.eval(&args[0].value)? else {
                    self.error("inst/type", "`select` condition must be Bool", span);
                    return Err(());
                };
                let t = self.eval(&args[1].value)?;
                let e = self.eval(&args[2].value)?;
                Ok(if c { t } else { e })
            }
            "PublicKey" => {
                // PublicKey("0x..."): sema validated 64 hex digits; decode
                // and check the point exists (an off-curve key makes every
                // path it pins permanently unspendable, a feasibility bug).
                match args.first().map(|a| &a.value) {
                    Some(Expr::Str { text, .. }) => match decode_hex(text) {
                        Some(bytes) => {
                            if <[u8; 32]>::try_from(bytes.as_slice())
                                .ok()
                                .and_then(|k| crate::crypto::secp::Point::lift_x(&k))
                                .is_none()
                            {
                                self.error(
                                    "inst/key",
                                    "this x-coordinate is not on the secp256k1 curve, \
                                     no such public key exists, so no signature could \
                                     ever satisfy a check against it",
                                    span,
                                );
                                return Err(());
                            }
                            Ok(ConstValue::Bytes(bytes))
                        }
                        None => {
                            self.error("inst/hex", "invalid hex literal", span);
                            Err(())
                        }
                    },
                    _ => {
                        self.error("inst/position", "malformed key literal", span);
                        Err(())
                    }
                }
            }
            alg @ ("sha256" | "hash256" | "hash160" | "ripemd160" | "sha1") => {
                // Const hashing: commitments fold at compile time, so
                // `const digest = sha256(preimage_bytes)` just works.
                if args.len() != 1 {
                    self.error(
                        "inst/arity",
                        format!("`{alg}` takes one Bytes argument"),
                        span,
                    );
                    return Err(());
                }
                let ConstValue::Bytes(input) = self.eval(&args[0].value)? else {
                    self.error("inst/type", format!("`{alg}` hashes Bytes values"), span);
                    return Err(());
                };
                let out: Vec<u8> = match alg {
                    "sha256" => crate::crypto::sha256::sha256(&input).to_vec(),
                    "hash256" => {
                        crate::crypto::sha256::sha256(&crate::crypto::sha256::sha256(&input))
                            .to_vec()
                    }
                    "hash160" => {
                        crate::crypto::ripemd160::ripemd160(&crate::crypto::sha256::sha256(&input))
                            .to_vec()
                    }
                    "ripemd160" => crate::crypto::ripemd160::ripemd160(&input).to_vec(),
                    _ => {
                        // sha1 stays unimplemented: present-but-deprecated
                        // surface; no const story until someone needs interop
                        // with a legacy commitment.
                        self.error(
                            "inst/not-yet",
                            "`sha1` is deprecated and has no const evaluation; \
                             use sha256",
                            span,
                        );
                        return Err(());
                    }
                };
                Ok(ConstValue::Bytes(out))
            }
            other => {
                // sema guarantees the call set; defensive.
                let msg = format!("`{other}` is not const-evaluable");
                self.error("inst/position", msg, span);
                Err(())
            }
        }
    }

    /// `PublicKey.MuSig2(keys)`: BIP327 KeySort + KeyAgg over x-only
    /// keys (even-y lift, the BIP390 convention). The key-path half of
    /// the canonical key-ordering rule: the aggregate, and therefore the
    /// address, depends on the key SET.
    fn musig2(&mut self, args: &[Arg], span: Span) -> Result<ConstValue, ()> {
        if args.len() != 1 {
            self.error("inst/arity", "`PublicKey.MuSig2` takes one key array", span);
            return Err(());
        }
        let ConstValue::Array(items) = self.eval(&args[0].value)? else {
            self.error(
                "inst/type",
                "`PublicKey.MuSig2` needs a [PublicKey; N] array",
                span,
            );
            return Err(());
        };
        let mut keys = Vec::with_capacity(items.len());
        for it in &items {
            let ConstValue::Bytes(b) = it else {
                self.error(
                    "inst/type",
                    "`PublicKey.MuSig2` elements must be public keys",
                    span,
                );
                return Err(());
            };
            let Ok(k) = <[u8; 32]>::try_from(b.as_slice()) else {
                self.error("inst/type", "public keys are 32 x-only bytes", span);
                return Err(());
            };
            keys.push(k);
        }
        match crate::crypto::musig::aggregate_xonly(&keys) {
            Ok(agg) => Ok(ConstValue::Bytes(agg.to_vec())),
            Err(e) => {
                // e.g. an x-only encoding that is not on the curve.
                self.error("inst/key", format!("MuSig2 aggregation failed: {e}"), span);
                Err(())
            }
        }
    }

    fn locktime(&mut self, variant: &Ident, args: &[Arg], span: Span) -> Result<ConstValue, ()> {
        let Some(label_ident) = args.first().and_then(|a| a.label.as_ref()) else {
            self.error(
                "inst/locktime",
                "LockTime constructors take one labeled argument",
                span,
            );
            return Err(());
        };
        let label = label_ident.text.as_str();
        match (variant.text.as_str(), label) {
            ("Absolute", "height") => {
                let h = self.as_int(&args[0].value)?;
                if !(0..500_000_000).contains(&h) {
                    self.error("inst/locktime", "a height is 0 <= h < 500,000,000", span);
                    return Err(());
                }
                Ok(ConstValue::LockAbs(LockAbs::Height(h as u32)))
            }
            ("Absolute", "time") => {
                let Expr::Str { text, .. } = &args[0].value else {
                    self.error(
                        "inst/locktime",
                        "expected an ISO-8601 timestamp string",
                        span,
                    );
                    return Err(());
                };
                match parse_iso8601(text) {
                    Ok(t) => Ok(ConstValue::LockAbs(LockAbs::Time(t))),
                    Err(e) => {
                        self.error("inst/locktime", e, span);
                        Err(())
                    }
                }
            }
            ("Relative", "blocks") => {
                let b = self.as_int(&args[0].value)?;
                if !(0..=65_535).contains(&b) {
                    self.error(
                        "inst/locktime",
                        "relative blocks are 0 <= n <= 65,535",
                        span,
                    );
                    return Err(());
                }
                Ok(ConstValue::LockRel(LockRel::Blocks(b as u16)))
            }
            ("Relative", "time") => {
                let Expr::Str { text, .. } = &args[0].value else {
                    // sema validated; degrade per totality.
                    self.error(
                        "inst/locktime",
                        "expected an ISO-8601 duration string",
                        span,
                    );
                    return Err(());
                };
                match iso_duration_to_units(text) {
                    Ok((units, rounded)) => {
                        if rounded {
                            self.warn(
                                "inst/span-rounded",
                                format!(
                                    "span rounded UP to {units}*512s = {} seconds (BIP68 \
                                     granularity)",
                                    units as u64 * 512
                                ),
                                span,
                            );
                        }
                        Ok(ConstValue::LockRel(LockRel::Units(units)))
                    }
                    Err(e) => {
                        self.error("inst/locktime", e, span);
                        Err(())
                    }
                }
            }
            _ => {
                self.error("inst/locktime", "unknown LockTime constructor form", span);
                Err(())
            }
        }
    }

    fn comprehension(
        &mut self,
        callee: &Ident,
        acc: Option<&AccClause>,
        binders: &[Binder],
        where_clauses: &[Expr],
        body: &Expr,
        span: Span,
    ) -> Result<ConstValue, ()> {
        // Materialize every sequence; zip lengths must agree concretely.
        let mut seqs: Vec<Vec<ConstValue>> = Vec::with_capacity(binders.len());
        for b in binders {
            let items = match &b.seq {
                Seq::Expr(e) => match self.eval(e)? {
                    ConstValue::Array(items) => items,
                    other => {
                        let msg = format!("a binder iterates an array, found {}", other.describe());
                        self.error("inst/type", msg, e.span());
                        return Err(());
                    }
                },
                Seq::Range {
                    lo,
                    hi,
                    inclusive,
                    span: rspan,
                } => {
                    let l = self.as_int(lo)?;
                    let h = self.as_int(hi)?;
                    let h = if *inclusive { h + 1 } else { h };
                    if h < l {
                        self.error("inst/range", "empty range (hi < lo)", *rspan);
                        return Err(());
                    }
                    if (h - l) as usize > MAX_FOLD_ITERATIONS {
                        let msg = format!(
                            "comprehension over {} elements exceeds the {MAX_FOLD_ITERATIONS} fold cap",
                            h - l
                        );
                        self.error("inst/fold-cap", msg, *rspan);
                        return Err(());
                    }
                    (l..h).map(ConstValue::Int).collect()
                }
            };
            if items.len() > MAX_FOLD_ITERATIONS {
                let msg = format!(
                    "comprehension over {} elements exceeds the {MAX_FOLD_ITERATIONS} fold cap",
                    items.len()
                );
                self.error("inst/fold-cap", msg, b.span);
                return Err(());
            }
            seqs.push(items);
        }
        let n = seqs.first().map(|s| s.len()).unwrap_or(0);
        if seqs.iter().any(|s| s.len() != n) {
            let lens: Vec<String> = seqs.iter().map(|s| s.len().to_string()).collect();
            self.error(
                "inst/zip-len",
                format!(
                    "parallel binders iterate zipped and must have equal lengths: {}",
                    lens.join(" vs ")
                ),
                span,
            );
            return Err(());
        }

        let agg = callee.text.as_str();
        let mut acc_val = if let Some(a) = acc {
            Some(self.eval(&a.init)?)
        } else {
            None
        };
        let mut sum: i128 = 0;
        let mut count: i128 = 0;
        let mut all = true;
        let mut any = false;

        for i in 0..n {
            let depth = self.scope.len();
            for (b, seq) in binders.iter().zip(&seqs) {
                self.scope.push((b.name.text.clone(), seq[i].clone()));
            }
            if let (Some(a), Some(v)) = (acc, &acc_val) {
                self.scope.push((a.name.text.clone(), v.clone()));
            }

            let mut included = true;
            for w in where_clauses {
                match self.eval(w) {
                    Ok(ConstValue::Bool(b)) => included &= b,
                    Ok(_) | Err(()) => {
                        self.scope.truncate(depth);
                        return Err(());
                    }
                }
            }
            if included {
                let body_val = match self.eval(body) {
                    Ok(v) => v,
                    Err(()) => {
                        self.scope.truncate(depth);
                        return Err(());
                    }
                };
                match (agg, &body_val) {
                    ("sum", ConstValue::Int(v)) => match sum.checked_add(*v) {
                        Some(s) => sum = s,
                        None => {
                            self.scope.truncate(depth);
                            self.error("inst/overflow", "sum exceeded 128-bit precision", span);
                            return Err(());
                        }
                    },
                    ("sum", ConstValue::Bool(b)) => sum += *b as i128,
                    ("count", ConstValue::Bool(b)) => count += *b as i128,
                    ("all", ConstValue::Bool(b)) => all &= *b,
                    ("any", ConstValue::Bool(b)) => any |= *b,
                    ("fold", v) => acc_val = Some(v.clone()),
                    _ => {
                        self.scope.truncate(depth);
                        self.error("inst/type", "comprehension body type mismatch", body.span());
                        return Err(());
                    }
                }
            }
            self.scope.truncate(depth);
        }

        Ok(match agg {
            "sum" => ConstValue::Int(sum),
            "count" => ConstValue::Int(count),
            "all" => ConstValue::Bool(all),
            "any" => ConstValue::Bool(any),
            "fold" => acc_val.expect("fold has acc"),
            _ => unreachable!("sema validated aggregators"),
        })
    }
}

fn const_eq(a: &ConstValue, b: &ConstValue) -> bool {
    match (a, b) {
        // Bool/Int widening mirror.
        (ConstValue::Int(x), ConstValue::Bool(y)) => *x == *y as i128,
        (ConstValue::Bool(x), ConstValue::Int(y)) => *x as i128 == *y,
        _ => a == b,
    }
}

fn collect_names<'a>(e: &'a Expr, out: &mut Vec<&'a Ident>) {
    match e {
        Expr::Name(n) => out.push(n),
        Expr::Unary { operand, .. } => collect_names(operand, out),
        Expr::Binary { lhs, rhs, .. } => {
            collect_names(lhs, out);
            collect_names(rhs, out);
        }
        Expr::Compare { first, rest, .. } => {
            collect_names(first, out);
            for (_, e) in rest {
                collect_names(e, out);
            }
        }
        Expr::In { value, lo, hi, .. } => {
            collect_names(value, out);
            collect_names(lo, out);
            collect_names(hi, out);
        }
        Expr::Index { base, index, .. } => {
            collect_names(base, out);
            collect_names(index, out);
        }
        Expr::Call { args, .. } | Expr::TypedCtor { args, .. } => {
            for a in args {
                collect_names(&a.value, out);
            }
        }
        Expr::Comprehension {
            binders,
            where_clauses,
            body,
            acc,
            ..
        } => {
            for b in binders {
                match &b.seq {
                    Seq::Expr(e) => collect_names(e, out),
                    Seq::Range { lo, hi, .. } => {
                        collect_names(lo, out);
                        collect_names(hi, out);
                    }
                }
            }
            if let Some(a) = acc {
                collect_names(&a.init, out);
            }
            for w in where_clauses {
                collect_names(w, out);
            }
            collect_names(body, out);
        }
        Expr::ArrayLit { elems, .. } => {
            for e in elems {
                collect_names(e, out);
            }
        }
        Expr::Int { .. }
        | Expr::Str { .. }
        | Expr::Duration { .. }
        | Expr::Bool { .. }
        | Expr::Member { .. } => {}
    }
}

fn decode_hex(s: &str) -> Option<Vec<u8>> {
    let h = s.strip_prefix("0x")?;
    if h.len() % 2 != 0 || !h.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    Some(
        (0..h.len() / 2)
            .map(|i| u8::from_str_radix(&h[i * 2..i * 2 + 2], 16).expect("hex"))
            .collect(),
    )
}
