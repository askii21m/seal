//! Semantic analysis, part one: names, types, provenance, check-kinds.
//!
//! Everything here is decidable at template level: externs are typed but
//! valueless (injection precedes instantiation). Const evaluation and the
//! interval engine (bounds, narrowing) come later and require instantiation
//! values.
//!
//! Rules enforced (every rule has a test):
//!
//! Names and scopes
//! - Declaration before use, no shadowing, no duplicates, no collision with
//!   the stdlib prelude. Spend scope = params + `let`s, sequential.
//! - Layout trees name spends: every spend placed (omission is an error),
//!   duplicates flagged as warnings.
//!
//! Types
//! - `Signature` is witness-only: parameters yes, `extern const` no (a
//!   signature commits to the spending tx's sighash, which cannot exist at
//!   contract-creation time; circular under SIGHASH_DEFAULT).
//! - `PublicKey` may be const OR a parameter: the witness-key airlock enforces
//!   SIZE==32 (closing the "unknown key type = auto-pass" footgun) and
//!   authorization counts only const-key signatures.
//! - `LockTime.*` values are const-only in v1: never parameters, since witness
//!   operands are vacuous unless separately constrained.
//! - Witness `Bytes<N>`: N <= 80 (relay policy); const `Bytes<N>`: N <= 520.
//! - `Hash<A> == Hash<B>` errors for A != B; `Hash<A>` compares freely with
//!   same-length `Bytes`. `Bytes` has equality, no ordering.
//! - Exactly one implicit conversion: Bool to Int 0/1 widening in arithmetic
//!   operand position. `require`/`where`/`select` conditions take `Bool` only.
//!
//! Check-kind: `after(...)` is not a value. It is legal only as a `require`
//! item in a spend; under `!`, in operators, in `let`, in `where`, or at
//! contract scope it is an error.
//!
//! Provenance: const-ness is structural. Const-required positions: `pow`
//! arguments, comprehension range bounds (unrolling), array literals,
//! `keypath:`, contract-scope `require` items, array indices.

use std::collections::BTreeMap;

use crate::diagnostics::Diagnostic;
use crate::syntax::ast::*;
use crate::syntax::span::Span;

/// Check a parsed contract. Returns diagnostics only; later phases recompute
/// facts on demand. The checker is deterministic and total, so recomputation
/// is sound.
pub fn check(contract: &Contract) -> Vec<Diagnostic> {
    analyze(contract).0
}

/// Facts the later phases need from the checker: typed extern signatures (in
/// declaration order, consumed by the args binder), const types, and the
/// spends' full parameter signatures (consumed by the path analyses).
#[derive(Debug, Clone)]
pub struct ContractInfo {
    pub externs: Vec<(String, Ty)>,
    pub consts: Vec<(String, Ty)>,
    pub spends: Vec<SpendSig>,
}

#[derive(Debug, Clone)]
pub struct SpendSig {
    pub name: String,
    pub open: bool,
    pub params: Vec<ParamSig>,
}

#[derive(Debug, Clone)]
pub struct ParamSig {
    pub name: String,
    pub ty: Ty,
    pub relaxed: bool,
}

/// Check + collect [`ContractInfo`].
pub fn analyze(contract: &Contract) -> (Vec<Diagnostic>, ContractInfo) {
    let mut cx = Checker {
        diags: Vec::new(),
        consts: BTreeMap::new(),
        spends: BTreeMap::new(),
        externs: Vec::new(),
        const_types: Vec::new(),
        spend_sigs: Vec::new(),
    };
    cx.contract(contract);
    (
        cx.diags,
        ContractInfo {
            externs: cx.externs,
            consts: cx.const_types,
            spends: cx.spend_sigs,
        },
    )
}

// --- the type model ---

/// A compile-time length: literal, or a named `const`/`extern const` Int.
/// Arbitrary const expressions in type positions await const evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Len {
    Lit(u64),
    Named(String),
}

impl Len {
    /// Lengths are equal when both are the same literal or the same name.
    /// Lit vs Named is unknown at template level (treated as equal only after
    /// const evaluation); here the comparison is conservative and rejects.
    fn same(&self, other: &Len) -> bool {
        self == other
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HashAlg {
    Sha256,
    Hash256,
    Hash160,
    Ripemd160,
    Sha1,
}

impl HashAlg {
    fn byte_len(self) -> u64 {
        match self {
            HashAlg::Sha256 | HashAlg::Hash256 => 32,
            HashAlg::Hash160 | HashAlg::Ripemd160 | HashAlg::Sha1 => 20,
        }
    }
    fn name(self) -> &'static str {
        match self {
            HashAlg::Sha256 => "Sha256",
            HashAlg::Hash256 => "Hash256",
            HashAlg::Hash160 => "Hash160",
            HashAlg::Ripemd160 => "Ripemd160",
            HashAlg::Sha1 => "Sha1",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    Bool,
    Int,
    PublicKey,
    Signature,
    Bytes(Len),
    Hash(HashAlg),
    LockTimeAbs,
    LockTimeRel,
    Array(Box<Ty>, Len),
}

impl Ty {
    fn describe(&self) -> String {
        match self {
            Ty::Bool => "Bool".into(),
            Ty::Int => "Int".into(),
            Ty::PublicKey => "PublicKey".into(),
            Ty::Signature => "Signature".into(),
            Ty::Bytes(Len::Lit(n)) => format!("Bytes<{n}>"),
            Ty::Bytes(Len::Named(n)) => format!("Bytes<{n}>"),
            Ty::Hash(a) => format!("Hash<{}>", a.name()),
            Ty::LockTimeAbs => "LockTime.Absolute".into(),
            Ty::LockTimeRel => "LockTime.Relative".into(),
            Ty::Array(t, Len::Lit(n)) => format!("[{}; {n}]", t.describe()),
            Ty::Array(t, Len::Named(n)) => format!("[{}; {n}]", t.describe()),
        }
    }
}

/// The result kind of an expression: a value, or a verify-style check
/// (`after(...)`) that composes via commas only.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Kind {
    Value(Ty),
    Check,
}

/// What a resolved name is, and what it may be used for. No declaration span
/// yet; reintroduce when diagnostics grow secondary "previously declared here"
/// labels.
#[derive(Debug, Clone)]
struct Binding {
    ty: Ty,
    is_const: bool,
    what: &'static str, // "extern const" | "const" | "parameter" | "let" | "binder" | "accumulator"
}

const STDLIB_NAMES: &[&str] = &[
    "sum",
    "count",
    "all",
    "any",
    "fold",
    "select",
    "pow",
    "min",
    "max",
    "abs",
    "int",
    "sha256",
    "hash160",
    "hash256",
    "ripemd160",
    "sha1",
    "after",
    "branch",
];

const TYPE_NAMES: &[&str] = &[
    "Int",
    "Bool",
    "Bytes",
    "Hash",
    "PublicKey",
    "Signature",
    "LockTime",
];

struct Checker {
    diags: Vec<Diagnostic>,
    /// Contract-scope bindings (externs + consts), in declaration order.
    consts: BTreeMap<String, Binding>,
    /// Spend name to (span, param count) for layout-tree resolution.
    spends: BTreeMap<String, Span>,
    /// Typed extern signatures in declaration order (for the args binder).
    externs: Vec<(String, Ty)>,
    /// Const item types in declaration order (for the path analyses).
    const_types: Vec<(String, Ty)>,
    /// Spend parameter signatures (for the path analyses).
    spend_sigs: Vec<SpendSig>,
}

/// Per-spend (or per-precondition) expression context.
struct Scope<'c> {
    cx: &'c mut Checker,
    /// Local bindings: params, lets, comprehension binders (lexical, ordered).
    locals: Vec<(String, Binding)>,
    /// True inside a spend body (vs contract scope). Gates `after()`.
    in_spend: bool,
}

impl Checker {
    fn error(&mut self, code: &'static str, msg: impl Into<String>, span: Span) {
        self.diags.push(Diagnostic::error(code, msg, span));
    }
    fn warn(&mut self, code: &'static str, msg: impl Into<String>, span: Span) {
        self.diags.push(Diagnostic::warning(code, msg, span));
    }

    fn contract(&mut self, c: &Contract) {
        // Pass 1: collect spend names (layout may precede or follow them).
        for item in &c.items {
            if let Item::Spend(s) = item
                && self
                    .spends
                    .insert(s.name.text.clone(), s.name.span)
                    .is_some()
            {
                self.error(
                    "sema/dup",
                    format!("duplicate spend `{}`", s.name.text),
                    s.name.span,
                );
            }
        }
        // Pass 2: check items in order (consts are declare-before-use).
        for item in &c.items {
            match item {
                Item::ExternConst { name, ty, span } => self.extern_const(name, ty, *span),
                Item::Const {
                    name,
                    ty,
                    value,
                    span,
                } => self.const_item(name, ty.as_ref(), value, *span),
                Item::Precondition(req) => self.precondition(req),
                Item::Spend(s) => self.spend(s),
                Item::Keypath(kp) => self.keypath(kp),
            }
        }
    }

    fn declare_const_name(&mut self, name: &Ident) -> bool {
        if STDLIB_NAMES.contains(&name.text.as_str()) || TYPE_NAMES.contains(&name.text.as_str()) {
            self.error(
                "sema/shadow-stdlib",
                format!(
                    "`{}` is a prelude/type name and cannot be redefined",
                    name.text
                ),
                name.span,
            );
            return false;
        }
        if self.consts.contains_key(&name.text) {
            self.error(
                "sema/dup",
                format!("duplicate declaration of `{}`", name.text),
                name.span,
            );
            return false;
        }
        if self.spends.contains_key(&name.text) {
            self.error(
                "sema/dup",
                format!("`{}` is already a spend name", name.text),
                name.span,
            );
            return false;
        }
        true
    }

    fn extern_const(&mut self, name: &Ident, ty: &Type, _span: Span) {
        let Ok(t) = self.resolve_type(ty, TypePosition::Const) else {
            return;
        };
        if contains_signature(&t) {
            self.error(
                "sema/extern-signature",
                "`Signature` is witness-only: it can never be a `const`; \
                 signatures arrive as spend parameters",
                ty.span,
            );
            return;
        }
        if self.declare_const_name(name) {
            self.externs.push((name.text.clone(), t.clone()));
            self.consts.insert(
                name.text.clone(),
                Binding {
                    ty: t,
                    is_const: true,
                    what: "extern const",
                },
            );
        }
    }

    fn const_item(&mut self, name: &Ident, ty: Option<&Type>, value: &Expr, _span: Span) {
        let mut scope = Scope {
            cx: self,
            locals: Vec::new(),
            in_spend: false,
        };
        let inferred = scope.expr(value);
        let declared = ty.map(|t| self.resolve_type(t, TypePosition::Const));
        let final_ty = match (declared, inferred) {
            (Some(Ok(d)), Ok((Kind::Value(i), is_const))) => {
                if !ty_compatible(&d, &i) {
                    self.error(
                        "sema/type-mismatch",
                        format!(
                            "const `{}` is declared `{}` but its value is `{}`",
                            name.text,
                            d.describe(),
                            i.describe()
                        ),
                        value.span(),
                    );
                }
                if !is_const {
                    self.error(
                        "sema/const-needs-const",
                        format!("the value of const `{}` must itself be const", name.text),
                        value.span(),
                    );
                }
                d
            }
            (None, Ok((Kind::Value(i), is_const))) => {
                if !is_const {
                    self.error(
                        "sema/const-needs-const",
                        format!("the value of const `{}` must itself be const", name.text),
                        value.span(),
                    );
                }
                i
            }
            (_, Ok((Kind::Check, _))) => {
                self.error(
                    "sema/check-position",
                    "`after(...)` is a spend-path check, not a value",
                    value.span(),
                );
                return;
            }
            _ => return, // already diagnosed
        };
        if contains_signature(&final_ty) {
            self.error(
                "sema/extern-signature",
                "`Signature` is witness-only: it can never be a `const`",
                name.span,
            );
            return;
        }
        if self.declare_const_name(name) {
            self.const_types.push((name.text.clone(), final_ty.clone()));
            self.consts.insert(
                name.text.clone(),
                Binding {
                    ty: final_ty,
                    is_const: true,
                    what: "const",
                },
            );
        }
    }

    fn precondition(&mut self, req: &RequireStmt) {
        let mut scope = Scope {
            cx: self,
            locals: Vec::new(),
            in_spend: false,
        };
        for item in &req.items {
            match scope.expr(item) {
                Ok((Kind::Value(Ty::Bool), true)) => {}
                Ok((Kind::Value(Ty::Bool), false)) => {
                    scope.cx.error(
                        "sema/precondition-const",
                        "a contract-scope `require` is a template precondition: it must be a \
                         const expression, checked at instantiation",
                        item.span(),
                    );
                }
                Ok((Kind::Value(other), _)) => {
                    scope.cx.error(
                        "sema/require-bool",
                        format!(
                            "a require item must be `Bool`, found `{}`",
                            other.describe()
                        ),
                        item.span(),
                    );
                }
                Ok((Kind::Check, _)) => {
                    scope.cx.error(
                        "sema/check-position",
                        "`after(...)` belongs in a spend's require: a template \
                         precondition has no spend path",
                        item.span(),
                    );
                }
                Err(()) => {}
            }
        }
    }

    fn spend(&mut self, s: &Spend) {
        let mut sig = SpendSig {
            name: s.name.text.clone(),
            open: s.open,
            params: Vec::new(),
        };
        let mut scope = Scope {
            cx: self,
            locals: Vec::new(),
            in_spend: true,
        };
        for p in &s.params {
            if let Some(ty) = scope.param(p) {
                sig.params.push(ParamSig {
                    name: p.name.text.clone(),
                    ty,
                    relaxed: p.relaxed,
                });
            }
        }
        for stmt in &s.body {
            scope.stmt(stmt);
        }
        self.spend_sigs.push(sig);
    }

    fn keypath(&mut self, kp: &Keypath) {
        match kp {
            Keypath::None(_) => {}
            Keypath::Key(expr) => {
                let mut scope = Scope {
                    cx: self,
                    locals: Vec::new(),
                    in_spend: false,
                };
                match scope.expr(expr) {
                    Ok((Kind::Value(Ty::PublicKey), true)) => {}
                    Ok((Kind::Value(Ty::PublicKey), false)) => self.error(
                        "sema/keypath-const",
                        "the keypath must be a const `PublicKey` expression",
                        expr.span(),
                    ),
                    Ok((Kind::Value(other), _)) => self.error(
                        "sema/type-mismatch",
                        format!(
                            "`keypath` takes a `PublicKey`, found `{}`",
                            other.describe()
                        ),
                        expr.span(),
                    ),
                    Ok((Kind::Check, _)) => self.error(
                        "sema/check-position",
                        "`after(...)` is not a value",
                        expr.span(),
                    ),
                    Err(()) => {}
                }
            }
        }
    }

    // --- types ---

    fn resolve_type(&mut self, ty: &Type, pos: TypePosition) -> Result<Ty, ()> {
        match &ty.kind {
            TypeKind::Array { elem, len } => {
                let e = self.resolve_type(elem, pos)?;
                let l = self.resolve_len(len)?;
                Ok(Ty::Array(Box::new(e), l))
            }
            TypeKind::Path { segments, args } => {
                self.resolve_path_type(segments, args, ty.span, pos)
            }
        }
    }

    fn resolve_path_type(
        &mut self,
        segments: &[Ident],
        args: &[Expr],
        span: Span,
        pos: TypePosition,
    ) -> Result<Ty, ()> {
        let no_args = |cx: &mut Checker, name: &str| {
            if !args.is_empty() {
                cx.error(
                    "sema/type-args",
                    format!("`{name}` takes no type arguments"),
                    span,
                );
                return Err(());
            }
            Ok(())
        };
        match segments {
            [one] => match one.text.as_str() {
                "Int" => {
                    no_args(self, "Int")?;
                    Ok(Ty::Int)
                }
                "Bool" => {
                    no_args(self, "Bool")?;
                    Ok(Ty::Bool)
                }
                "PublicKey" => {
                    no_args(self, "PublicKey")?;
                    // Witness keys are allowed: the airlock enforces SIZE==32
                    // (never elided; a non-32 key in sig position would be
                    // "unknown key type = check auto-passes"), and a check()
                    // against a witness key does not confer theft-resistance
                    // (authorization counts const keys only). Legitimate
                    // pattern: hash-committed delegation.
                    Ok(Ty::PublicKey)
                }
                "Signature" => {
                    no_args(self, "Signature")?;
                    Ok(Ty::Signature)
                }
                "Bytes" => {
                    let [len] = args else {
                        self.error(
                            "sema/type-args",
                            "`Bytes<N>` takes exactly one length",
                            span,
                        );
                        return Err(());
                    };
                    let l = self.resolve_len(len)?;
                    if let Len::Lit(n) = l {
                        let cap = if pos == TypePosition::Param { 80 } else { 520 };
                        let why = if pos == TypePosition::Param {
                            "witness items are capped at 80 bytes by relay policy"
                        } else {
                            "stack elements are capped at 520 bytes by consensus"
                        };
                        if n > cap {
                            self.error(
                                "sema/bytes-cap",
                                format!("`Bytes<{n}>` exceeds {cap}: {why}"),
                                span,
                            );
                            return Err(());
                        }
                        if n == 0 {
                            self.error("sema/bytes-cap", "`Bytes<0>` is not a useful type", span);
                            return Err(());
                        }
                    }
                    Ok(Ty::Bytes(l))
                }
                "Hash" => {
                    let [alg] = args else {
                        self.error(
                            "sema/type-args",
                            "`Hash<Alg>` takes exactly one algorithm",
                            span,
                        );
                        return Err(());
                    };
                    let Expr::Name(alg_name) = alg else {
                        self.error(
                            "sema/type-args",
                            "`Hash<Alg>`: Alg must be an algorithm name",
                            alg.span(),
                        );
                        return Err(());
                    };
                    let alg = match alg_name.text.as_str() {
                        "Sha256" => HashAlg::Sha256,
                        "Hash256" => HashAlg::Hash256,
                        "Hash160" => HashAlg::Hash160,
                        "Ripemd160" => HashAlg::Ripemd160,
                        "Sha1" => {
                            self.warn(
                                "sema/sha1",
                                "SHA-1 is collision-broken; use only for legacy puzzles",
                                alg_name.span,
                            );
                            HashAlg::Sha1
                        }
                        other => {
                            self.error(
                                "sema/type-unknown",
                                format!(
                                    "unknown hash algorithm `{other}` (Sha256, Hash256, \
                                     Hash160, Ripemd160, Sha1)"
                                ),
                                alg_name.span,
                            );
                            return Err(());
                        }
                    };
                    Ok(Ty::Hash(alg))
                }
                other => {
                    self.error("sema/type-unknown", format!("unknown type `{other}`"), span);
                    Err(())
                }
            },
            [base, variant] if base.text == "LockTime" => {
                no_args(self, "LockTime")?;
                if pos == TypePosition::Param {
                    self.error(
                        "sema/witness-locktime",
                        "`LockTime` values are const-only in v1",
                        span,
                    );
                    return Err(());
                }
                match variant.text.as_str() {
                    "Absolute" => Ok(Ty::LockTimeAbs),
                    "Relative" => Ok(Ty::LockTimeRel),
                    other => {
                        self.error(
                            "sema/type-unknown",
                            format!("unknown `LockTime.{other}` (Absolute, Relative)"),
                            span,
                        );
                        Err(())
                    }
                }
            }
            _ => {
                self.error("sema/type-unknown", "unknown type path", span);
                Err(())
            }
        }
    }

    /// A type-position length: an integer literal or a named const Int.
    fn resolve_len(&mut self, e: &Expr) -> Result<Len, ()> {
        match e {
            Expr::Int { text, span } => match parse_int_text(text) {
                Some(v) if v <= u64::MAX as u128 => Ok(Len::Lit(v as u64)),
                _ => {
                    self.error("sema/len", "length literal out of range", *span);
                    Err(())
                }
            },
            Expr::Name(name) => {
                match self.consts.get(&name.text) {
                    Some(b) if b.ty == Ty::Int && b.is_const => Ok(Len::Named(name.text.clone())),
                    Some(b) => {
                        let (msg, span) = (
                            format!(
                                "`{}` is a {} of type `{}`: a length must be a const `Int`",
                                name.text,
                                b.what,
                                b.ty.describe()
                            ),
                            name.span,
                        );
                        self.error("sema/len", msg, span);
                        Err(())
                    }
                    Option::None => {
                        self.error(
                        "sema/unresolved",
                        format!("`{}` is not declared (lengths resolve against consts declared above)", name.text),
                        name.span,
                    );
                        Err(())
                    }
                }
            }
            other => {
                self.error(
                    "sema/len-unsupported",
                    "type-position lengths are an integer literal or a const name \
                     (general const expressions await const evaluation)",
                    other.span(),
                );
                Err(())
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypePosition {
    Param,
    Const,
}

// --- expression checking (scoped) ---

impl<'c> Scope<'c> {
    fn lookup(&self, name: &str) -> Option<&Binding> {
        self.locals
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, b)| b)
            .or_else(|| self.cx.consts.get(name))
    }

    fn declare_local(&mut self, name: &Ident, b: Binding) {
        if STDLIB_NAMES.contains(&name.text.as_str()) || TYPE_NAMES.contains(&name.text.as_str()) {
            self.cx.error(
                "sema/shadow-stdlib",
                format!(
                    "`{}` is a prelude/type name and cannot be redefined",
                    name.text
                ),
                name.span,
            );
            return;
        }
        if self.lookup(&name.text).is_some() || self.cx.spends.contains_key(&name.text) {
            self.cx.error(
                "sema/shadow",
                format!(
                    "`{}` is already in scope; shadowing is not allowed",
                    name.text
                ),
                name.span,
            );
            return;
        }
        self.locals.push((name.text.clone(), b));
    }

    fn param(&mut self, p: &Param) -> Option<Ty> {
        let Ok(ty) = self.cx.resolve_type(&p.ty, TypePosition::Param) else {
            return None;
        };
        self.declare_local(
            &p.name,
            Binding {
                ty: ty.clone(),
                is_const: false,
                what: "parameter",
            },
        );
        Some(ty)
    }

    fn stmt(&mut self, s: &Stmt) {
        match s {
            Stmt::Let { name, value, .. } => match self.expr(value) {
                Ok((Kind::Value(ty), is_const)) => self.declare_local(
                    name,
                    Binding {
                        ty,
                        is_const,
                        what: "let",
                    },
                ),
                Ok((Kind::Check, _)) => self.cx.error(
                    "sema/check-position",
                    "`after(...)` is a check, not a value; it cannot be bound",
                    value.span(),
                ),
                Err(()) => {}
            },
            Stmt::Require(req) => {
                for item in &req.items {
                    match self.expr(item) {
                        Ok((Kind::Value(Ty::Bool), _)) | Ok((Kind::Check, _)) => {}
                        Ok((Kind::Value(other), _)) => self.cx.error(
                            "sema/require-bool",
                            format!(
                                "a require item must be `Bool` (or a timelock check), \
                                 found `{}`",
                                other.describe()
                            ),
                            item.span(),
                        ),
                        Err(()) => {}
                    }
                }
            }
        }
    }

    /// Check an expression: its kind (value/check) and const-ness.
    fn expr(&mut self, e: &Expr) -> Result<(Kind, bool), ()> {
        match e {
            Expr::Int { text, span } => {
                if parse_int_text(text).is_none() {
                    self.cx
                        .error("sema/int", "integer literal out of supported range", *span);
                    return Err(());
                }
                Ok((Kind::Value(Ty::Int), true))
            }
            Expr::Bool { .. } => Ok((Kind::Value(Ty::Bool), true)),
            Expr::Str { span, .. } => {
                self.cx.error(
                    "sema/str-position",
                    "string literals exist only as typed-constructor arguments \
                     (`PublicKey(\"0x...\")`, `LockTime.Absolute(time: \"...\")`)",
                    *span,
                );
                Err(())
            }
            Expr::Duration { span, .. } => {
                self.cx.error(
                    "sema/duration-position",
                    "span literals were replaced by ISO-8601 duration strings; \
                     write `LockTime.Relative(time: \"P90D\")`",
                    *span,
                );
                Err(())
            }
            Expr::Name(name) => self.name(name),
            Expr::ArrayLit { elems, span } => self.array_lit(elems, *span),
            Expr::Unary { op, operand, span } => self.unary(*op, operand, *span),
            Expr::Binary { op, lhs, rhs, span } => self.binary(*op, lhs, rhs, *span),
            Expr::Compare { first, rest, span } => self.compare(first, rest, *span),
            Expr::In { value, lo, hi, .. } => self.in_range(value, lo, hi),
            Expr::Index { base, index, span } => self.index(base, index, *span),
            Expr::Member { base, member, span } => {
                // A bare member access (no call) is never a value in v1.
                let _ = (base, member);
                self.cx.error(
                    "sema/member",
                    "member access is only used in calls (`key.check(sig)`, \
                     `PublicKey.MuSig2(...)`, `LockTime.Absolute(...)`)",
                    *span,
                );
                Err(())
            }
            Expr::Call { callee, args, span } => self.call(callee, args, *span),
            Expr::Comprehension {
                callee,
                acc,
                binders,
                where_clauses,
                body,
                span,
            } => self.comprehension(callee, acc.as_ref(), binders, where_clauses, body, *span),
            Expr::TypedCtor { ty, args, span } => self.typed_ctor(ty, args, *span),
        }
    }

    fn name(&mut self, name: &Ident) -> Result<(Kind, bool), ()> {
        if let Some(b) = self.lookup(&name.text) {
            // Const-required positions (keypath, preconditions, const inits,
            // pow, range bounds, indices) enforce const-ness at their level;
            // a name lookup never needs to.
            return Ok((Kind::Value(b.ty.clone()), b.is_const));
        }
        if TYPE_NAMES.contains(&name.text.as_str()) {
            self.cx.error(
                "sema/type-as-value",
                format!("`{}` is a type, not a value", name.text),
                name.span,
            );
            return Err(());
        }
        if STDLIB_NAMES.contains(&name.text.as_str()) {
            self.cx.error(
                "sema/fn-as-value",
                format!("`{}` is a function, call it", name.text),
                name.span,
            );
            return Err(());
        }
        if self.cx.spends.contains_key(&name.text) {
            self.cx.error(
                "sema/spend-as-value",
                format!(
                    "`{}` is a spend; it is referenced only in the layout tree",
                    name.text
                ),
                name.span,
            );
            return Err(());
        }
        self.cx.error(
            "sema/unresolved",
            format!("`{}` is not declared", name.text),
            name.span,
        );
        Err(())
    }

    fn array_lit(&mut self, elems: &[Expr], span: Span) -> Result<(Kind, bool), ()> {
        let mut elem_ty: Option<Ty> = None;
        let mut all_const = true;
        for e in elems {
            let (k, c) = self.expr(e)?;
            let Kind::Value(t) = k else {
                self.cx.error(
                    "sema/check-position",
                    "`after(...)` is not a value",
                    e.span(),
                );
                return Err(());
            };
            all_const &= c;
            match &elem_ty {
                Option::None => elem_ty = Some(t),
                Some(prev) if ty_compatible(prev, &t) => {}
                Some(prev) => {
                    self.cx.error(
                        "sema/type-mismatch",
                        format!(
                            "array elements must share one type: `{}` vs `{}`",
                            prev.describe(),
                            t.describe()
                        ),
                        e.span(),
                    );
                    return Err(());
                }
            }
        }
        if !all_const {
            self.cx
                .error("sema/array-const", "array literals are const-only", span);
            return Err(());
        }
        let ty = Ty::Array(
            Box::new(elem_ty.expect("parser rejects empty")),
            Len::Lit(elems.len() as u64),
        );
        Ok((Kind::Value(ty), true))
    }

    fn unary(&mut self, op: UnaryOp, operand: &Expr, _span: Span) -> Result<(Kind, bool), ()> {
        let (k, c) = self.expr(operand)?;
        match (op, k) {
            (UnaryOp::Not, Kind::Value(Ty::Bool)) => Ok((Kind::Value(Ty::Bool), c)),
            (UnaryOp::Neg, Kind::Value(Ty::Int)) => Ok((Kind::Value(Ty::Int), c)),
            (UnaryOp::Neg, Kind::Value(Ty::Bool)) => {
                self.cx.error(
                    "sema/type-mismatch",
                    "unary `-` takes `Int` (Bool widens only in binary arithmetic position)",
                    operand.span(),
                );
                Err(())
            }
            (_, Kind::Check) => {
                self.cx.error(
                    "sema/check-position",
                    "a timelock cannot be negated or operated on; it composes via commas \
                     only",
                    operand.span(),
                );
                Err(())
            }
            (op, Kind::Value(t)) => {
                let what = if op == UnaryOp::Not {
                    "`!` takes `Bool`"
                } else {
                    "unary `-` takes `Int`"
                };
                self.cx.error(
                    "sema/type-mismatch",
                    format!("{what}, found `{}`", t.describe()),
                    operand.span(),
                );
                Err(())
            }
        }
    }

    /// Arithmetic operand: Int, or Bool widened (the one implicit conversion).
    fn arith_operand(&mut self, e: &Expr) -> Result<bool, ()> {
        let (k, c) = self.expr(e)?;
        match k {
            Kind::Value(Ty::Int) | Kind::Value(Ty::Bool) => Ok(c),
            Kind::Check => {
                self.cx.error(
                    "sema/check-position",
                    "a timelock cannot appear in arithmetic; it composes via commas only",
                    e.span(),
                );
                Err(())
            }
            Kind::Value(t) => {
                self.cx.error(
                    "sema/type-mismatch",
                    format!(
                        "arithmetic takes `Int` (or `Bool`, widened 0/1), found `{}`",
                        t.describe()
                    ),
                    e.span(),
                );
                Err(())
            }
        }
    }

    fn binary(
        &mut self,
        _op: BinaryOp,
        lhs: &Expr,
        rhs: &Expr,
        _span: Span,
    ) -> Result<(Kind, bool), ()> {
        let lc = self.arith_operand(lhs);
        let rc = self.arith_operand(rhs);
        Ok((Kind::Value(Ty::Int), lc? && rc?))
    }

    fn compare(
        &mut self,
        first: &Expr,
        rest: &[(CmpOp, Expr)],
        _span: Span,
    ) -> Result<(Kind, bool), ()> {
        debug_assert!(!rest.is_empty());
        // Ordering chains are Int-domain (with Bool widening). Equality pairs
        // dispatch on type class.
        let only_eq = rest.len() == 1 && matches!(rest[0].0, CmpOp::Eq | CmpOp::Ne);
        if only_eq {
            let (lk, lc) = self.expr(first)?;
            let (rk, rc) = self.expr(&rest[0].1)?;
            let (Kind::Value(lt), Kind::Value(rt)) = (lk, rk) else {
                let span = first.span();
                self.cx
                    .error("sema/check-position", "a timelock cannot be compared", span);
                return Err(());
            };
            self.eq_compatible(&lt, &rt, rest[0].1.span())?;
            return Ok((Kind::Value(Ty::Bool), lc && rc));
        }
        let mut all_const = self.arith_operand(first)?;
        for (op, e) in rest {
            if matches!(op, CmpOp::Eq | CmpOp::Ne) {
                // Parser allows == only as a single pair; defensive here.
                self.cx
                    .error("sema/chain-eq", "`==`/`!=` do not chain", e.span());
                return Err(());
            }
            all_const &= self.arith_operand(e)?;
        }
        Ok((Kind::Value(Ty::Bool), all_const))
    }

    /// Equality classes: Int (NUMEQUAL); Bool; Bytes/Hash byte equality with
    /// one-way Hash-to-Bytes compatibility and Hash<A> != Hash<B>.
    fn eq_compatible(&mut self, l: &Ty, r: &Ty, span: Span) -> Result<(), ()> {
        let ok = match (l, r) {
            (Ty::Int, Ty::Int) | (Ty::Bool, Ty::Bool) => true,
            (Ty::Int, Ty::Bool) | (Ty::Bool, Ty::Int) => true, // widening
            (Ty::Bytes(a), Ty::Bytes(b)) => {
                if !a.same(b) {
                    self.cx.error(
                        "sema/type-mismatch",
                        format!(
                            "byte-equality of different lengths is always false: `{}` vs `{}`",
                            l.describe(),
                            r.describe()
                        ),
                        span,
                    );
                    return Err(());
                }
                true
            }
            (Ty::Hash(a), Ty::Hash(b)) => {
                if a != b {
                    self.cx.error(
                        "sema/hash-mix",
                        format!(
                            "`Hash<{}> == Hash<{}>` is a compile error: different \
                             algorithms never match",
                            a.name(),
                            b.name()
                        ),
                        span,
                    );
                    return Err(());
                }
                true
            }
            (Ty::Hash(a), Ty::Bytes(b)) | (Ty::Bytes(b), Ty::Hash(a)) => {
                if let Len::Lit(n) = b
                    && *n != a.byte_len()
                {
                    self.cx.error(
                        "sema/type-mismatch",
                        format!(
                            "`Hash<{}>` is {} bytes; comparing with `Bytes<{n}>` is \
                                 always false",
                            a.name(),
                            a.byte_len()
                        ),
                        span,
                    );
                    return Err(());
                }
                true
            }
            _ => false,
        };
        if ok {
            Ok(())
        } else {
            self.cx.error(
                "sema/type-mismatch",
                format!(
                    "`==` between `{}` and `{}` is not defined",
                    l.describe(),
                    r.describe()
                ),
                span,
            );
            Err(())
        }
    }

    fn in_range(&mut self, value: &Expr, lo: &Expr, hi: &Expr) -> Result<(Kind, bool), ()> {
        let vc = self.arith_operand(value);
        let lc = self.arith_operand(lo);
        let hc = self.arith_operand(hi);
        Ok((Kind::Value(Ty::Bool), vc? && lc? && hc?))
    }

    fn index(&mut self, base: &Expr, index: &Expr, span: Span) -> Result<(Kind, bool), ()> {
        let (bk, bc) = self.expr(base)?;
        let Kind::Value(Ty::Array(elem, _)) = bk else {
            let t = match bk {
                Kind::Value(t) => t.describe(),
                Kind::Check => "a timelock check".into(),
            };
            self.cx.error(
                "sema/type-mismatch",
                format!("only arrays index, found `{t}`"),
                span,
            );
            return Err(());
        };
        let (ik, ic) = self.expr(index)?;
        if !matches!(ik, Kind::Value(Ty::Int)) {
            self.cx.error(
                "sema/type-mismatch",
                "array index must be `Int`",
                index.span(),
            );
            return Err(());
        }
        if !ic {
            self.cx.error(
                "sema/index-const",
                "array indices are const: there is no runtime indexing on a stack machine; \
                 runtime selection is a comprehension",
                index.span(),
            );
            return Err(());
        }
        Ok((Kind::Value(*elem), bc))
    }

    // --- calls ---

    fn call(&mut self, callee: &Expr, args: &[Arg], span: Span) -> Result<(Kind, bool), ()> {
        match callee {
            Expr::Name(name) => self.call_named(name, args, span),
            Expr::Member { base, member, .. } => self.call_member(base, member, args, span),
            other => {
                self.cx
                    .error("sema/call", "this expression is not callable", other.span());
                Err(())
            }
        }
    }

    fn positional(&mut self, args: &[Arg], n: usize, what: &str, span: Span) -> Result<(), ()> {
        if args.len() != n || args.iter().any(|a| a.label.is_some()) {
            self.cx.error(
                "sema/args",
                format!(
                    "`{what}` takes exactly {n} positional argument{}",
                    if n == 1 { "" } else { "s" }
                ),
                span,
            );
            return Err(());
        }
        Ok(())
    }

    fn int_arg(&mut self, e: &Expr) -> Result<bool, ()> {
        self.arith_operand(e)
    }

    fn call_named(&mut self, name: &Ident, args: &[Arg], span: Span) -> Result<(Kind, bool), ()> {
        match name.text.as_str() {
            "min" | "max" => {
                self.positional(args, 2, &name.text, span)?;
                let a = self.int_arg(&args[0].value);
                let b = self.int_arg(&args[1].value);
                Ok((Kind::Value(Ty::Int), a? && b?))
            }
            "abs" | "int" => {
                self.positional(args, 1, &name.text, span)?;
                let c = if name.text == "int" {
                    let (k, c) = self.expr(&args[0].value)?;
                    if !matches!(k, Kind::Value(Ty::Bool)) {
                        self.cx.error(
                            "sema/type-mismatch",
                            "`int(b)` takes `Bool`",
                            args[0].value.span(),
                        );
                        return Err(());
                    }
                    c
                } else {
                    self.int_arg(&args[0].value)?
                };
                Ok((Kind::Value(Ty::Int), c))
            }
            "mul" | "div" | "mod" => {
                self.cx.error(
                    "sema/no-muldiv",
                    "multiplication and division are not available in v1: every witness \
                     element must be a declared parameter, and a variable-by-variable \
                     mul/div needs hidden witness hints. Use add chains for constant scaling.",
                    span,
                );
                Err(())
            }
            "pow" => {
                self.positional(args, 2, "pow", span)?;
                let a = self.int_arg(&args[0].value);
                let b = self.int_arg(&args[1].value);
                let (a, b) = (a?, b?);
                if !(a && b) {
                    self.cx.error(
                        "sema/pow-const",
                        "`pow(base, exp)` requires constant base and exponent",
                        span,
                    );
                    return Err(());
                }
                Ok((Kind::Value(Ty::Int), true))
            }
            "sha256" | "hash256" | "hash160" | "ripemd160" | "sha1" => {
                self.positional(args, 1, &name.text, span)?;
                if name.text == "sha1" {
                    self.cx.warn("sema/sha1", "SHA-1 is collision-broken", span);
                }
                let (k, c) = self.expr(&args[0].value)?;
                match k {
                    // Keys are 32-byte data and hashable, required by the
                    // hash-committed delegation pattern.
                    Kind::Value(Ty::Bytes(_))
                    | Kind::Value(Ty::Hash(_))
                    | Kind::Value(Ty::PublicKey) => {}
                    Kind::Value(t) => {
                        self.cx.error(
                            "sema/type-mismatch",
                            format!(
                                "hash intrinsics take byte data (`Bytes`/`Hash`/`PublicKey`; \
                                 no Int-to-Bytes in v1), found `{}`",
                                t.describe()
                            ),
                            args[0].value.span(),
                        );
                        return Err(());
                    }
                    Kind::Check => {
                        self.cx
                            .error("sema/check-position", "a timelock is not hashable", span);
                        return Err(());
                    }
                }
                let alg = match name.text.as_str() {
                    "sha256" => HashAlg::Sha256,
                    "hash256" => HashAlg::Hash256,
                    "hash160" => HashAlg::Hash160,
                    "ripemd160" => HashAlg::Ripemd160,
                    _ => HashAlg::Sha1,
                };
                Ok((Kind::Value(Ty::Hash(alg)), c))
            }
            "select" => self.select(args, span),
            "after" => {
                if !self.in_spend {
                    self.cx.error(
                        "sema/check-position",
                        "`after(...)` is a spend-path check; it belongs in a spend's \
                         require",
                        span,
                    );
                    return Err(());
                }
                self.positional(args, 1, "after", span)?;
                let (k, c) = self.expr(&args[0].value)?;
                match k {
                    Kind::Value(Ty::LockTimeAbs) | Kind::Value(Ty::LockTimeRel) => {
                        if !c {
                            self.cx.error(
                                "sema/locktime-const",
                                "`LockTime` values are const-only in v1",
                                args[0].value.span(),
                            );
                            return Err(());
                        }
                        Ok((Kind::Check, true))
                    }
                    Kind::Value(t) => {
                        self.cx.error(
                            "sema/type-mismatch",
                            format!(
                                "`after(...)` takes a `LockTime.Absolute` or `LockTime.Relative`, \
                                 found `{}`",
                                t.describe()
                            ),
                            args[0].value.span(),
                        );
                        Err(())
                    }
                    Kind::Check => Err(()),
                }
            }
            "sum" | "count" | "all" | "any" | "fold" => {
                self.cx.error(
                    "sema/comp-form",
                    format!(
                        "`{}` uses comprehension form: `{}(x in xs => ...)`",
                        name.text, name.text
                    ),
                    span,
                );
                Err(())
            }
            "PublicKey" => {
                // PublicKey("0x...") is the one generic-free literal constructor.
                self.positional(args, 1, "PublicKey", span)?;
                let Expr::Str { text, span: s } = &args[0].value else {
                    self.cx.error(
                        "sema/args",
                        "`PublicKey(...)` takes a hex string literal",
                        args[0].value.span(),
                    );
                    return Err(());
                };
                if !is_hex_literal(text, 32) {
                    self.cx.error(
                        "sema/key-literal",
                        "a `PublicKey` literal is `\"0x\"` + exactly 64 hex digits \
                         (32-byte x-only key)",
                        *s,
                    );
                    return Err(());
                }
                Ok((Kind::Value(Ty::PublicKey), true))
            }
            "branch" => {
                self.cx.error(
                    "sema/branch-position",
                    "`branch(...)` exists only in the layout `script:` tree",
                    span,
                );
                Err(())
            }
            _ => {
                // Not a stdlib function: calling a value/const is meaningless.
                self.cx.error(
                    "sema/call",
                    format!("`{}` is not a function", name.text),
                    name.span,
                );
                Err(())
            }
        }
    }

    /// `Bytes<32>("0x...")` / `Hash<Sha256>("0x...")`: literal constructors for
    /// fixed-length byte data. The hex length must match the type exactly.
    fn typed_ctor(&mut self, ty: &Type, args: &[Arg], span: Span) -> Result<(Kind, bool), ()> {
        let resolved = self.cx.resolve_type(ty, TypePosition::Const)?;
        let expected_len = match &resolved {
            Ty::Bytes(Len::Lit(n)) => *n,
            Ty::Hash(alg) => alg.byte_len(),
            Ty::Bytes(Len::Named(_)) => {
                self.cx.error(
                    "sema/ctor-len",
                    "a `Bytes` literal constructor needs a literal length \
                     (`Bytes<32>(\"0x...\")`); a named length has no value at template level",
                    ty.span,
                );
                return Err(());
            }
            other => {
                self.cx.error(
                    "sema/ctor-type",
                    format!("`{}` has no literal constructor", other.describe()),
                    ty.span,
                );
                return Err(());
            }
        };
        self.positional(args, 1, "the constructor", span)?;
        let Expr::Str { text, span: s } = &args[0].value else {
            self.cx.error(
                "sema/ctor-arg",
                "a byte-data constructor takes one hex string literal (`\"0x...\"`)",
                args[0].value.span(),
            );
            return Err(());
        };
        if !is_hex_literal(text, expected_len as usize) {
            self.cx.error(
                "sema/ctor-hex",
                format!(
                    "`{}` needs `\"0x\"` + exactly {} hex digits ({} bytes)",
                    resolved.describe(),
                    expected_len * 2,
                    expected_len
                ),
                *s,
            );
            return Err(());
        }
        Ok((Kind::Value(resolved), true))
    }

    fn select(&mut self, args: &[Arg], span: Span) -> Result<(Kind, bool), ()> {
        // select(cond, then: a, else: b): labels mandatory.
        let shape_ok = args.len() == 3
            && args[0].label.is_none()
            && args[1].label.as_ref().is_some_and(|l| l.text == "then")
            && args[2].label.as_ref().is_some_and(|l| l.text == "else");
        if !shape_ok {
            self.cx.error(
                "sema/select-shape",
                "`select` is `select(cond, then: a, else: b)`; labels are mandatory \
                 (no arm-order bugs)",
                span,
            );
            return Err(());
        }
        let (ck, cc) = self.expr(&args[0].value)?;
        if !matches!(ck, Kind::Value(Ty::Bool)) {
            self.cx.error(
                "sema/type-mismatch",
                "`select` condition must be `Bool`",
                args[0].value.span(),
            );
            return Err(());
        }
        let (tk, tc) = self.expr(&args[1].value)?;
        let (ek, ec) = self.expr(&args[2].value)?;
        let (Kind::Value(tt), Kind::Value(et)) = (tk, ek) else {
            self.cx
                .error("sema/check-position", "a timelock cannot be selected", span);
            return Err(());
        };
        if !ty_compatible(&tt, &et) {
            self.cx.error(
                "sema/type-mismatch",
                format!(
                    "`select` arms must match: `{}` vs `{}`",
                    tt.describe(),
                    et.describe()
                ),
                span,
            );
            return Err(());
        }
        Ok((Kind::Value(tt), cc && tc && ec))
    }

    fn call_member(
        &mut self,
        base: &Expr,
        member: &Ident,
        args: &[Arg],
        span: Span,
    ) -> Result<(Kind, bool), ()> {
        // Static constructors: PublicKey.MuSig2, LockTime.Absolute/Relative.
        if let Expr::Name(type_name) = base {
            match (type_name.text.as_str(), member.text.as_str()) {
                ("PublicKey", "MuSig2") => {
                    self.positional(args, 1, "PublicKey.MuSig2", span)?;
                    let (k, c) = self.expr(&args[0].value)?;
                    match k {
                        Kind::Value(Ty::Array(elem, _)) if *elem == Ty::PublicKey => {
                            if !c {
                                self.cx.error(
                                    "sema/keypath-const",
                                    "MuSig2 aggregates const keys",
                                    args[0].value.span(),
                                );
                                return Err(());
                            }
                            return Ok((Kind::Value(Ty::PublicKey), true));
                        }
                        Kind::Value(t) => {
                            self.cx.error(
                                "sema/type-mismatch",
                                format!(
                                    "`PublicKey.MuSig2` takes `[PublicKey; n]`, found `{}`",
                                    t.describe()
                                ),
                                args[0].value.span(),
                            );
                            return Err(());
                        }
                        Kind::Check => return Err(()),
                    }
                }
                ("LockTime", variant @ ("Absolute" | "Relative")) => {
                    return self.locktime_ctor(variant, args, span);
                }
                ("LockTime", other) => {
                    self.cx.error(
                        "sema/type-unknown",
                        format!("unknown `LockTime.{other}` (Absolute, Relative)"),
                        member.span,
                    );
                    return Err(());
                }
                _ => {}
            }
            if TYPE_NAMES.contains(&type_name.text.as_str()) {
                self.cx.error(
                    "sema/member",
                    format!(
                        "`{}` has no associated function `{}`",
                        type_name.text, member.text
                    ),
                    member.span,
                );
                return Err(());
            }
        }

        // The one method: key.check(sig).
        if member.text == "check" {
            let (bk, _) = self.expr(base)?;
            if !matches!(bk, Kind::Value(Ty::PublicKey)) {
                let t = match bk {
                    Kind::Value(t) => t.describe(),
                    Kind::Check => "a timelock check".into(),
                };
                self.cx.error(
                    "sema/type-mismatch",
                    format!("`.check(sig)` is a `PublicKey` method, found `{t}`"),
                    base.span(),
                );
                return Err(());
            }
            self.positional(args, 1, "check", span)?;
            let (ak, _) = self.expr(&args[0].value)?;
            if !matches!(ak, Kind::Value(Ty::Signature)) {
                let t = match ak {
                    Kind::Value(t) => t.describe(),
                    Kind::Check => "a timelock check".into(),
                };
                self.cx.error(
                    "sema/type-mismatch",
                    format!("`check` takes a `Signature`, found `{t}`"),
                    args[0].value.span(),
                );
                return Err(());
            }
            // check() is never const: it verifies a witness signature.
            return Ok((Kind::Value(Ty::Bool), false));
        }

        self.cx.error(
            "sema/member",
            format!(
                "unknown method `{}` (the only method is `key.check(sig)`)",
                member.text
            ),
            member.span,
        );
        Err(())
    }

    fn locktime_ctor(
        &mut self,
        variant: &str,
        args: &[Arg],
        span: Span,
    ) -> Result<(Kind, bool), ()> {
        let (label, value) = match args {
            [
                Arg {
                    label: Some(l),
                    value,
                },
            ] => (l, value),
            _ => {
                self.cx.error(
                    "sema/args",
                    format!(
                        "`LockTime.{variant}` takes exactly one labeled argument \
                         ({})",
                        if variant == "Absolute" {
                            "`height:` or `time:`"
                        } else {
                            "`blocks:` or `time:`"
                        }
                    ),
                    span,
                );
                return Err(());
            }
        };
        let ok = match (variant, label.text.as_str()) {
            ("Absolute", "height") | ("Relative", "blocks") => {
                let c = self.int_arg(value)?;
                if !c {
                    self.cx.error(
                        "sema/locktime-const",
                        "`LockTime` values are const-only in v1",
                        value.span(),
                    );
                    return Err(());
                }
                true
            }
            ("Absolute", "time") => {
                if !matches!(value, Expr::Str { .. }) {
                    self.cx.error(
                        "sema/type-mismatch",
                        "`LockTime.Absolute(time: ...)` takes an ISO-8601 string",
                        value.span(),
                    );
                    return Err(());
                }
                true
            }
            ("Relative", "time") => {
                if matches!(value, Expr::Duration { .. }) {
                    self.cx.error(
                        "sema/type-mismatch",
                        "span literals were replaced by ISO-8601 duration strings; \
                         write `time: \"P90D\"` (or \"PT1H30M\", \"P4W\")",
                        value.span(),
                    );
                    return Err(());
                }
                if !matches!(value, Expr::Str { .. }) {
                    self.cx.error(
                        "sema/type-mismatch",
                        "`LockTime.Relative(time: ...)` takes an ISO-8601 duration string \
                         (\"P90D\")",
                        value.span(),
                    );
                    return Err(());
                }
                true
            }
            _ => {
                self.cx.error(
                    "sema/args",
                    format!(
                        "`LockTime.{variant}` takes {}, found `{}:`",
                        if variant == "Absolute" {
                            "`height:` or `time:`"
                        } else {
                            "`blocks:` or `time:`"
                        },
                        label.text
                    ),
                    label.span,
                );
                return Err(());
            }
        };
        debug_assert!(ok);
        let ty = if variant == "Absolute" {
            Ty::LockTimeAbs
        } else {
            Ty::LockTimeRel
        };
        Ok((Kind::Value(ty), true))
    }

    // --- comprehensions ---

    fn comprehension(
        &mut self,
        callee: &Ident,
        acc: Option<&AccClause>,
        binders: &[Binder],
        where_clauses: &[Expr],
        body: &Expr,
        span: Span,
    ) -> Result<(Kind, bool), ()> {
        // Scope hygiene on every exit path: binders/accumulator must never
        // leak into the enclosing scope, including on error returns.
        let depth_before = self.locals.len();
        let result = self.comprehension_inner(callee, acc, binders, where_clauses, body, span);
        self.locals.truncate(depth_before);
        result
    }

    fn comprehension_inner(
        &mut self,
        callee: &Ident,
        acc: Option<&AccClause>,
        binders: &[Binder],
        where_clauses: &[Expr],
        body: &Expr,
        span: Span,
    ) -> Result<(Kind, bool), ()> {
        let agg = callee.text.as_str();
        if !matches!(agg, "sum" | "count" | "all" | "any" | "fold") {
            self.cx.error(
                "sema/comp-callee",
                format!("`{agg}` is not an aggregator (sum, count, all, any, fold)"),
                callee.span,
            );
            return Err(());
        }
        if agg == "fold" && acc.is_none() {
            self.cx.error(
                "sema/fold-acc",
                "`fold` needs an accumulator: `fold(acc = init, x in xs => ...)`",
                span,
            );
            return Err(());
        }
        if agg != "fold"
            && let Some(a) = acc
        {
            self.cx.error(
                "sema/comp-acc",
                format!("only `fold` takes an accumulator clause, not `{agg}`"),
                a.span,
            );
            return Err(());
        }

        // Binder sequences: arrays or const ranges; parallel lengths must agree.
        // A comprehension over all-const data is itself const: binder elements
        // inherit the sequence's const-ness.
        let mut comp_const = true;
        let mut first_len: Option<(Len, Span)> = None;
        for b in binders {
            let (elem_ty, elem_const) = match &b.seq {
                Seq::Range {
                    lo,
                    hi,
                    span: rspan,
                    ..
                } => {
                    let lc = self.arith_operand(lo);
                    let hc = self.arith_operand(hi);
                    if !(lc? && hc?) {
                        self.cx.error(
                            "sema/range-const",
                            "comprehension range bounds are const; the loop unrolls at \
                             compile time",
                            *rspan,
                        );
                        return Err(());
                    }
                    // Range length equality with other binders is checked
                    // concretely at instantiation; ranges don't constrain
                    // `first_len`. Range elements are const by construction.
                    (Ty::Int, true)
                }
                Seq::Expr(e) => {
                    let (k, seq_const) = self.expr(e)?;
                    match k {
                        Kind::Value(Ty::Array(elem, len)) => {
                            match &first_len {
                                Option::None => first_len = Some((len.clone(), e.span())),
                                Some((prev, _)) if prev.same(&len) => {}
                                Some((prev, prev_span)) => {
                                    let (msg, span) = (
                                        format!(
                                            "parallel binders iterate zipped and must have \
                                             equal lengths: `{}` vs `{}`",
                                            describe_len(prev),
                                            describe_len(&len)
                                        ),
                                        e.span(),
                                    );
                                    self.cx.error("sema/zip-len", msg, span);
                                    let _ = prev_span;
                                    return Err(());
                                }
                            }
                            (*elem, seq_const)
                        }
                        Kind::Value(t) => {
                            self.cx.error(
                                "sema/type-mismatch",
                                format!(
                                    "a binder iterates an array or range, found `{}`",
                                    t.describe()
                                ),
                                e.span(),
                            );
                            return Err(());
                        }
                        Kind::Check => return Err(()),
                    }
                }
            };
            comp_const &= elem_const;
            self.declare_local(
                &b.name,
                Binding {
                    ty: elem_ty,
                    is_const: elem_const,
                    what: "binder",
                },
            );
        }

        // fold's accumulator binds AFTER its init is checked in the outer scope.
        let acc_ty = if let Some(a) = acc {
            // init is checked with binders out of scope conceptually; they are
            // in scope here, but using them in init is meaningless and caught
            // by the body-type unification anyway. Keep simple: check in place.
            let (k, init_const) = self.expr(&a.init)?;
            let Kind::Value(t) = k else {
                self.cx.error(
                    "sema/check-position",
                    "a timelock is not a value",
                    a.init.span(),
                );
                return Err(());
            };
            comp_const &= init_const;
            self.declare_local(
                &a.name,
                Binding {
                    ty: t.clone(),
                    is_const: init_const && comp_const,
                    what: "accumulator",
                },
            );
            Some(t)
        } else {
            Option::None
        };

        for w in where_clauses {
            match self.expr(w) {
                Ok((Kind::Value(Ty::Bool), c)) => comp_const &= c,
                Ok((Kind::Value(t), _)) => {
                    self.cx.error(
                        "sema/type-mismatch",
                        format!("a `where` guard must be `Bool`, found `{}`", t.describe()),
                        w.span(),
                    );
                }
                Ok((Kind::Check, _)) => {
                    self.cx.error(
                        "sema/check-position",
                        "a timelock cannot guard a comprehension",
                        w.span(),
                    );
                }
                Err(()) => {}
            }
        }

        let (bk, body_const) = self.expr(body)?;
        comp_const &= body_const;
        let Kind::Value(bt) = bk else {
            self.cx.error(
                "sema/check-position",
                "a timelock is not a comprehension body",
                body.span(),
            );
            return Err(());
        };

        let result = match agg {
            "sum" => {
                if !matches!(bt, Ty::Int | Ty::Bool) {
                    self.cx.error(
                        "sema/type-mismatch",
                        format!(
                            "`sum` body must be `Int` (or `Bool`, widened), found `{}`",
                            bt.describe()
                        ),
                        body.span(),
                    );
                    return Err(());
                }
                Ty::Int
            }
            "count" | "all" | "any" => {
                if bt != Ty::Bool {
                    self.cx.error(
                        "sema/type-mismatch",
                        format!("`{agg}` body must be `Bool`, found `{}`", bt.describe()),
                        body.span(),
                    );
                    return Err(());
                }
                if agg == "count" { Ty::Int } else { Ty::Bool }
            }
            "fold" => {
                let at = acc_ty.expect("fold has acc");
                if !ty_compatible(&at, &bt) {
                    self.cx.error(
                        "sema/type-mismatch",
                        format!(
                            "`fold` body must produce the accumulator type `{}`, found `{}`",
                            at.describe(),
                            bt.describe()
                        ),
                        body.span(),
                    );
                    return Err(());
                }
                at
            }
            _ => unreachable!(),
        };
        // A comprehension over all-const sequences/guards/body is const:
        // const evaluation folds it at instantiation.
        Ok((Kind::Value(result), comp_const))
    }
}

// --- small helpers ---

fn ty_compatible(a: &Ty, b: &Ty) -> bool {
    match (a, b) {
        (Ty::Hash(x), Ty::Hash(y)) => x == y,
        (Ty::Bytes(x), Ty::Bytes(y)) => x.same(y),
        (Ty::Array(ea, la), Ty::Array(eb, lb)) => ty_compatible(ea, eb) && la.same(lb),
        // Hash<A> is one-way compatible with same-length Bytes.
        (Ty::Hash(h), Ty::Bytes(Len::Lit(n))) | (Ty::Bytes(Len::Lit(n)), Ty::Hash(h)) => {
            h.byte_len() == *n
        }
        _ => a == b,
    }
}

fn contains_signature(t: &Ty) -> bool {
    match t {
        Ty::Signature => true,
        Ty::Array(e, _) => contains_signature(e),
        _ => false,
    }
}

fn describe_len(l: &Len) -> String {
    match l {
        Len::Lit(n) => n.to_string(),
        Len::Named(n) => n.clone(),
    }
}

/// Parse an integer literal's text (decimal with `_`, or `0x...`). The lexer
/// guarantees shape; this only extracts the value (unbounded would need
/// bignums; u128 covers every materializable value by orders of magnitude).
pub fn parse_int_text(text: &str) -> Option<u128> {
    let (digits, radix) = match text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
        Some(hex) => (hex, 16),
        Option::None => (text, 10),
    };
    let mut value: u128 = 0;
    for ch in digits.chars() {
        if ch == '_' {
            continue;
        }
        let d = ch.to_digit(radix)? as u128;
        value = value.checked_mul(radix as u128)?.checked_add(d)?;
    }
    Some(value)
}

/// `"0x" + 2N hex digits`: the literal shape for keys (and later, hashes).
fn is_hex_literal(s: &str, bytes: usize) -> bool {
    s.strip_prefix("0x")
        .map(|h| h.len() == bytes * 2 && h.chars().all(|c| c.is_ascii_hexdigit()))
        .unwrap_or(false)
}
