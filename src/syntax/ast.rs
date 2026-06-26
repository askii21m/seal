//! The abstract syntax tree: the parser's output, the analyses' input.
//!
//! Every node carries its [`Span`] so later phases (types, intervals, paths,
//! lowering) can point diagnostics at source.
//!
//! The AST is syntactic: it records what was written, not what it means.
//! `sum`/`fold`/`select` are ordinary identifiers here; the semantic layer
//! resolves them and validates their special rules. Integer values stay as
//! written (`"1_000_000"`, `"0x3FFF_FFFF"`): const evaluation is
//! unbounded-precision and happens above the parser.

use crate::syntax::span::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident {
    pub text: String,
    pub span: Span,
}

/// One `.sl` file is one contract (v1).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Contract {
    pub name: Ident,
    pub items: Vec<Item>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Item {
    /// `extern const name: Type;`. Type annotation required.
    ExternConst {
        name: Ident,
        ty: Type,
        span: Span,
    },
    /// `const name = expr;` / `const name: Type = expr;`
    Const {
        name: Ident,
        ty: Option<Type>,
        value: Expr,
        span: Span,
    },
    /// Contract-scope `require`: a template precondition.
    Precondition(RequireStmt),
    Spend(Spend),
    /// `keypath <None | const PublicKey expr>;` (or `keypath { ... }`).
    /// Required, top-level; declares the key-path spend.
    Keypath(Keypath),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spend {
    /// `open spend ...`: an authorization concession.
    pub open: bool,
    pub name: Ident,
    pub params: Vec<Param>,
    pub body: Vec<Stmt>,
    /// `@depth(n)`: pin this leaf's tree depth (absolute cost ceiling).
    pub depth: Option<u32>,
    /// `@weight(n)`: relative usage weight for the planner, as fixed-point
    /// micro-weight (value times 1_000_000; `@weight(0.4)` gives 400_000).
    /// Default (no decorator) is 1.0 = 1_000_000. Fixed-point, not float,
    /// for determinism.
    pub weight: Option<u64>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    /// `relaxed name: Type`: a non-malleability concession.
    pub relaxed: bool,
    pub name: Ident,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    /// `let name = expr;`. No type annotation: lets are inferred.
    Let {
        name: Ident,
        value: Expr,
        span: Span,
    },
    Require(RequireStmt),
}

/// `require expr;` or `require { e1, e2, ... };`. Items conjoin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RequireStmt {
    pub items: Vec<Expr>,
    /// Written with braces? (Single-item blocks are legal; semantics identical.)
    pub block_form: bool,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Keypath {
    /// `keypath None;` gives a deterministic per-contract NUMS.
    None(Span),
    /// `keypath <const PublicKey expression>;`.
    Key(Expr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind {
    /// `Int`, `PublicKey`, `LockTime.Absolute`, `Bytes<32>`, `Hash<Sha256>`.
    /// Generic arguments are expressions at additive level: type args are
    /// const expressions or algorithm names (`Sha256` parses as a path
    /// expression; the semantic layer interprets).
    Path {
        segments: Vec<Ident>,
        args: Vec<Expr>,
    },
    /// `[Type; len]`. len is a const expression (possibly an extern).
    Array { elem: Box<Type>, len: Box<Expr> },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// Integer literal, text as written (decimal with `_`, or `0x...`).
    Int {
        text: String,
        span: Span,
    },
    /// String literal content (delimiters excluded).
    Str {
        text: String,
        span: Span,
    },
    /// Duration literal: `90d` becomes ("90", 'd'). Retired surface, kept
    /// for the ISO-8601 migration diagnostic.
    Duration {
        value: String,
        unit: char,
        span: Span,
    },
    Bool {
        value: bool,
        span: Span,
    },
    /// A name: variable, const, type-in-expression-position (`PublicKey`),
    /// or stdlib function. Resolution is semantic.
    Name(Ident),
    /// `base.member`: field/associated access (`LockTime.Absolute`,
    /// `PublicKey.MuSig2`, the callee of `key.check`).
    Member {
        base: Box<Expr>,
        member: Ident,
        span: Span,
    },
    /// `callee(args...)`: a plain call (NOT comprehension form).
    Call {
        callee: Box<Expr>,
        args: Vec<Arg>,
        span: Span,
    },
    /// `agg(acc = init, x in xs, ... where c, ... => body)`.
    /// The callee name is syntactic; the semantic layer validates it
    /// (`sum`/`count`/`all`/`any`/`fold`) and that `acc` appears only with
    /// `fold`.
    Comprehension {
        callee: Ident,
        acc: Option<AccClause>,
        binders: Vec<Binder>,
        where_clauses: Vec<Expr>,
        body: Box<Expr>,
        span: Span,
    },
    /// `base[index]`: const index (a semantic rule).
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
        span: Span,
    },
    Unary {
        op: UnaryOp,
        operand: Box<Expr>,
        span: Span,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        span: Span,
    },
    /// A comparison run: `a < b`, or a same-direction chain `1 <= M <= N`.
    /// `rest` is non-empty; direction validity is enforced at parse time, so
    /// a constructed chain is always well-formed.
    Compare {
        first: Box<Expr>,
        rest: Vec<(CmpOp, Expr)>,
        span: Span,
    },
    /// `x in lo..hi` / `x in lo..=hi`. Membership requires a range RHS, the
    /// only place ranges are values-adjacent.
    In {
        value: Box<Expr>,
        lo: Box<Expr>,
        hi: Box<Expr>,
        inclusive: bool,
        span: Span,
    },
    /// `[a, b, c]`: const-only array literal. Never empty.
    ArrayLit {
        elems: Vec<Expr>,
        span: Span,
    },
    /// A generic typed constructor in expression position:
    /// `Bytes<32>("0x...")`, `Hash<Sha256>("0x...")`. Unambiguous because the
    /// generic type-name set is closed and a bare type name is never a value.
    TypedCtor {
        ty: Type,
        args: Vec<Arg>,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Arg {
    /// `label: value`. Labels may lexically be keywords (`then:`, `else:`).
    pub label: Option<Ident>,
    pub value: Expr,
}

/// `acc = init`: fold's accumulator clause.
/// `init` is boxed to break the `Expr` to `AccClause` to `Expr` size cycle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccClause {
    pub name: Ident,
    pub init: Box<Expr>,
    pub span: Span,
}

/// `x in seq`. Parallel binders iterate zipped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binder {
    pub name: Ident,
    pub seq: Seq,
    pub span: Span,
}

/// A comprehension sequence: an array expression or a literal range.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Seq {
    Expr(Expr),
    Range {
        lo: Expr,
        hi: Expr,
        inclusive: bool,
        span: Span,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    /// `-` maps to OP_NEGATE (total: symmetric domain).
    Neg,
    /// `!` maps to OP_NOT.
    Not,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpOp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

impl CmpOp {
    /// Chains may mix only within a direction class.
    pub fn chain_class(self) -> Option<ChainClass> {
        match self {
            CmpOp::Lt | CmpOp::Le => Some(ChainClass::Ascending),
            CmpOp::Gt | CmpOp::Ge => Some(ChainClass::Descending),
            CmpOp::Eq | CmpOp::Ne => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChainClass {
    Ascending,
    Descending,
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Expr::Int { span, .. }
            | Expr::Str { span, .. }
            | Expr::Duration { span, .. }
            | Expr::Bool { span, .. }
            | Expr::Member { span, .. }
            | Expr::Call { span, .. }
            | Expr::Comprehension { span, .. }
            | Expr::Index { span, .. }
            | Expr::Unary { span, .. }
            | Expr::Binary { span, .. }
            | Expr::Compare { span, .. }
            | Expr::In { span, .. }
            | Expr::ArrayLit { span, .. }
            | Expr::TypedCtor { span, .. } => *span,
            Expr::Name(ident) => ident.span,
        }
    }
}
