//! The parser: token stream to [`Contract`] AST plus diagnostics.
//!
//! Hand-rolled recursive descent (zero dependencies, total control over
//! diagnostics).
//!
//! # Decisions encoded here (each tested)
//!
//! - **Reserved tokens are rejected by the parser**, with their teaching
//!   diagnostic, at the position they appear: the lexer produces them as
//!   valid tokens precisely so this can happen in context.
//! - **Comprehension vs call**: a call is comprehension-form iff a `=>` occurs
//!   at parenthesis depth 1 before the matching `)`. Bounded lookahead over
//!   the token buffer, deterministic, no backtracking.
//! - **Argument labels may lexically be keywords** (`then:`, `else:` in
//!   `select`). Label position (`token ':'` inside call arguments) is closed
//!   and unambiguous; the label text is taken from the source span.
//! - **Type arguments parse at additive level** (`Bytes<N-1>` works; a
//!   comparison inside `<...>` cannot occur, killing `>` ambiguity outright).
//! - **Ranges are not values**: they parse only as `in`'s right-hand side and
//!   as comprehension sequences; a stray `lo..hi` gets a targeted error.
//! - **Trailing commas** are allowed in every bracket-closed list (params,
//!   arguments, arrays, require blocks, layout fields) and not before `=>`.
//! - **Recovery**: errors sync to statement/item boundaries; the parser never
//!   panics and reports multiple independent errors per run. A `Contract` is
//!   returned even when diagnostics exist (best effort: callers must treat
//!   any error diagnostic as failure).
//!
//! One `.sl` file is one contract.

use crate::diagnostics::Diagnostic;
use crate::syntax::ast::*;
use crate::syntax::lexer::{Token, lex};
use crate::syntax::span::Span;
use crate::syntax::token::TokenKind as K;

/// A source-size cap, mirroring the JSON input cap (`json::MAX_INPUT_BYTES`): a
/// `.sl` larger than this is rejected BEFORE lexing, so an oversized file cannot
/// grow the token stream / AST without bound (e.g. a giant array literal).
/// Generous -- real contracts are kilobytes.
const MAX_SOURCE_BYTES: usize = 8 << 20; // 8 MiB

/// Lex and parse a source file. Total: never panics; all problems are
/// diagnostics. The contract is `None` only when the top level is unusable.
pub fn parse_source(src: &str) -> (Option<Contract>, Vec<Diagnostic>) {
    if src.len() > MAX_SOURCE_BYTES {
        return (
            None,
            vec![Diagnostic::error(
                "parse/input",
                format!("source exceeds the {MAX_SOURCE_BYTES}-byte cap"),
                Span::new(0, 1),
            )],
        );
    }
    let (tokens, mut diags) = lex(src);
    let mut p = Parser {
        src,
        tokens: &tokens,
        pos: 0,
        diags: Vec::new(),
        depth: 0,
    };
    let contract = p.contract().ok();
    diags.extend(p.diags);
    (contract, diags)
}

/// Internal result: `Err(())` always means "already diagnosed".
type PResult<T> = Result<T, ()>;

struct Parser<'a> {
    src: &'a str,
    tokens: &'a [Token],
    pos: usize,
    diags: Vec<Diagnostic>,
    /// Current AST construction height. Every wrapping of a node in another,
    /// recursion (`(((...`) and chains (`a+b+c+...`, `a.b.c...`, `!!!x`) alike,
    /// draws on this one budget, so the height of any produced AST is bounded
    /// by construction. That bound is what makes the parser total on the
    /// stack at parse time and at drop time (a 100k-deep Box chain overflows
    /// in `Drop`, not in parsing; totality includes destruction).
    depth: u32,
}

/// One budget, sized for the worst real consumer: each nesting level costs
/// about 6 parser stack frames (`expr` to `comparison` to `additive` to
/// `unary` to `postfix` to `atom`), and debug-build frames must fit a 2 MiB
/// test-thread stack with ample margin. 64 levels is an order of magnitude
/// beyond any real contract (the corpus maxes at about 4) and keeps
/// parse-time recursion and drop-time recursion trivially safe in every build
/// profile.
const MAX_NESTING_DEPTH: u32 = 64;

impl<'a> Parser<'a> {
    // --- primitives ---

    fn tok(&self) -> &'a Token {
        // The lexer guarantees a final EOF token; clamp keeps us total.
        &self.tokens[self.pos.min(self.tokens.len() - 1)]
    }

    fn kind(&self) -> &'a K {
        &self.tok().kind
    }

    fn nth_kind(&self, n: usize) -> &'a K {
        &self.tokens[(self.pos + n).min(self.tokens.len() - 1)].kind
    }

    fn span(&self) -> Span {
        self.tok().span
    }

    fn bump(&mut self) -> &'a Token {
        let t = self.tok();
        if self.pos < self.tokens.len() - 1 {
            self.pos += 1;
        }
        t
    }

    fn at(&self, k: &K) -> bool {
        std::mem::discriminant(self.kind()) == std::mem::discriminant(k)
    }

    fn eat(&mut self, k: &K) -> bool {
        if self.at(k) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn error(&mut self, code: &'static str, msg: impl Into<String>, span: Span) {
        self.diags.push(Diagnostic::error(code, msg, span));
    }

    /// Describe the current token for error messages.
    fn describe(&self) -> String {
        match self.kind() {
            K::Eof => "end of file".into(),
            K::Ident(s) => format!("identifier `{s}`"),
            K::Int(s) => format!("integer `{s}`"),
            K::Decimal(s) => format!("decimal `{s}`"),
            K::Str(_) => "string literal".into(),
            _ => format!("`{}`", self.span().slice(self.src)),
        }
    }

    /// If the current token is reserved, emit its teaching diagnostic and
    /// consume it. Returns true when one was found (caller bails with Err).
    fn reserved_guard(&mut self) -> bool {
        if let K::Reserved(r) = self.kind() {
            let (r, span) = (*r, self.span());
            let (msg, help) = r.diagnostic();
            self.diags
                .push(Diagnostic::error("parse/reserved", msg, span).with_help(help));
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, k: &K, what: &str) -> PResult<&'a Token> {
        if self.at(k) {
            Ok(self.bump())
        } else {
            if !self.reserved_guard() {
                let (msg, span) = (
                    format!("expected {what}, found {}", self.describe()),
                    self.span(),
                );
                self.error("parse/expected", msg, span);
            }
            Err(())
        }
    }

    fn expect_ident(&mut self, what: &str) -> PResult<Ident> {
        if let K::Ident(text) = self.kind() {
            let (text, span) = (text.clone(), self.span());
            self.bump();
            Ok(Ident { text, span })
        } else {
            if !self.reserved_guard() {
                let (msg, span) = (
                    format!("expected {what}, found {}", self.describe()),
                    self.span(),
                );
                self.error("parse/expected", msg, span);
            }
            Err(())
        }
    }

    /// Skip to just after the next `;` at brace depth 0, or stop before an
    /// unmatched `}` or EOF. Brace-aware so one bad statement containing
    /// braces yields one diagnostic, not a cascade.
    fn sync_stmt(&mut self) {
        self.depth = 0; // recovery starts the next statement with a fresh height budget
        let mut depth = 0usize;
        loop {
            match self.kind() {
                K::Semi if depth == 0 => {
                    self.bump();
                    return;
                }
                K::LBrace => {
                    depth += 1;
                    self.bump();
                }
                K::RBrace => {
                    if depth == 0 {
                        return;
                    }
                    depth -= 1;
                    self.bump();
                }
                K::Eof => return,
                _ => {
                    self.bump();
                }
            }
        }
    }

    /// Skip until the start of a plausible next item at brace depth 0, or an
    /// unmatched `}` or EOF.
    fn sync_item(&mut self) {
        self.depth = 0; // recovery starts the next item with a fresh height budget
        let mut depth = 0usize;
        loop {
            match self.kind() {
                K::Extern | K::Const | K::Require | K::Spend | K::Open | K::At | K::Keypath
                    if depth == 0 =>
                {
                    return;
                }
                K::Semi if depth == 0 => {
                    self.bump();
                    return;
                }
                K::LBrace => {
                    depth += 1;
                    self.bump();
                }
                K::RBrace => {
                    if depth == 0 {
                        return;
                    }
                    depth -= 1;
                    self.bump();
                }
                K::Eof => return,
                _ => {
                    self.bump();
                }
            }
        }
    }

    // --- contract & items ---

    fn contract(&mut self) -> PResult<Contract> {
        let start = self.span();
        self.expect(&K::Contract, "`contract`")?;
        let name = self.expect_ident("contract name")?;
        self.expect(&K::LBrace, "`{` to open the contract body")?;

        let mut items = Vec::new();
        while !self.at(&K::RBrace) && !self.at(&K::Eof) {
            let before = self.pos;
            match self.item() {
                Ok(item) => items.push(item),
                Err(()) => self.sync_item(),
            }
            // Forward-progress guarantee (totality): a parse arm that errors
            // without consuming, plus a recovery anchor on the same token,
            // would otherwise spin forever. Append-only diagnostics make
            // that an unbounded-memory crash, not just a hang. Never trust
            // the arms to advance; enforce it here.
            if self.pos == before {
                self.bump();
            }
        }
        let close = self.span();
        self.expect(&K::RBrace, "`}` to close the contract body")?;

        // `keypath` is structurally required, exactly once.
        let keypaths = items
            .iter()
            .filter(|i| matches!(i, Item::Keypath(_)))
            .count();
        if keypaths == 0 {
            self.error(
                "parse/keypath-missing",
                "the contract must declare `keypath ...;` - a `PublicKey` expression or \
                 `None` (the most consequential line in a contract never defaults)",
                Span::new(start.start, close.end),
            );
        } else if keypaths > 1 {
            self.error(
                "parse/keypath-dup",
                "a contract declares exactly one `keypath`",
                Span::new(start.start, close.end),
            );
        }

        if !self.at(&K::Eof) {
            let (msg, span) = (
                format!(
                    "expected end of file after the contract, found {} (one contract per file)",
                    self.describe()
                ),
                self.span(),
            );
            self.error("parse/trailing", msg, span);
        }
        Ok(Contract {
            name,
            items,
            span: Span::new(start.start, close.end),
        })
    }

    fn item(&mut self) -> PResult<Item> {
        match self.kind() {
            K::Extern => self.extern_const(),
            K::Const => self.const_item(),
            K::Require => Ok(Item::Precondition(self.require_stmt()?)),
            K::At | K::Open | K::Spend => self.spend(),
            K::Keypath => self.keypath_item(),
            K::Layout => {
                let span = self.span();
                self.error(
                    "parse/layout-removed",
                    "the `layout { }` block was removed: write `keypath ...;` at the top \
                     level and `@depth(n)` / `@weight(n)` on spends",
                    span,
                );
                self.bump(); // consume `layout` so the item loop makes progress
                Err(())
            }
            _ => {
                if !self.reserved_guard() {
                    let (msg, span) = (
                        format!(
                            "expected an item (`extern const`, `const`, `require`, \
                             `keypath`, `@depth`/`@weight`, `spend`), found {}",
                            self.describe()
                        ),
                        self.span(),
                    );
                    self.error("parse/expected", msg, span);
                    self.bump();
                }
                Err(())
            }
        }
    }

    fn extern_const(&mut self) -> PResult<Item> {
        let start = self.span();
        self.expect(&K::Extern, "`extern`")?;
        self.expect(&K::Const, "`const` after `extern`")?;
        let name = self.expect_ident("constant name")?;
        if !self.at(&K::Colon) {
            let span = self.span();
            self.error(
                "parse/extern-needs-type",
                "`extern const` requires a type annotation: the value is injected at \
                 instantiation, so there is no initializer to infer from",
                span,
            );
            return Err(());
        }
        self.bump(); // ':'
        let ty = self.type_()?;
        let end = self
            .expect(&K::Semi, "`;` after the extern declaration")?
            .span;
        Ok(Item::ExternConst {
            name,
            ty,
            span: Span::new(start.start, end.end),
        })
    }

    fn const_item(&mut self) -> PResult<Item> {
        let start = self.span();
        self.expect(&K::Const, "`const`")?;
        let name = self.expect_ident("constant name")?;
        let ty = if self.eat(&K::Colon) {
            Some(self.type_()?)
        } else {
            None
        };
        self.expect(
            &K::Assign,
            "`=` (a `const` without a value is `extern const`)",
        )?;
        let value = self.expr()?;
        let end = self
            .expect(&K::Semi, "`;` after the const declaration")?
            .span;
        Ok(Item::Const {
            name,
            ty,
            value,
            span: Span::new(start.start, end.end),
        })
    }

    fn spend(&mut self) -> PResult<Item> {
        let start = self.span();
        // Leading cost decorators: `@depth(n)` / `@weight(n)`.
        let (depth, weight) = self.decorators()?;
        let open = self.eat(&K::Open);
        self.expect(&K::Spend, "`spend` (decorators attach to a spend)")?;
        let name = self.expect_ident("spend name")?;
        self.expect(&K::LParen, "`(` to open the parameter list")?;

        let mut params = Vec::new();
        while !self.at(&K::RParen) && !self.at(&K::Eof) {
            params.push(self.param()?);
            if !self.eat(&K::Comma) {
                break;
            }
        }
        self.expect(&K::RParen, "`)` to close the parameter list")?;
        self.expect(&K::LBrace, "`{` to open the spend body")?;

        let mut body = Vec::new();
        while !self.at(&K::RBrace) && !self.at(&K::Eof) {
            let before = self.pos;
            match self.stmt() {
                Ok(s) => body.push(s),
                Err(()) => self.sync_stmt(),
            }
            if self.pos == before {
                self.bump(); // forward-progress guarantee (totality)
            }
        }
        let end = self.expect(&K::RBrace, "`}` to close the spend body")?.span;
        Ok(Item::Spend(Spend {
            open,
            name,
            params,
            body,
            depth,
            weight,
            span: Span::new(start.start, end.end),
        }))
    }

    /// `@depth(n)` / `@weight(n)` cost decorators. Returns
    /// (depth, weight). Each may appear at most once.
    fn decorators(&mut self) -> PResult<(Option<u32>, Option<u64>)> {
        let mut depth: Option<u32> = None;
        let mut weight: Option<u64> = None;
        while self.at(&K::At) {
            let at = self.span();
            self.bump(); // '@'
            let name = self.expect_ident("a decorator name (`depth` or `weight`)")?;
            // Validate the name BEFORE its argument, so `@inline` teaches
            // "unknown decorator" rather than "expected `(`".
            let which = match name.text.as_str() {
                "depth" => "depth",
                "weight" => "weight",
                other => {
                    self.error(
                        "parse/decorator-unknown",
                        format!("unknown decorator `@{other}`: only `@depth` and `@weight` exist"),
                        Span::new(at.start, name.span.end),
                    );
                    return Err(());
                }
            };
            self.expect(&K::LParen, "`(` after the decorator name")?;
            if which == "depth" {
                let (n, n_span) = self.decorator_depth()?;
                self.expect(&K::RParen, "`)` to close the decorator")?;
                if depth.is_some() {
                    self.error("parse/decorator-dup", "duplicate `@depth`", name.span);
                    return Err(());
                }
                if n > 128 {
                    self.error(
                        "parse/depth-range",
                        "`@depth` is 0..=128 (BIP341 control-block limit)",
                        n_span,
                    );
                    return Err(());
                }
                depth = Some(n);
            } else {
                let w = self.decorator_weight()?;
                self.expect(&K::RParen, "`)` to close the decorator")?;
                if weight.is_some() {
                    self.error("parse/decorator-dup", "duplicate `@weight`", name.span);
                    return Err(());
                }
                weight = Some(w);
            }
        }
        Ok((depth, weight))
    }

    /// `@depth(n)`: a non-negative integer (a tree depth). A decimal is a
    /// type error here (depth is a whole number of levels).
    fn decorator_depth(&mut self) -> PResult<(u32, Span)> {
        let span = self.span();
        match self.kind() {
            K::Int(text) => {
                let text = text.clone();
                self.bump();
                match crate::analysis::sema::parse_int_text(&text)
                    .and_then(|v| u32::try_from(v).ok())
                {
                    Some(v) => Ok((v, span)),
                    None => {
                        self.error(
                            "parse/decorator-arg",
                            "`@depth` is out of range (0..=128)",
                            span,
                        );
                        Err(())
                    }
                }
            }
            _ => {
                let what = self.describe();
                self.error(
                    "parse/decorator-arg",
                    format!("`@depth` takes a whole number of tree levels (0..=128), found {what}"),
                    span,
                );
                Err(())
            }
        }
    }

    /// `@weight(n)`: a positive decimal usage weight, parsed exactly to a
    /// fixed-point micro-weight (value * 1_000_000; not IEEE float, so the
    /// planner stays deterministic). Accepts `4`, `0.4`, `2.5`, ...; up
    /// to 6 fractional digits; must be > 0.
    fn decorator_weight(&mut self) -> PResult<u64> {
        const SCALE: u64 = 1_000_000; // 6 fractional digits
        let span = self.span();
        let text = match self.kind() {
            K::Int(t) | K::Decimal(t) => t.clone(),
            _ => {
                let what = self.describe();
                self.error(
                    "parse/decorator-arg",
                    format!("`@weight` takes a positive number (relative usage, e.g. `0.4`, `2.5`, `4`), found {what}"),
                    span,
                );
                return Err(());
            }
        };
        self.bump();
        let clean = text.replace('_', "");
        let (int_part, frac_part) = match clean.split_once('.') {
            Some((i, f)) => (i, f),
            None => (clean.as_str(), ""),
        };
        if frac_part.len() > 6 {
            self.error(
                "parse/weight-precision",
                "`@weight` supports up to 6 fractional digits",
                span,
            );
            return Err(());
        }
        let Ok(int_val) = int_part.parse::<u64>() else {
            self.error(
                "parse/weight-range",
                "`@weight` integer part is too large",
                span,
            );
            return Err(());
        };
        if int_val > 1_000_000 {
            self.error("parse/weight-range", "`@weight` is at most 1_000_000", span);
            return Err(());
        }
        // Pad the fractional digits to exactly 6 places, then parse.
        let mut frac_padded = String::from(frac_part);
        while frac_padded.len() < 6 {
            frac_padded.push('0');
        }
        let frac_val: u64 = if frac_padded.is_empty() {
            0
        } else {
            match frac_padded.parse::<u64>() {
                Ok(v) => v,
                Err(_) => {
                    self.error(
                        "parse/weight-range",
                        "`@weight` fractional part malformed",
                        span,
                    );
                    return Err(());
                }
            }
        };
        let micro = int_val.saturating_mul(SCALE).saturating_add(frac_val);
        if micro == 0 {
            self.error(
                "parse/weight-range",
                "`@weight` must be positive (a zero weight has no meaning)",
                span,
            );
            return Err(());
        }
        Ok(micro)
    }

    fn keypath_item(&mut self) -> PResult<Item> {
        self.expect(&K::Keypath, "`keypath`")?;
        if self.eat(&K::LBrace) {
            // Block form holds exactly one value and is self-terminating.
            let kp = self.keypath_value()?;
            if !self.at(&K::RBrace) {
                let span = self.span();
                self.error(
                    "parse/keypath-block",
                    "a `keypath { }` block holds exactly one thing (a key or `None`)",
                    span,
                );
                return Err(());
            }
            self.bump(); // '}'
            self.forbid_block_semi("keypath { ... }");
            Ok(Item::Keypath(kp))
        } else {
            let kp = self.keypath_value()?;
            let _ = self.expect(
                &K::Semi,
                "`;` after `keypath ...` (a one-liner ends with `;`; a `keypath { }` block does not)",
            )?;
            Ok(Item::Keypath(kp))
        }
    }

    fn keypath_value(&mut self) -> PResult<Keypath> {
        if self.at(&K::None) {
            let s = self.span();
            self.bump();
            Ok(Keypath::None(s))
        } else {
            Ok(Keypath::Key(self.expr()?))
        }
    }

    fn param(&mut self) -> PResult<Param> {
        let start = self.span();
        let relaxed = self.eat(&K::Relaxed);
        let name = self.expect_ident("parameter name")?;
        self.expect(
            &K::Colon,
            "`:` before the parameter type (params are the witness interface)",
        )?;
        let ty = self.type_()?;
        let span = Span::new(start.start, ty.span.end);
        Ok(Param {
            relaxed,
            name,
            ty,
            span,
        })
    }

    // --- statements ---

    fn stmt(&mut self) -> PResult<Stmt> {
        match self.kind() {
            K::Let => {
                let start = self.span();
                self.bump();
                let name = self.expect_ident("binding name")?;
                if self.at(&K::Colon) {
                    let span = self.span();
                    self.error(
                        "parse/let-annotation",
                        "`let` bindings are inferred: remove the type annotation",
                        span,
                    );
                    return Err(());
                }
                self.expect(&K::Assign, "`=` in the let binding")?;
                let value = self.expr()?;
                let end = self.expect(&K::Semi, "`;` after the let binding")?.span;
                Ok(Stmt::Let {
                    name,
                    value,
                    span: Span::new(start.start, end.end),
                })
            }
            K::Require => Ok(Stmt::Require(self.require_stmt()?)),
            _ => {
                if !self.reserved_guard() {
                    let (msg, span) = (
                        format!(
                            "expected a statement (`let` or `require`), found {}",
                            self.describe()
                        ),
                        self.span(),
                    );
                    self.error("parse/expected", msg, span);
                    self.bump();
                }
                Err(())
            }
        }
    }

    fn require_stmt(&mut self) -> PResult<RequireStmt> {
        let start = self.span();
        self.expect(&K::Require, "`require`")?;
        if self.eat(&K::LBrace) {
            // Block form is self-terminating: the `}` ends it, no `;`.
            let mut items = Vec::new();
            while !self.at(&K::RBrace) && !self.at(&K::Eof) {
                items.push(self.expr()?);
                if !self.eat(&K::Comma) {
                    break;
                }
            }
            let end = self
                .expect(&K::RBrace, "`}` to close the require block")?
                .span;
            if items.is_empty() {
                self.error(
                    "parse/require-empty",
                    "empty `require` block: a require must constrain something",
                    Span::new(start.start, end.end),
                );
                return Err(());
            }
            self.forbid_block_semi("require { ... }");
            Ok(RequireStmt {
                items,
                block_form: true,
                span: Span::new(start.start, end.end),
            })
        } else {
            let item = self.expr()?;
            let end = self.expect(
                &K::Semi,
                "`;` after a single-line `require` (a one-liner ends with `;`; a `require { ... }` block does not)",
            )?.span;
            Ok(RequireStmt {
                items: vec![item],
                block_form: false,
                span: Span::new(start.start, end.end),
            })
        }
    }

    /// A brace block self-terminates; a trailing `;` is a mistake. Emits
    /// one teaching diagnostic and consumes the stray `;` (graceful
    /// recovery: the canonical form has no terminator).
    fn forbid_block_semi(&mut self, what: &str) {
        if self.at(&K::Semi) {
            self.error(
                "parse/block-semi",
                format!("no `;` after a `{what}` block: a brace block is self-terminating"),
                self.span(),
            );
            self.bump();
        }
    }

    // --- types ---

    fn type_(&mut self) -> PResult<Type> {
        self.descend()?;
        let result = self.type_inner();
        self.ascend();
        result
    }

    fn type_inner(&mut self) -> PResult<Type> {
        let start = self.span();
        if self.eat(&K::LBracket) {
            let elem = self.type_()?;
            self.expect(&K::Semi, "`;` between element type and length in `[T; N]`")?;
            let len = self.additive()?;
            let end = self
                .expect(&K::RBracket, "`]` to close the array type")?
                .span;
            return Ok(Type {
                kind: TypeKind::Array {
                    elem: Box::new(elem),
                    len: Box::new(len),
                },
                span: Span::new(start.start, end.end),
            });
        }

        let mut segments = vec![self.expect_ident("a type name")?];
        while self.at(&K::Dot) {
            self.bump();
            segments.push(self.expect_ident("type path segment after `.`")?);
        }
        let mut args = Vec::new();
        let mut end = segments.last().expect("nonempty").span;
        if self.eat(&K::Lt) {
            loop {
                args.push(self.additive()?);
                if !self.eat(&K::Comma) {
                    break;
                }
                if self.at(&K::Gt) {
                    break; // trailing comma
                }
            }
            end = self.expect(&K::Gt, "`>` to close the type arguments")?.span;
        }
        Ok(Type {
            kind: TypeKind::Path { segments, args },
            span: Span::new(start.start, end.end),
        })
    }

    /// Claim one level of AST height; errors past the bound (without
    /// claiming, so the counter stays consistent on the error path).
    fn descend(&mut self) -> PResult<()> {
        if self.depth >= MAX_NESTING_DEPTH {
            let span = self.span();
            self.error(
                "parse/depth",
                format!(
                    "nesting/chain deeper than {MAX_NESTING_DEPTH} levels: simplify the \
                     expression (aggregations belong in comprehensions)"
                ),
                span,
            );
            return Err(());
        }
        self.depth += 1;
        Ok(())
    }

    fn ascend(&mut self) {
        debug_assert!(self.depth > 0, "ascend without matching descend");
        self.depth -= 1;
    }

    /// Release `n` levels claimed by a chain loop.
    fn ascend_n(&mut self, n: u32) {
        for _ in 0..n {
            self.ascend();
        }
    }

    // --- expressions (precedence) ---

    pub(crate) fn expr(&mut self) -> PResult<Expr> {
        self.descend()?;
        let result = self.comparison();
        self.ascend();
        result
    }

    /// Comparison / membership level, the loosest. Handles single comparisons,
    /// same-direction chains, `in lo..hi`, and the targeted range error.
    fn comparison(&mut self) -> PResult<Expr> {
        let first = self.additive()?;

        if self.at(&K::DotDot) || self.at(&K::DotDotEq) {
            let span = self.span();
            self.error(
                "parse/range-not-value",
                "a range is not a value: ranges appear only after `in` \
                 (`x in lo..hi`) and as comprehension sequences",
                span,
            );
            return Err(());
        }

        if self.at(&K::In) {
            self.bump();
            let lo = self.additive()?;
            let inclusive = if self.eat(&K::DotDot) {
                false
            } else if self.eat(&K::DotDotEq) {
                true
            } else {
                if !self.reserved_guard() {
                    let (msg, span) = (
                        format!(
                            "`in` needs a range: `lo..hi` (half-open) or `lo..=hi` (inclusive), \
                             found {}",
                            self.describe()
                        ),
                        self.span(),
                    );
                    self.error("parse/in-needs-range", msg, span);
                }
                return Err(());
            };
            let hi = self.additive()?;
            let span = Span::new(first.span().start, hi.span().end);
            let node = Expr::In {
                value: Box::new(first),
                lo: Box::new(lo),
                hi: Box::new(hi),
                inclusive,
                span,
            };
            if self.peek_cmp_op().is_some() || self.at(&K::In) {
                let span = self.span();
                self.error(
                    "parse/chain-in",
                    "`in` does not chain with comparisons: parenthesize or split into \
                     require items",
                    span,
                );
                return Err(());
            }
            return Ok(node);
        }

        let mut rest: Vec<(CmpOp, Expr)> = Vec::new();
        while let Some(op) = self.peek_cmp_op() {
            self.bump();
            let rhs = self.additive()?;
            rest.push((op, rhs));
        }
        if rest.is_empty() {
            return Ok(first);
        }
        let span = Span::new(
            first.span().start,
            rest.last().expect("nonempty").1.span().end,
        );

        if rest.len() > 1 {
            // Chain validity: all ops in one direction class.
            let mut class = None;
            for (op, _) in &rest {
                match op.chain_class() {
                    Some(c) => match class {
                        None => class = Some(c),
                        Some(prev) if prev == c => {}
                        Some(_) => {
                            self.error(
                                "parse/chain-mixed",
                                "comparison chains must run in one direction: all `<`/`<=` \
                                 or all `>`/`>=`",
                                span,
                            );
                            return Err(());
                        }
                    },
                    None => {
                        self.error(
                            "parse/chain-eq",
                            "`==`/`!=` do not chain: split into separate require items",
                            span,
                        );
                        return Err(());
                    }
                }
            }
        }
        Ok(Expr::Compare {
            first: Box::new(first),
            rest,
            span,
        })
    }

    fn peek_cmp_op(&self) -> Option<CmpOp> {
        Some(match self.kind() {
            K::Lt => CmpOp::Lt,
            K::Le => CmpOp::Le,
            K::Gt => CmpOp::Gt,
            K::Ge => CmpOp::Ge,
            K::EqEq => CmpOp::Eq,
            K::NotEq => CmpOp::Ne,
            _ => return None,
        })
    }

    fn additive(&mut self) -> PResult<Expr> {
        let mut lhs = self.unary()?;
        let mut claimed = 0u32;
        let result = loop {
            let op = match self.kind() {
                K::Plus => BinaryOp::Add,
                K::Minus => BinaryOp::Sub,
                _ => break Ok(lhs),
            };
            // Each wrap deepens the left-leaning tree by one level.
            if self.descend().is_err() {
                break Err(());
            }
            claimed += 1;
            self.bump();
            let rhs = match self.unary() {
                Ok(e) => e,
                Err(()) => break Err(()),
            };
            let span = Span::new(lhs.span().start, rhs.span().end);
            lhs = Expr::Binary {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
                span,
            };
        };
        self.ascend_n(claimed);
        result
    }

    /// Unary prefixes are collected iteratively (no parse recursion) and each
    /// claims one level of AST height (the fold below builds a chain that
    /// deep, and drop glue recurses over it, so it draws on the same budget).
    fn unary(&mut self) -> PResult<Expr> {
        let mut prefixes: Vec<(UnaryOp, Span)> = Vec::new();
        let mut claimed = 0u32;
        let result = 'parse: {
            loop {
                let op = match self.kind() {
                    K::Bang => UnaryOp::Not,
                    K::Minus => UnaryOp::Neg,
                    _ => break,
                };
                if self.descend().is_err() {
                    break 'parse Err(());
                }
                claimed += 1;
                prefixes.push((op, self.span()));
                self.bump();
            }
            let mut expr = match self.postfix() {
                Ok(e) => e,
                Err(()) => break 'parse Err(()),
            };
            for (op, start) in prefixes.into_iter().rev() {
                let span = Span::new(start.start, expr.span().end);
                expr = Expr::Unary {
                    op,
                    operand: Box::new(expr),
                    span,
                };
            }
            Ok(expr)
        };
        self.ascend_n(claimed);
        result
    }

    fn postfix(&mut self) -> PResult<Expr> {
        let mut expr = self.atom()?;
        let mut claimed = 0u32;
        let result = 'parse: loop {
            // Each postfix step wraps the base one level deeper.
            match self.kind() {
                K::Dot | K::LParen | K::LBracket => {
                    if self.descend().is_err() {
                        break 'parse Err(());
                    }
                    claimed += 1;
                }
                _ => break 'parse Ok(expr),
            }
            match self.kind() {
                K::Dot => {
                    self.bump();
                    let member = match self.expect_ident("member name after `.`") {
                        Ok(m) => m,
                        Err(()) => break 'parse Err(()),
                    };
                    let span = Span::new(expr.span().start, member.span.end);
                    expr = Expr::Member {
                        base: Box::new(expr),
                        member,
                        span,
                    };
                }
                K::LParen => {
                    expr = match self.call(expr) {
                        Ok(e) => e,
                        Err(()) => break 'parse Err(()),
                    };
                }
                K::LBracket => {
                    self.bump();
                    let index = match self.expr() {
                        Ok(e) => e,
                        Err(()) => break 'parse Err(()),
                    };
                    let end = match self.expect(&K::RBracket, "`]` to close the index") {
                        Ok(t) => t.span,
                        Err(()) => break 'parse Err(()),
                    };
                    let span = Span::new(expr.span().start, end.end);
                    expr = Expr::Index {
                        base: Box::new(expr),
                        index: Box::new(index),
                        span,
                    };
                }
                _ => unreachable!("guarded above"),
            }
        };
        self.ascend_n(claimed);
        result
    }

    /// Parse a call. Comprehension-form iff `=>` occurs at depth 1 before the
    /// matching `)` (bounded lookahead over the token buffer).
    fn call(&mut self, callee: Expr) -> PResult<Expr> {
        debug_assert!(self.at(&K::LParen));
        if self.lookahead_comprehension() {
            let Expr::Name(name) = callee else {
                let span = callee.span();
                self.error(
                    "parse/comp-callee",
                    "comprehension form applies to a plain aggregator name \
                     (`sum`, `count`, `all`, `any`, `fold`)",
                    span,
                );
                return Err(());
            };
            return self.comprehension(name);
        }

        self.bump(); // '('
        let mut args = Vec::new();
        while !self.at(&K::RParen) && !self.at(&K::Eof) {
            args.push(self.arg()?);
            if !self.eat(&K::Comma) {
                break;
            }
        }
        let end = self.expect(&K::RParen, "`)` to close the call")?.span;
        let span = Span::new(callee.span().start, end.end);
        Ok(Expr::Call {
            callee: Box::new(callee),
            args,
            span,
        })
    }

    /// True iff a `=>` occurs at parenthesis depth 1 before the `)` matching
    /// the `(` at the current position. Brackets/braces tracked too so a
    /// `=>` inside nested structure never miscounts.
    fn lookahead_comprehension(&self) -> bool {
        let mut depth = 0usize;
        let mut i = self.pos;
        loop {
            let k = &self.tokens[i.min(self.tokens.len() - 1)].kind;
            match k {
                K::LParen | K::LBracket | K::LBrace => depth += 1,
                K::RParen | K::RBracket | K::RBrace => {
                    if depth <= 1 {
                        return false;
                    }
                    depth -= 1;
                }
                K::FatArrow if depth == 1 => return true,
                K::Eof => return false,
                _ => {}
            }
            i += 1;
        }
    }

    fn arg(&mut self) -> PResult<Arg> {
        // A label is `token ':'` where the token is an identifier OR any
        // keyword/reserved word (closed position; text from the source span).
        let labelable = matches!(self.kind(), K::Ident(_))
            || matches!(self.kind(), K::Reserved(_))
            || self.kind_is_keyword();
        if labelable && matches!(self.nth_kind(1), K::Colon) {
            let span = self.span();
            let text = span.slice(self.src).to_string();
            self.bump(); // label
            self.bump(); // ':'
            let value = self.expr()?;
            return Ok(Arg {
                label: Some(Ident { text, span }),
                value,
            });
        }
        Ok(Arg {
            label: None,
            value: self.expr()?,
        })
    }

    fn kind_is_keyword(&self) -> bool {
        matches!(
            self.kind(),
            K::Contract
                | K::Spend
                | K::Extern
                | K::Const
                | K::Require
                | K::Let
                | K::Layout
                | K::Keypath
                | K::Open
                | K::Relaxed
                | K::Where
                | K::In
                | K::None
                | K::True
                | K::False
        )
    }

    /// `agg(acc = init, x in xs, ... where c1, c2 => body)`
    fn comprehension(&mut self, callee: Ident) -> PResult<Expr> {
        self.expect(&K::LParen, "`(`")?;
        let mut acc: Option<AccClause> = None;
        let mut binders: Vec<Binder> = Vec::new();
        let mut where_clauses: Vec<Expr> = Vec::new();

        loop {
            if self.at(&K::Where) {
                break; // `where` follows the last binder without a comma
            }
            if matches!(self.kind(), K::Ident(_)) && matches!(self.nth_kind(1), K::Assign) {
                let name = self.expect_ident("accumulator name")?;
                self.bump(); // '='
                let init = self.expr()?;
                let span = Span::new(name.span.start, init.span().end);
                if acc.is_some() {
                    self.error(
                        "parse/comp-acc-dup",
                        "only one accumulator clause is allowed",
                        span,
                    );
                    return Err(());
                }
                if !binders.is_empty() {
                    self.error(
                        "parse/comp-acc-order",
                        "the accumulator clause comes first: `fold(acc = init, x in xs => ...)`",
                        span,
                    );
                    return Err(());
                }
                acc = Some(AccClause {
                    name,
                    init: Box::new(init),
                    span,
                });
            } else {
                let name = self.expect_ident(
                    "a binder (`x in xs`), `where`, or an accumulator (`acc = init`)",
                )?;
                self.expect(&K::In, "`in` after the binder name")?;
                let seq = self.seq()?;
                let span = Span::new(name.span.start, seq_end(&seq));
                binders.push(Binder { name, seq, span });
            }
            if !self.eat(&K::Comma) {
                break;
            }
        }

        // Optional guard list: `where c1, c2` runs to `=>`.
        if self.at(&K::Where) {
            self.bump();
            loop {
                where_clauses.push(self.expr()?);
                if !self.eat(&K::Comma) {
                    break;
                }
            }
        }

        self.expect(&K::FatArrow, "`=>` before the comprehension body")?;
        if binders.is_empty() {
            let span = self.span();
            self.error(
                "parse/comp-no-binder",
                "a comprehension needs at least one binder (`x in xs`)",
                span,
            );
            return Err(());
        }
        let body = self.expr()?;
        let end = self
            .expect(&K::RParen, "`)` to close the comprehension")?
            .span;
        let span = Span::new(callee.span.start, end.end);
        Ok(Expr::Comprehension {
            callee,
            acc,
            binders,
            where_clauses,
            body: Box::new(body),
            span,
        })
    }

    /// A comprehension sequence: range (unparenthesized) or array expression.
    fn seq(&mut self) -> PResult<Seq> {
        let first = self.additive()?;
        if self.at(&K::DotDot) || self.at(&K::DotDotEq) {
            let inclusive = self.at(&K::DotDotEq);
            self.bump();
            let hi = self.additive()?;
            let span = Span::new(first.span().start, hi.span().end);
            return Ok(Seq::Range {
                lo: first,
                hi,
                inclusive,
                span,
            });
        }
        Ok(Seq::Expr(first))
    }

    // --- atoms ---

    fn atom(&mut self) -> PResult<Expr> {
        let span = self.span();
        match self.kind() {
            K::Int(text) => {
                let text = text.clone();
                self.bump();
                Ok(Expr::Int { text, span })
            }
            K::Decimal(_) => {
                self.error(
                    "parse/decimal-position",
                    "decimal literals exist only as `@weight(...)` arguments: there is no \
                     fractional number type",
                    span,
                );
                self.bump();
                Err(())
            }
            K::Str(text) => {
                let text = text.clone();
                self.bump();
                Ok(Expr::Str { text, span })
            }
            K::Duration { value, unit } => {
                let (value, unit) = (value.clone(), *unit);
                self.bump();
                Ok(Expr::Duration { value, unit, span })
            }
            K::True => {
                self.bump();
                Ok(Expr::Bool { value: true, span })
            }
            K::False => {
                self.bump();
                Ok(Expr::Bool { value: false, span })
            }
            K::Ident(text) => {
                // Generic typed constructor: `Bytes<32>("0x...")` / `Hash<Sha256>("0x...")`.
                // Unambiguous: the generic type-name set is closed, and a bare
                // type name is never a value, so `Bytes <` can only open
                // type arguments, never a comparison.
                if (text == "Bytes" || text == "Hash") && matches!(self.nth_kind(1), K::Lt) {
                    let ty = self.type_()?;
                    self.expect(
                        &K::LParen,
                        "`(`: a generic type in expression position is a constructor",
                    )?;
                    let mut args = Vec::new();
                    while !self.at(&K::RParen) && !self.at(&K::Eof) {
                        args.push(self.arg()?);
                        if !self.eat(&K::Comma) {
                            break;
                        }
                    }
                    let end = self
                        .expect(&K::RParen, "`)` to close the constructor")?
                        .span;
                    return Ok(Expr::TypedCtor {
                        ty,
                        args,
                        span: Span::new(span.start, end.end),
                    });
                }
                let text = text.clone();
                self.bump();
                Ok(Expr::Name(Ident { text, span }))
            }
            K::None => {
                self.error(
                    "parse/none-position",
                    "`None` is only valid as the layout `keypath:` value",
                    span,
                );
                self.bump();
                Err(())
            }
            K::LParen => {
                self.bump();
                let inner = self.expr()?;
                self.expect(&K::RParen, "`)` to close the parenthesized expression")?;
                Ok(inner)
            }
            K::LBracket => {
                self.bump();
                let mut elems = Vec::new();
                while !self.at(&K::RBracket) && !self.at(&K::Eof) {
                    elems.push(self.expr()?);
                    if !self.eat(&K::Comma) {
                        break;
                    }
                }
                let end = self
                    .expect(&K::RBracket, "`]` to close the array literal")?
                    .span;
                if elems.is_empty() {
                    self.error(
                        "parse/array-empty",
                        "empty array literals are not supported (no element type to infer)",
                        Span::new(span.start, end.end),
                    );
                    return Err(());
                }
                Ok(Expr::ArrayLit {
                    elems,
                    span: Span::new(span.start, end.end),
                })
            }
            _ => {
                if !self.reserved_guard() {
                    let msg = format!("expected an expression, found {}", self.describe());
                    self.error("parse/expected", msg, span);
                    self.bump();
                }
                Err(())
            }
        }
    }
}

fn seq_end(seq: &Seq) -> u32 {
    match seq {
        Seq::Expr(e) => e.span().end,
        Seq::Range { span, .. } => span.end,
    }
}
