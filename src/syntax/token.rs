//! The token vocabulary.
//!
//! Comments are `//` line comments; identifiers are `[a-zA-Z_][a-zA-Z0-9_]*`
//! (types capitalized by convention).
//!
//! The `Reserved` variants are load-bearing: the lexer recognizes every habit the
//! language refuses and emits a teaching diagnostic instead of a generic parse
//! error.

/// A token kind. Spans and positions live in the lexer's `Token` wrapper.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    // --- Keywords ---
    Contract,
    Spend,
    Extern,
    Const,
    Require,
    Let,
    Layout,
    Keypath,
    Open,    // prefix modifier on `spend` (authorization concession)
    Relaxed, // prefix modifier on parameters (non-malleability concession)
    Where,   // comprehension guard clause; commas conjoin
    In,      // iteration binder and range membership
    None,    // keypath: None means deterministic per-contract NUMS
    True,
    False,

    // --- Punctuation and operators (each operator <= 1 opcode) ---
    Plus,
    Minus, // binary OP_SUB / unary OP_NEGATE (parser disambiguates)
    Bang,  // `!` to OP_NOT (fuses to OP_NOTIF in branch position)
    EqEq,
    NotEq,
    Lt,
    Le,
    Gt,
    Ge,
    Assign, // `=` binds names (const/let/fold accumulator); never compares
    Comma,  // the conjunction (require blocks, where clauses) and list separator
    Semi,
    Colon,    // labels: named args, layout fields, type ascription
    Dot,      // method/associated access: key.check, PublicKey.MuSig2, LockTime.Absolute
    DotDot,   // `..`  half-open range: index idiom; native OP_WITHIN, zero adjustment
    DotDotEq, // `..=` inclusive range: domain idiom (Rust-style)
    FatArrow, // `=>` comprehension/fold heads only
    At,       // retired (`@override`); lexes for the migration diagnostic
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,

    // --- Literals ---
    /// Decimal (`1_000_000`) or hex (`0x3FFF_FFFF`). Stored as written; const
    /// evaluation is unbounded-precision, so value parsing happens above the lexer.
    Int(String),
    /// A decimal fraction (`0.4`, `2.5`): the ONLY non-integer numeric
    /// literal, and valid ONLY as a `@weight(...)` argument.
    /// Fixed-point, not IEEE float; the parser converts it exactly. Lexed
    /// here so misuse elsewhere gets a clear diagnostic, not a lex error.
    Decimal(String),
    /// String literals exist ONLY as typed-constructor arguments; there is no
    /// string type.
    Str(String),
    /// Span literal (`90d`, `12h`, ...): retired surface (ISO-8601
    /// duration strings replaced it); still lexes so sema can teach the
    /// migration. Previously legal only inside
    /// `LockTime.Relative(time: ...)`; rounds UP to 512-second units, reported.
    Duration {
        value: String,
        unit: char,
    },
    Ident(String),

    // --- Reserved: recognized solely to teach ---
    Reserved(Reserved),

    Eof,
}

/// Everything the language refuses, kept nameable so diagnostics can teach.
/// One entry per habit; `diagnostic()` is the single source of truth for the
/// error text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reserved {
    AmpAmp,     // &&
    PipePipe,   // ||
    And,        // and
    Or,         // or
    If,         // if
    Else,       // else
    Var,        // var
    For,        // for
    While,      // while
    Fn,         // fn
    Match,      // match
    DotDotDot,  // ...
    Question,   // ?
    Star,       // *
    Slash,      // /
    Percent,    // %
    StarStar,   // **
    Shl,        // <<
    Shr,        // >>
    Amp,        // &   (bitwise, disabled in Script)
    Pipe,       // |
    Caret,      // ^
    Tilde,      // ~
    PlusEq,     // +=  (mutation habit)
    MinusEq,    // -=
    ColonColon, // ::  (path habit; the language uses `.`)
    Hash,       // #   (attribute habit; the language uses `@`)
    Arrow,      // ->  (function-type habit)
}

impl Reserved {
    /// The teaching diagnostic shown when a refused habit is encountered:
    /// `(headline, help)`. The headline states what is unavailable; the help
    /// names the supported alternative.
    pub fn diagnostic(self) -> (&'static str, &'static str) {
        use Reserved::*;
        match self {
            AmpAmp | PipePipe | And | Or => (
                "boolean operators are not available",
                "conjunction is the comma list in a `require`/`where`; disjunction is a separate `spend`, or widened arithmetic `(a) + (b) >= 1`",
            ),
            If | Else => (
                "`if` is not available",
                "selection is a `where` filter or `select(c, then:, else:)`; policy alternatives are separate `spend`s",
            ),
            Var | For | While => (
                "mutable bindings and loops are not available",
                "bindings are immutable; iterate with a comprehension like `sum(x in xs => ...)`",
            ),
            Fn => (
                "helper functions are not available",
                "a `spend` is the only root; inline the logic into its `require`",
            ),
            Match => (
                "`match` is not available",
                "use a `where` filter or `select(c, then:, else:)`",
            ),
            DotDotDot => (
                "`...` is not a range operator",
                "use `..` for a half-open range or `..=` for an inclusive one",
            ),
            Question => (
                "optional types are not available",
                "declinability is a property of the predicate (the `>= k` threshold), not the slot; a declined signature is the empty vector",
            ),
            Star | Slash | Percent => (
                "multiplication, division, and modulo are not available",
                "Bitcoin Script has no safe multiply or divide; express the check with addition and comparison, or fold a constant",
            ),
            StarStar => (
                "`**` is not a power operator",
                "use `pow(base, exp)` with constant operands",
            ),
            Shl | Shr => (
                "shift operators are not available",
                "there are no bit-shift opcodes; use arithmetic on `Int`s",
            ),
            Amp | Pipe | Caret | Tilde => (
                "bitwise operators are not available",
                "OP_AND/OP_OR/OP_XOR/OP_INVERT are disabled in tapscript; model bits as 0/1 `Int`s and combine with arithmetic",
            ),
            PlusEq | MinusEq => (
                "compound assignment is not available",
                "bindings are immutable; each `let` introduces a new value",
            ),
            ColonColon => (
                "`::` is not a path separator",
                "use `.` for associated access, e.g. `PublicKey.MuSig2([...])` or `LockTime.Absolute(...)`",
            ),
            Hash => (
                "attribute syntax is not available",
                "`script:` alone pins the layout tree",
            ),
            Arrow => (
                "`->` is not available",
                "a `spend`'s body is its `require` constraints",
            ),
        }
    }

    /// Reserved words (a subset of `Reserved`): the lexer checks identifiers
    /// against this table after the keyword table.
    pub fn from_word(word: &str) -> Option<Reserved> {
        use Reserved::*;
        Some(match word {
            "and" => And,
            "or" => Or,
            "if" => If,
            "else" => Else,
            "var" => Var,
            "for" => For,
            "while" => While,
            "fn" => Fn,
            "match" => Match,
            _ => return Option::None,
        })
    }
}

/// Keyword table, checked before `Reserved::from_word`, then `Ident`.
pub fn keyword(word: &str) -> Option<TokenKind> {
    use TokenKind::*;
    Some(match word {
        "contract" => Contract,
        "spend" => Spend,
        "extern" => Extern,
        "const" => Const,
        "require" => Require,
        "let" => Let,
        "layout" => Layout,
        "keypath" => Keypath,
        "open" => Open,
        "relaxed" => Relaxed,
        "where" => Where,
        "in" => In,
        "None" => None,
        "true" => True,
        "false" => False,
        _ => return Option::None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALL_RESERVED: [Reserved; 28] = [
        Reserved::AmpAmp,
        Reserved::PipePipe,
        Reserved::And,
        Reserved::Or,
        Reserved::If,
        Reserved::Else,
        Reserved::Var,
        Reserved::For,
        Reserved::While,
        Reserved::Fn,
        Reserved::Match,
        Reserved::DotDotDot,
        Reserved::Question,
        Reserved::Star,
        Reserved::Slash,
        Reserved::Percent,
        Reserved::StarStar,
        Reserved::Shl,
        Reserved::Shr,
        Reserved::Amp,
        Reserved::Pipe,
        Reserved::Caret,
        Reserved::Tilde,
        Reserved::PlusEq,
        Reserved::MinusEq,
        Reserved::ColonColon,
        Reserved::Hash,
        Reserved::Arrow,
    ];

    #[test]
    fn every_reserved_token_teaches() {
        for r in ALL_RESERVED {
            let (msg, help) = r.diagnostic();
            assert!(!msg.is_empty(), "{r:?} has no headline");
            assert!(
                !help.is_empty(),
                "{r:?} has no help (the supported alternative)"
            );
            // No user-facing message may reference "the spec".
            assert!(
                !msg.contains("spec") && !help.contains("spec"),
                "{r:?} references spec: {msg} / {help}"
            );
        }
    }

    #[test]
    fn keywords_and_reserved_words_are_disjoint() {
        for word in [
            "contract", "spend", "extern", "const", "require", "let", "layout", "keypath", "open",
            "relaxed", "where", "in", "None", "true", "false",
        ] {
            assert!(keyword(word).is_some(), "{word} must be a keyword");
            assert!(
                Reserved::from_word(word).is_none(),
                "{word} is both keyword and reserved"
            );
        }
        for word in [
            "and", "or", "if", "else", "var", "for", "while", "fn", "match",
        ] {
            assert!(
                Reserved::from_word(word).is_some(),
                "{word} must be reserved"
            );
            assert!(
                keyword(word).is_none(),
                "{word} is both reserved and keyword"
            );
        }
    }
}
