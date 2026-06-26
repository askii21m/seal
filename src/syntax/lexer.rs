//! The lexer: source text to token stream plus diagnostics.
//!
//! # Lexical grammar (normative)
//!
//! - **Whitespace**: space, `\t`, `\r`, `\n`.
//! - **Comments**: `//` to end of line. There are no block comments (`/*` is a
//!   dedicated error with recovery past a matching `*/`).
//! - **Identifiers**: `[A-Za-z_][A-Za-z0-9_]*`, ASCII only. Checked against the
//!   keyword table, then the reserved-word table, else `Ident`.
//! - **Integers**: decimal `[0-9][0-9_]*` or hex `0x[0-9a-fA-F_]+`.
//!   Underscores must sit between digits (no leading, trailing, or doubled).
//!   No leading zeros in decimal (`0` itself is fine; there are no octal
//!   literals to imitate). Hex prefix is lowercase `0x`.
//! - **Durations**: decimal integer immediately followed by a unit in
//!   `{s, m, h, d, w}` (`90d`). Decimal only: a trailing `d` in hex is a hex
//!   digit.
//! - **Suffix rule**: a numeric literal must not be immediately followed by an
//!   identifier character (`90q`, `90dd`, `0x1z` are errors, recovered as one
//!   bad token, no cascade).
//! - **Strings**: `"..."`, single-line, no escape sequences (strings exist
//!   only as typed-constructor arguments, such as hex keys and ISO timestamps,
//!   which never need them). A backslash or a control byte is an error; a
//!   newline or EOF before the closing quote is an unterminated-string error.
//! - **Non-ASCII**: legal only inside comments and strings. Anywhere else it is
//!   an error covering the full character (spans never split a UTF-8 sequence).
//!
//! # Error philosophy
//!
//! The lexer is total: it never panics, on any input, and always produces a
//! best-effort token stream plus diagnostics. Malformed lexemes are lexer
//! errors; reserved tokens are not: they lex successfully as
//! [`TokenKind::Reserved`] and are rejected with their teaching diagnostic by
//! the parser (which can point at them in context).
//!
//! # Invariants (checked by [`verify_token_stream_invariants`])
//!
//! Spans are ascending, non-overlapping, within bounds, and lie on UTF-8
//! boundaries; every non-EOF token has a non-empty span; the stream ends with
//! exactly one EOF token whose span is empty.

use crate::diagnostics::Diagnostic;
use crate::syntax::span::Span;
use crate::syntax::token::{Reserved, TokenKind, keyword};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

/// Lex `src` completely. Total: never panics; errors become diagnostics.
pub fn lex(src: &str) -> (Vec<Token>, Vec<Diagnostic>) {
    if src.len() > u32::MAX as usize {
        return (
            vec![Token {
                kind: TokenKind::Eof,
                span: Span::at(0),
            }],
            vec![Diagnostic::error(
                "lex/too-large",
                "source exceeds 4 GiB; compilation refused",
                Span::at(0),
            )],
        );
    }
    let mut lx = Lexer {
        src,
        bytes: src.as_bytes(),
        pos: 0,
        tokens: Vec::new(),
        diags: Vec::new(),
    };
    lx.run();
    (lx.tokens, lx.diags)
}

struct Lexer<'s> {
    src: &'s str,
    bytes: &'s [u8],
    pos: usize,
    tokens: Vec<Token>,
    diags: Vec<Diagnostic>,
}

const DURATION_UNITS: &[u8] = b"smhdw";

fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}
fn is_ident_continue(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}
fn is_hex_digit(b: u8) -> bool {
    b.is_ascii_hexdigit()
}

impl<'s> Lexer<'s> {
    fn run(&mut self) {
        while self.pos < self.bytes.len() {
            let b = self.bytes[self.pos];
            match b {
                b' ' | b'\t' | b'\r' | b'\n' => self.pos += 1,
                b'/' => self.slash(),
                b'"' => self.string(),
                b'0'..=b'9' => self.number(),
                _ if is_ident_start(b) => self.ident(),
                _ if b.is_ascii() => self.punct(),
                _ => self.unexpected_char(),
            }
        }
        let end = self.pos as u32;
        self.tokens.push(Token {
            kind: TokenKind::Eof,
            span: Span::at(end),
        });
    }

    // --- primitives ---

    /// Byte at `pos + ahead`, or 0 past the end (0 is never a valid lexeme byte).
    fn peek(&self, ahead: usize) -> u8 {
        self.bytes.get(self.pos + ahead).copied().unwrap_or(0)
    }

    fn span_from(&self, start: usize) -> Span {
        Span::new(start as u32, self.pos as u32)
    }

    fn push(&mut self, kind: TokenKind, start: usize) {
        let span = self.span_from(start);
        self.tokens.push(Token { kind, span });
    }

    /// Emit a fixed-width token: consume `width` bytes (all ASCII by caller's
    /// guarantee), then push.
    fn op(&mut self, kind: TokenKind, width: usize) {
        let start = self.pos;
        self.pos += width;
        self.push(kind, start);
    }

    fn error(&mut self, code: &'static str, message: impl Into<String>, span: Span) {
        self.diags.push(Diagnostic::error(code, message, span));
    }

    // --- comments and `/` ---

    fn slash(&mut self) {
        match self.peek(1) {
            b'/' => {
                // Line comment: skip to (not past) the newline. Bytes are safe:
                // b'\n' cannot occur inside a multi-byte UTF-8 sequence.
                while self.pos < self.bytes.len() && self.bytes[self.pos] != b'\n' {
                    self.pos += 1;
                }
            }
            b'*' => {
                // No block comments. Recover past a matching `*/` (or EOF) so
                // the commented-out text doesn't cascade into nonsense errors.
                let start = self.pos;
                self.pos += 2;
                let mut closed = false;
                while self.pos < self.bytes.len() {
                    if self.bytes[self.pos] == b'*' && self.peek(1) == b'/' {
                        self.pos += 2;
                        closed = true;
                        break;
                    }
                    self.pos += 1;
                }
                // Re-align to a char boundary if the byte scan stopped mid-char
                // (only possible at the unclosed-EOF case, where pos == len).
                debug_assert!(closed || self.pos == self.bytes.len());
                let _ = closed;
                self.error(
                    "lex/block-comment",
                    "no block comments; use `//` line comments",
                    self.span_from(start),
                );
            }
            _ => self.op(TokenKind::Reserved(Reserved::Slash), 1),
        }
    }

    // --- strings ---

    fn string(&mut self) {
        let start = self.pos;
        self.pos += 1; // opening quote
        let content_start = self.pos;
        let mut escape_reported = false;
        let mut control_reported = false;
        loop {
            if self.pos >= self.bytes.len() {
                self.error(
                    "lex/string-unterminated",
                    "unterminated string literal (reached end of file)",
                    self.span_from(start),
                );
                let content = self.src[content_start..self.pos].to_string();
                self.push(TokenKind::Str(content), start);
                return;
            }
            let b = self.bytes[self.pos];
            match b {
                b'"' => {
                    let content = self.src[content_start..self.pos].to_string();
                    self.pos += 1; // closing quote
                    self.push(TokenKind::Str(content), start);
                    return;
                }
                b'\n' => {
                    // Strings are single-line. End the token before the newline.
                    self.error(
                        "lex/string-unterminated",
                        "unterminated string literal (strings are single-line)",
                        self.span_from(start),
                    );
                    let content = self.src[content_start..self.pos].to_string();
                    self.push(TokenKind::Str(content), start);
                    return;
                }
                b'\\' => {
                    if !escape_reported {
                        self.error(
                            "lex/string-escape",
                            "escape sequences are not supported (strings are raw: \
                             hex keys and timestamps never need them)",
                            Span::new(self.pos as u32, self.pos as u32 + 1),
                        );
                        escape_reported = true;
                    }
                    self.pos += 1;
                }
                0x00..=0x1F => {
                    if !control_reported {
                        self.error(
                            "lex/string-control",
                            "control character in string literal",
                            Span::new(self.pos as u32, self.pos as u32 + 1),
                        );
                        control_reported = true;
                    }
                    self.pos += 1;
                }
                _ if b.is_ascii() => self.pos += 1,
                _ => {
                    // Non-ASCII is legal inside strings; advance one full char.
                    let ch = self.src[self.pos..]
                        .chars()
                        .next()
                        .expect("pos on char boundary");
                    self.pos += ch.len_utf8();
                }
            }
        }
    }

    // --- numbers ---

    fn number(&mut self) {
        let start = self.pos;
        if self.bytes[self.pos] == b'0' && (self.peek(1) == b'x' || self.peek(1) == b'X') {
            if self.peek(1) == b'X' {
                self.error(
                    "lex/hex-prefix",
                    "use lowercase `0x` for hex literals",
                    Span::new(start as u32, start as u32 + 2),
                );
            }
            self.pos += 2;
            let digits_start = self.pos;
            self.scan_digit_run(is_hex_digit, start);
            if self.pos == digits_start {
                // `0x` with no digits: swallow any trailing identifier run as
                // one bad token so `0xg...` reports exactly one error.
                while self.pos < self.bytes.len() && is_ident_continue(self.bytes[self.pos]) {
                    self.pos += 1;
                }
                self.error(
                    "lex/int-empty-hex",
                    "hex literal needs at least one digit after `0x`",
                    self.span_from(start),
                );
                let text = self.src[start..self.pos].to_string();
                self.push(TokenKind::Int(text), start);
                return;
            }
            let text = self.src[start..self.pos].to_string();
            self.suffix_check(start);
            self.push(TokenKind::Int(text), start);
            return;
        }

        // Decimal.
        self.scan_digit_run(|b| b.is_ascii_digit(), start);
        let digit_text = &self.src[start..self.pos];
        let digit_count = digit_text.bytes().filter(u8::is_ascii_digit).count();
        if digit_count > 1 && digit_text.as_bytes()[0] == b'0' {
            self.error(
                "lex/int-leading-zero",
                "leading zeros are not permitted (there are no octal literals)",
                self.span_from(start),
            );
        }

        // Decimal fraction (`0.4`): a single `.` followed by a digit. Must
        // precede the range check elsewhere (`0..4` is NOT a decimal: the
        // second char after the digits is `.`, not a digit) and the duration
        // check below. The fractional part is NOT subject to the leading-zero
        // rule (`0.04` is valid). Only `@weight(...)` accepts it.
        if self.peek(0) == b'.' && self.peek(1).is_ascii_digit() {
            self.pos += 1; // consume '.'
            self.scan_digit_run(|b| b.is_ascii_digit(), start);
            let text = self.src[start..self.pos].to_string();
            self.suffix_check(start);
            self.push(TokenKind::Decimal(text), start);
            return;
        }

        // Duration? A unit letter binds to the literal only if what follows the
        // unit is NOT another identifier character (so `90d` is a duration but
        // `90dd` falls through to the suffix error below).
        let unit = self.peek(0);
        if DURATION_UNITS.contains(&unit) && !is_ident_continue(self.peek(1)) {
            let value = digit_text.to_string();
            self.pos += 1;
            self.push(
                TokenKind::Duration {
                    value,
                    unit: unit as char,
                },
                start,
            );
            return;
        }

        let text = digit_text.to_string();
        self.suffix_check(start);
        self.push(TokenKind::Int(text), start);
    }

    /// Scan `[digit _]*` enforcing: underscores strictly between digits.
    /// Reports at most one underscore error per literal.
    fn scan_digit_run(&mut self, is_digit: fn(u8) -> bool, literal_start: usize) {
        let mut reported = false;
        let mut prev_was_digit = false;
        loop {
            let b = self.peek(0);
            if is_digit(b) {
                prev_was_digit = true;
                self.pos += 1;
            } else if b == b'_' {
                let next_is_digit = is_digit(self.peek(1));
                if (!prev_was_digit || !next_is_digit) && !reported {
                    self.error(
                        "lex/int-underscore",
                        "underscores must sit between digits (`1_000_000`)",
                        Span::new(self.pos as u32, self.pos as u32 + 1),
                    );
                    reported = true;
                }
                prev_was_digit = false;
                self.pos += 1;
            } else {
                break;
            }
        }
        let _ = literal_start;
    }

    /// A numeric literal must not be immediately followed by an identifier
    /// character. Recover by consuming the offending run into the same span.
    fn suffix_check(&mut self, literal_start: usize) {
        if is_ident_continue(self.peek(0)) {
            let bad_start = self.pos;
            while self.pos < self.bytes.len() && is_ident_continue(self.bytes[self.pos]) {
                self.pos += 1;
            }
            self.error(
                "lex/int-suffix",
                format!(
                    "invalid suffix `{}` on numeric literal (durations take exactly one \
                     unit of s/m/h/d/w)",
                    &self.src[bad_start..self.pos]
                ),
                self.span_from(literal_start),
            );
        }
    }

    // --- identifiers / keywords / reserved words ---

    fn ident(&mut self) {
        let start = self.pos;
        while self.pos < self.bytes.len() && is_ident_continue(self.bytes[self.pos]) {
            self.pos += 1;
        }
        let word = &self.src[start..self.pos];
        let kind = if let Some(kw) = keyword(word) {
            kw
        } else if let Some(r) = Reserved::from_word(word) {
            TokenKind::Reserved(r)
        } else {
            TokenKind::Ident(word.to_string())
        };
        self.push(kind, start);
    }

    // --- punctuation (maximal munch) ---

    fn punct(&mut self) {
        use Reserved as R;
        use TokenKind as K;
        let b = self.bytes[self.pos];
        let b1 = self.peek(1);
        match (b, b1) {
            (b'+', b'=') => self.op(K::Reserved(R::PlusEq), 2),
            (b'+', _) => self.op(K::Plus, 1),
            (b'-', b'>') => self.op(K::Reserved(R::Arrow), 2),
            (b'-', b'=') => self.op(K::Reserved(R::MinusEq), 2),
            (b'-', _) => self.op(K::Minus, 1),
            (b'!', b'=') => self.op(K::NotEq, 2),
            (b'!', _) => self.op(K::Bang, 1),
            (b'=', b'=') => self.op(K::EqEq, 2),
            (b'=', b'>') => self.op(K::FatArrow, 2),
            (b'=', _) => self.op(K::Assign, 1),
            (b'<', b'=') => self.op(K::Le, 2),
            (b'<', b'<') => self.op(K::Reserved(R::Shl), 2),
            (b'<', _) => self.op(K::Lt, 1),
            (b'>', b'=') => self.op(K::Ge, 2),
            (b'>', b'>') => self.op(K::Reserved(R::Shr), 2),
            (b'>', _) => self.op(K::Gt, 1),
            (b'.', b'.') => match self.peek(2) {
                b'=' => self.op(K::DotDotEq, 3),
                b'.' => self.op(K::Reserved(R::DotDotDot), 3),
                _ => self.op(K::DotDot, 2),
            },
            (b'.', _) => self.op(K::Dot, 1),
            (b':', b':') => self.op(K::Reserved(R::ColonColon), 2),
            (b':', _) => self.op(K::Colon, 1),
            (b'&', b'&') => self.op(K::Reserved(R::AmpAmp), 2),
            (b'&', _) => self.op(K::Reserved(R::Amp), 1),
            (b'|', b'|') => self.op(K::Reserved(R::PipePipe), 2),
            (b'|', _) => self.op(K::Reserved(R::Pipe), 1),
            (b'*', b'*') => self.op(K::Reserved(R::StarStar), 2),
            (b'*', _) => self.op(K::Reserved(R::Star), 1),
            (b'%', _) => self.op(K::Reserved(R::Percent), 1),
            (b'?', _) => self.op(K::Reserved(R::Question), 1),
            (b'@', _) => self.op(K::At, 1),
            (b'^', _) => self.op(K::Reserved(R::Caret), 1),
            (b'~', _) => self.op(K::Reserved(R::Tilde), 1),
            (b'#', _) => self.op(K::Reserved(R::Hash), 1),
            (b',', _) => self.op(K::Comma, 1),
            (b';', _) => self.op(K::Semi, 1),
            (b'(', _) => self.op(K::LParen, 1),
            (b')', _) => self.op(K::RParen, 1),
            (b'{', _) => self.op(K::LBrace, 1),
            (b'}', _) => self.op(K::RBrace, 1),
            (b'[', _) => self.op(K::LBracket, 1),
            (b']', _) => self.op(K::RBracket, 1),
            _ => self.unexpected_char(),
        }
    }

    fn unexpected_char(&mut self) {
        let start = self.pos;
        let ch = self.src[self.pos..]
            .chars()
            .next()
            .expect("pos on char boundary");
        self.pos += ch.len_utf8();
        self.error(
            "lex/char",
            format!("unexpected character `{ch}`"),
            self.span_from(start),
        );
    }
}

/// Check the lexer's output invariants. Used by unit, integration, and any
/// future fuzz tests; returns the first violation as a message.
pub fn verify_token_stream_invariants(src: &str, tokens: &[Token]) -> Result<(), String> {
    let len = src.len() as u32;
    if tokens.is_empty() {
        return Err("empty token stream (EOF token missing)".into());
    }
    let mut prev_end = 0u32;
    for (i, t) in tokens.iter().enumerate() {
        let last = i == tokens.len() - 1;
        if (t.kind == TokenKind::Eof) != last {
            return Err(format!("EOF token misplaced at index {i}"));
        }
        if t.span.start > t.span.end || t.span.end > len {
            return Err(format!("span out of bounds: {:?}", t.span));
        }
        if t.span.start < prev_end {
            return Err(format!(
                "overlapping/unordered span at index {i}: {:?}",
                t.span
            ));
        }
        if !src.is_char_boundary(t.span.start as usize)
            || !src.is_char_boundary(t.span.end as usize)
        {
            return Err(format!("span splits a UTF-8 character: {:?}", t.span));
        }
        if !last && t.span.is_empty() {
            return Err(format!("empty span on non-EOF token at index {i}"));
        }
        prev_end = t.span.end;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::token::Reserved as R;
    use crate::syntax::token::TokenKind as K;

    /// Lex, assert invariants, return (kinds-without-EOF, diagnostic codes).
    fn lex_all(src: &str) -> (Vec<K>, Vec<&'static str>) {
        let (tokens, diags) = lex(src);
        verify_token_stream_invariants(src, &tokens).unwrap();
        let kinds = tokens[..tokens.len() - 1]
            .iter()
            .map(|t| t.kind.clone())
            .collect();
        let codes = diags.iter().map(|d| d.code).collect();
        (kinds, codes)
    }

    /// Lex expecting zero diagnostics.
    fn lex_ok(src: &str) -> Vec<K> {
        let (kinds, codes) = lex_all(src);
        assert!(
            codes.is_empty(),
            "unexpected diagnostics for {src:?}: {codes:?}"
        );
        kinds
    }

    fn ident(s: &str) -> K {
        K::Ident(s.into())
    }
    fn int(s: &str) -> K {
        K::Int(s.into())
    }

    // --- maximal munch ---

    #[test]
    fn munch_dots() {
        assert_eq!(lex_ok(".."), vec![K::DotDot]);
        assert_eq!(lex_ok("..="), vec![K::DotDotEq]);
        assert_eq!(lex_ok("..."), vec![K::Reserved(R::DotDotDot)]);
        assert_eq!(lex_ok("."), vec![K::Dot]);
        assert_eq!(lex_ok("0..784"), vec![int("0"), K::DotDot, int("784")]);
        assert_eq!(lex_ok("0..=10"), vec![int("0"), K::DotDotEq, int("10")]);
        // Four dots: `...` then `.`, one reserved token, one stray dot.
        assert_eq!(lex_ok("...."), vec![K::Reserved(R::DotDotDot), K::Dot]);
    }

    #[test]
    fn munch_comparisons_and_arrows() {
        assert_eq!(lex_ok("== = =>"), vec![K::EqEq, K::Assign, K::FatArrow]);
        assert_eq!(lex_ok("<= < <<"), vec![K::Le, K::Lt, K::Reserved(R::Shl)]);
        assert_eq!(lex_ok(">= > >>"), vec![K::Ge, K::Gt, K::Reserved(R::Shr)]);
        assert_eq!(lex_ok("!= !"), vec![K::NotEq, K::Bang]);
        assert_eq!(
            lex_ok("-> - -="),
            vec![K::Reserved(R::Arrow), K::Minus, K::Reserved(R::MinusEq)]
        );
        assert_eq!(lex_ok("+ +="), vec![K::Plus, K::Reserved(R::PlusEq)]);
        assert_eq!(lex_ok(":: :"), vec![K::Reserved(R::ColonColon), K::Colon]);
        assert_eq!(
            lex_ok("&& & || |"),
            vec![
                K::Reserved(R::AmpAmp),
                K::Reserved(R::Amp),
                K::Reserved(R::PipePipe),
                K::Reserved(R::Pipe)
            ]
        );
        assert_eq!(
            lex_ok("** *"),
            vec![K::Reserved(R::StarStar), K::Reserved(R::Star)]
        );
    }

    // --- keywords, reserved words, identifiers ---

    #[test]
    fn keywords_lex_as_keywords() {
        assert_eq!(
            lex_ok("contract spend extern const require let layout keypath"),
            vec![
                K::Contract,
                K::Spend,
                K::Extern,
                K::Const,
                K::Require,
                K::Let,
                K::Layout,
                K::Keypath
            ]
        );
        assert_eq!(
            lex_ok("open relaxed where in None true false"),
            vec![
                K::Open,
                K::Relaxed,
                K::Where,
                K::In,
                K::None,
                K::True,
                K::False
            ]
        );
    }

    #[test]
    fn reserved_words_lex_as_reserved() {
        assert_eq!(
            lex_ok("if else and or var for while fn match"),
            vec![
                K::Reserved(R::If),
                K::Reserved(R::Else),
                K::Reserved(R::And),
                K::Reserved(R::Or),
                K::Reserved(R::Var),
                K::Reserved(R::For),
                K::Reserved(R::While),
                K::Reserved(R::Fn),
                K::Reserved(R::Match)
            ]
        );
    }

    #[test]
    fn idents_including_near_keywords() {
        assert_eq!(
            lex_ok("none If ELSE _x x1 PublicKey"),
            vec![
                ident("none"), // `None` is the keyword; lowercase is an ident
                ident("If"),
                ident("ELSE"),
                ident("_x"),
                ident("x1"),
                ident("PublicKey")
            ]
        );
    }

    // --- numbers ---

    #[test]
    fn numbers_valid() {
        assert_eq!(
            lex_ok("0 7 784 1_000_000 0x3FFF_FFFF 0xab 0x10d"),
            vec![
                int("0"),
                int("7"),
                int("784"),
                int("1_000_000"),
                int("0x3FFF_FFFF"),
                int("0xab"),
                int("0x10d") // `d` is a hex digit, not a duration unit
            ]
        );
    }

    #[test]
    fn decimal_literals_lex_and_dont_collide_with_ranges() {
        // A single `.` between digits is a decimal; `..` stays a range.
        assert_eq!(lex_ok("0.4"), vec![K::Decimal("0.4".into())]);
        assert_eq!(lex_ok("2.5"), vec![K::Decimal("2.5".into())]);
        // Fractional leading zeros are fine (not subject to the int rule).
        assert_eq!(lex_ok("0.04"), vec![K::Decimal("0.04".into())]);
        // `0..4` is a range, not `0.` then `.4`.
        assert_eq!(lex_ok("0..4"), vec![int("0"), K::DotDot, int("4")]);
        // A `.` not followed by a digit is the member-access dot.
        assert_eq!(lex_ok("x.m"), vec![ident("x"), K::Dot, ident("m")]);
        assert_eq!(lex_ok("3 .. 5"), vec![int("3"), K::DotDot, int("5")]);
    }

    #[test]
    fn durations_valid() {
        let kinds = lex_ok("90d 12h 45m 30s 2w 0d");
        let expect = [
            ("90", 'd'),
            ("12", 'h'),
            ("45", 'm'),
            ("30", 's'),
            ("2", 'w'),
            ("0", 'd'),
        ];
        for (k, (v, u)) in kinds.iter().zip(expect) {
            assert_eq!(
                *k,
                K::Duration {
                    value: v.into(),
                    unit: u
                }
            );
        }
    }

    #[test]
    fn duration_binds_only_when_terminated() {
        // `90dd` is not a duration followed by `d`; it's a suffix error.
        let (_, codes) = lex_all("90dd");
        assert_eq!(codes, vec!["lex/int-suffix"]);
        // `90d2` likewise.
        let (_, codes) = lex_all("90d2");
        assert_eq!(codes, vec!["lex/int-suffix"]);
    }

    #[test]
    fn number_errors() {
        for (src, code) in [
            ("01", "lex/int-leading-zero"),
            ("007", "lex/int-leading-zero"),
            ("0_1", "lex/int-leading-zero"),
            ("1_", "lex/int-underscore"),
            ("1__0", "lex/int-underscore"),
            ("0x_1", "lex/int-underscore"),
            ("0x1_", "lex/int-underscore"),
            ("0x", "lex/int-empty-hex"),
            ("0xg", "lex/int-empty-hex"),
            ("90q", "lex/int-suffix"),
            ("9z9", "lex/int-suffix"),
        ] {
            let (_, codes) = lex_all(src);
            assert_eq!(codes, vec![code], "for input {src:?}");
        }
        // `0X` prefix: error, but still recovers as a hex literal.
        let (kinds, codes) = lex_all("0X1f");
        assert_eq!(codes, vec!["lex/hex-prefix"]);
        assert_eq!(kinds, vec![int("0X1f")]);
    }

    // --- strings ---

    #[test]
    fn strings_valid() {
        assert_eq!(
            lex_ok(r#""0xba78" "2026-06-10T14:30:00Z" """#),
            vec![
                K::Str("0xba78".into()),
                K::Str("2026-06-10T14:30:00Z".into()),
                K::Str("".into())
            ]
        );
        // Non-ASCII inside strings is legal.
        assert_eq!(
            lex_ok("\"\u{a7} \u{2264} \u{d7}\""),
            vec![K::Str("\u{a7} \u{2264} \u{d7}".into())]
        );
    }

    #[test]
    fn string_errors() {
        let (_, codes) = lex_all("\"abc");
        assert_eq!(codes, vec!["lex/string-unterminated"]);
        let (kinds, codes) = lex_all("\"abc\nlet");
        assert_eq!(codes, vec!["lex/string-unterminated"]);
        assert_eq!(kinds, vec![K::Str("abc".into()), K::Let]); // recovery continues
        let (_, codes) = lex_all(r#""a\n""#);
        assert_eq!(codes, vec!["lex/string-escape"]);
        let (_, codes) = lex_all("\"a\tb\"");
        assert_eq!(codes, vec!["lex/string-control"]);
    }

    // --- comments ---

    #[test]
    fn comments() {
        assert_eq!(
            lex_ok("let // trailing \u{a7} unicode \u{2248} fine\nrequire"),
            vec![K::Let, K::Require]
        );
        assert_eq!(lex_ok("// comment at EOF"), vec![]);
        let (kinds, codes) = lex_all("/* old style */ let");
        assert_eq!(codes, vec!["lex/block-comment"]);
        assert_eq!(kinds, vec![K::Let]); // recovered past the close
        let (kinds, codes) = lex_all("/* unclosed");
        assert_eq!(codes, vec!["lex/block-comment"]);
        assert_eq!(kinds, vec![]);
    }

    // --- stray characters ---

    #[test]
    fn unexpected_chars_cover_whole_utf8_char() {
        let (tokens, diags) = lex("\u{b2}");
        verify_token_stream_invariants("\u{b2}", &tokens).unwrap();
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "lex/char");
        assert_eq!(diags[0].span.len() as usize, "\u{b2}".len());
    }

    // --- totality and determinism ---

    #[test]
    fn total_on_all_single_bytes() {
        for b in 0..=255u8 {
            if let Ok(s) = std::str::from_utf8(&[b]) {
                let (tokens, _) = lex(s);
                verify_token_stream_invariants(s, &tokens).unwrap();
            }
        }
    }

    #[test]
    fn total_on_all_ascii_pairs() {
        for a in 0..128u8 {
            for b in 0..128u8 {
                let buf = [a, b];
                let s = std::str::from_utf8(&buf).expect("ascii");
                let (tokens, _) = lex(s);
                verify_token_stream_invariants(s, &tokens)
                    .unwrap_or_else(|e| panic!("invariants failed on {buf:?}: {e}"));
            }
        }
    }

    #[test]
    fn deterministic() {
        let src = "spend f(sigs: [Signature; N]) { require sum(k in keys, s in sigs => k.check(s)) >= M; }";
        assert_eq!(lex(src), lex(src));
    }

    /// Every non-literal, non-reserved TokenKind must be producible by the
    /// lexer. An enum variant without a lexer rule is dead weight or, worse,
    /// an unlexable piece of the language.
    #[test]
    fn every_punctuation_token_is_producible() {
        let table: &[(&str, K)] = &[
            ("+", K::Plus),
            ("-", K::Minus),
            ("!", K::Bang),
            ("==", K::EqEq),
            ("!=", K::NotEq),
            ("<", K::Lt),
            ("<=", K::Le),
            (">", K::Gt),
            (">=", K::Ge),
            ("=", K::Assign),
            (",", K::Comma),
            (";", K::Semi),
            (":", K::Colon),
            (".", K::Dot),
            ("..", K::DotDot),
            ("..=", K::DotDotEq),
            ("=>", K::FatArrow),
            ("@", K::At),
            ("(", K::LParen),
            (")", K::RParen),
            ("{", K::LBrace),
            ("}", K::RBrace),
            ("[", K::LBracket),
            ("]", K::RBracket),
        ];
        for (src, expected) in table {
            assert_eq!(lex_ok(src), vec![expected.clone()], "for source {src:?}");
        }
    }

    // --- a realistic fragment end-to-end ---

    #[test]
    fn realistic_fragment() {
        let src = "require bid in 0..=1_000_000;";
        assert_eq!(
            lex_ok(src),
            vec![
                K::Require,
                ident("bid"),
                K::In,
                int("0"),
                K::DotDotEq,
                int("1_000_000"),
                K::Semi
            ]
        );
    }
}
