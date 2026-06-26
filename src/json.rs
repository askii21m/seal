//! A strict JSON subset parser for instantiation arguments. Hand-rolled,
//! zero dependencies, total.
//!
//! The subset is the point: everything JSON allows that an extern cannot
//! honor is a parse error with a teaching message, not a lossy conversion.
//!
//! - No floats, no exponents (`1.5`, `1e3`): an `Int` extern can never
//!   take one, so refusing beats rounding.
//! - No `null`: there is no optional extern.
//! - No duplicate object keys: silent last-wins is how wrong keys ship.
//! - No trailing commas (JSON standard), no comments.
//! - Strings: `\"` and `\\` escapes only (hex keys and ISO timestamps never
//!   need more); raw control bytes rejected; UTF-8 passthrough otherwise.
//! - Integers: i128, checked; leading zeros rejected (JSON standard).
//! - Nesting depth at most 64: totality includes the stack.
//!
//! Object key order is preserved (Vec, not a map) for deterministic
//! diagnostics; duplicate detection is exact.

/// A parsed value. Key order preserved; duplicates already rejected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Json {
    Object(Vec<(String, Json)>),
    Array(Vec<Json>),
    Str(String),
    Int(i128),
    Bool(bool),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsonError {
    /// Byte offset into the source.
    pub offset: usize,
    pub msg: String,
}

const MAX_DEPTH: u32 = 64;
/// Input-size cap: a standard contract's args are kilobytes; an 8 MiB ceiling is
/// orders of magnitude above any real input yet stops a hostile args blob (e.g.
/// a multi-gigabyte array literal) from OOMing the parser before a per-array
/// limit could apply. Totality includes memory.
const MAX_INPUT_BYTES: usize = 8 << 20;

/// Serialize a [`Json`] value to a compact, standard JSON string -- the kind any
/// conformant reader (`JSON.parse`, serde, ...) accepts.
///
/// This is the OUTPUT path: the structured compile result a web IDE consumes. It
/// is deliberately separate from [`parse`] above, whose strict subset grammar
/// (no floats, no `null`, only `\"`/`\\` escapes) must NOT change -- that grammar
/// guards extern args, this serializer feeds a frontend. Strings get full
/// standard escaping (`\n`, `\t`, `\uXXXX`, ...), so a diagnostic message with a
/// quote or newline round-trips through any conformant JSON reader.
pub fn to_string(v: &Json) -> String {
    let mut out = String::new();
    write_value(&mut out, v);
    out
}

fn write_value(out: &mut String, v: &Json) {
    match v {
        Json::Object(fields) => {
            out.push('{');
            for (i, (k, val)) in fields.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write_json_string(out, k);
                out.push(':');
                write_value(out, val);
            }
            out.push('}');
        }
        Json::Array(items) => {
            out.push('[');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write_value(out, item);
            }
            out.push(']');
        }
        Json::Str(s) => write_json_string(out, s),
        Json::Int(n) => out.push_str(&n.to_string()),
        Json::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
    }
}

fn write_json_string(out: &mut String, s: &str) {
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{08}' => out.push_str("\\b"),
            '\u{0c}' => out.push_str("\\f"),
            // Remaining C0 control characters have no short escape: \u00XX.
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            // Everything else (including non-ASCII UTF-8) is a literal JSON char.
            c => out.push(c),
        }
    }
    out.push('"');
}

pub fn parse(src: &str) -> Result<Json, JsonError> {
    if src.len() > MAX_INPUT_BYTES {
        return Err(JsonError {
            offset: 0,
            msg: format!("input exceeds the {MAX_INPUT_BYTES}-byte cap"),
        });
    }
    let mut p = Parser {
        bytes: src.as_bytes(),
        src,
        pos: 0,
    };
    p.skip_ws();
    let v = p.value(0)?;
    p.skip_ws();
    if p.pos != p.bytes.len() {
        return Err(p.err("trailing content after the JSON value"));
    }
    Ok(v)
}

struct Parser<'s> {
    bytes: &'s [u8],
    src: &'s str,
    pos: usize,
}

impl<'s> Parser<'s> {
    fn err(&self, msg: impl Into<String>) -> JsonError {
        JsonError {
            offset: self.pos,
            msg: msg.into(),
        }
    }

    fn peek(&self) -> u8 {
        self.bytes.get(self.pos).copied().unwrap_or(0)
    }

    fn skip_ws(&mut self) {
        while matches!(self.peek(), b' ' | b'\t' | b'\r' | b'\n') {
            self.pos += 1;
        }
    }

    fn expect(&mut self, b: u8) -> Result<(), JsonError> {
        if self.peek() == b {
            self.pos += 1;
            Ok(())
        } else {
            Err(self.err(format!("expected `{}`", b as char)))
        }
    }

    fn value(&mut self, depth: u32) -> Result<Json, JsonError> {
        if depth > MAX_DEPTH {
            return Err(self.err(format!("nesting deeper than {MAX_DEPTH} levels")));
        }
        match self.peek() {
            b'{' => self.object(depth),
            b'[' => self.array(depth),
            b'"' => Ok(Json::Str(self.string()?)),
            b'-' | b'0'..=b'9' => self.number(),
            b't' | b'f' => self.boolean(),
            b'n' => Err(self.err("`null` is not a valid extern value: every extern needs a value")),
            0 => Err(self.err("unexpected end of input")),
            c => Err(self.err(format!("unexpected character `{}`", c as char))),
        }
    }

    fn object(&mut self, depth: u32) -> Result<Json, JsonError> {
        self.expect(b'{')?;
        let mut fields: Vec<(String, Json)> = Vec::new();
        self.skip_ws();
        if self.peek() == b'}' {
            self.pos += 1;
            return Ok(Json::Object(fields));
        }
        loop {
            self.skip_ws();
            let key_offset = self.pos;
            let key = self.string().map_err(|e| JsonError {
                offset: e.offset,
                msg: format!("object key: {}", e.msg),
            })?;
            if fields.iter().any(|(k, _)| *k == key) {
                return Err(JsonError {
                    offset: key_offset,
                    msg: format!("duplicate key `{key}`: last-wins is how wrong values ship"),
                });
            }
            self.skip_ws();
            self.expect(b':')?;
            self.skip_ws();
            let v = self.value(depth + 1)?;
            fields.push((key, v));
            self.skip_ws();
            match self.peek() {
                b',' => {
                    self.pos += 1;
                    self.skip_ws();
                    if self.peek() == b'}' {
                        return Err(self.err("trailing comma (not valid JSON)"));
                    }
                }
                b'}' => {
                    self.pos += 1;
                    return Ok(Json::Object(fields));
                }
                _ => return Err(self.err("expected `,` or `}` in object")),
            }
        }
    }

    fn array(&mut self, depth: u32) -> Result<Json, JsonError> {
        self.expect(b'[')?;
        let mut items = Vec::new();
        self.skip_ws();
        if self.peek() == b']' {
            self.pos += 1;
            return Ok(Json::Array(items));
        }
        loop {
            self.skip_ws();
            items.push(self.value(depth + 1)?);
            self.skip_ws();
            match self.peek() {
                b',' => {
                    self.pos += 1;
                    self.skip_ws();
                    if self.peek() == b']' {
                        return Err(self.err("trailing comma (not valid JSON)"));
                    }
                }
                b']' => {
                    self.pos += 1;
                    return Ok(Json::Array(items));
                }
                _ => return Err(self.err("expected `,` or `]` in array")),
            }
        }
    }

    fn string(&mut self) -> Result<String, JsonError> {
        self.expect(b'"')?;
        let mut out = String::new();
        loop {
            match self.peek() {
                b'"' => {
                    self.pos += 1;
                    return Ok(out);
                }
                b'\\' => {
                    self.pos += 1;
                    match self.peek() {
                        b'"' => {
                            out.push('"');
                            self.pos += 1;
                        }
                        b'\\' => {
                            out.push('\\');
                            self.pos += 1;
                        }
                        c => {
                            return Err(self.err(format!(
                                "unsupported escape `\\{}`: hex keys and timestamps never \
                                 need escapes beyond \\\" and \\\\",
                                c as char
                            )));
                        }
                    }
                }
                0 => return Err(self.err("unterminated string")),
                c if c < 0x20 => return Err(self.err("raw control character in string")),
                c if c.is_ascii() => {
                    out.push(c as char);
                    self.pos += 1;
                }
                _ => {
                    // Non-ASCII UTF-8 passthrough, full character.
                    let Some(ch) = self.src[self.pos..].chars().next() else {
                        // Unreachable: peek() returned Some and src is
                        // valid UTF-8. Degrade gracefully, never panic.
                        return Err(self.err("internal: lost UTF-8 alignment"));
                    };
                    out.push(ch);
                    self.pos += ch.len_utf8();
                }
            }
        }
    }

    fn number(&mut self) -> Result<Json, JsonError> {
        let start = self.pos;
        let neg = self.peek() == b'-';
        if neg {
            self.pos += 1;
        }
        let digits_start = self.pos;
        while self.peek().is_ascii_digit() {
            self.pos += 1;
        }
        if self.pos == digits_start {
            return Err(self.err("expected digits"));
        }
        // JSON forbids leading zeros.
        let digits = &self.src[digits_start..self.pos];
        if digits.len() > 1 && digits.starts_with('0') {
            return Err(JsonError {
                offset: start,
                msg: "leading zeros are not valid JSON".into(),
            });
        }
        match self.peek() {
            b'.' | b'e' | b'E' => {
                return Err(self.err(
                    "floats/exponents are not valid extern values: an `Int` extern takes \
                     a plain integer",
                ));
            }
            _ => {}
        }
        let mut value: i128 = 0;
        for b in digits.bytes() {
            value = value
                .checked_mul(10)
                .and_then(|v| v.checked_add((b - b'0') as i128))
                .ok_or_else(|| JsonError {
                    offset: start,
                    msg: "integer exceeds 128-bit precision".into(),
                })?;
        }
        Ok(Json::Int(if neg { -value } else { value }))
    }

    fn boolean(&mut self) -> Result<Json, JsonError> {
        if self.src[self.pos..].starts_with("true") {
            self.pos += 4;
            Ok(Json::Bool(true))
        } else if self.src[self.pos..].starts_with("false") {
            self.pos += 5;
            Ok(Json::Bool(false))
        } else {
            Err(self.err("unexpected token"))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ok(src: &str) -> Json {
        parse(src).unwrap_or_else(|e| panic!("{src:?}: {e:?}"))
    }
    fn err_containing(src: &str, needle: &str) {
        let e = parse(src).expect_err(&format!("expected error for {src:?}"));
        assert!(e.msg.contains(needle), "for {src:?}: {e:?}");
    }

    #[test]
    fn valid_shapes() {
        assert_eq!(ok("42"), Json::Int(42));
        assert_eq!(ok("-7"), Json::Int(-7));
        assert_eq!(ok("0"), Json::Int(0));
        assert_eq!(ok("true"), Json::Bool(true));
        assert_eq!(ok(r#""0xab""#), Json::Str("0xab".into()));
        assert_eq!(ok("\"\u{a7}\""), Json::Str("\u{a7}".into()));
        assert_eq!(ok(r#""a\"b\\c""#), Json::Str("a\"b\\c".into()));
        assert_eq!(ok("[1, 2]"), Json::Array(vec![Json::Int(1), Json::Int(2)]));
        assert_eq!(ok("[]"), Json::Array(vec![]));
        assert_eq!(
            ok(r#"{ "a": 1, "b": [true] }"#),
            Json::Object(vec![
                ("a".into(), Json::Int(1)),
                ("b".into(), Json::Array(vec![Json::Bool(true)]))
            ])
        );
        assert_eq!(ok("{}"), Json::Object(vec![]));
    }

    #[test]
    fn rejections_teach() {
        err_containing("1.5", "floats");
        err_containing("1e3", "floats");
        err_containing("null", "null");
        err_containing(r#"{"a":1,"a":2}"#, "duplicate key");
        err_containing("[1,2,]", "trailing comma");
        err_containing(r#"{"a":1,}"#, "trailing comma");
        err_containing("01", "leading zeros");
        err_containing(r#""a\n""#, "escape");
        err_containing("\"a\tb\"", "control");
        err_containing("\"abc", "unterminated");
        err_containing("42 43", "trailing content");
        err_containing("", "end of input");
        let deep = format!("{}1{}", "[".repeat(100), "]".repeat(100));
        err_containing(&deep, "nesting");
    }

    #[test]
    fn total_on_ascii_pairs() {
        for a in 0..128u8 {
            for b in 0..128u8 {
                let buf = [a, b];
                if let Ok(s) = std::str::from_utf8(&buf) {
                    let _ = parse(s); // must not panic
                }
            }
        }
    }

    #[test]
    fn deterministic() {
        let src = r#"{"keys": ["0xaa", "0xbb"], "M": 2}"#;
        assert_eq!(parse(src), parse(src));
    }

    #[test]
    fn serialize_escapes_exactly() {
        // The output path must escape per standard JSON, not the strict subset.
        assert_eq!(to_string(&Json::Str("a\"b\\c".into())), r#""a\"b\\c""#);
        assert_eq!(
            to_string(&Json::Str("line\ntab\t".into())),
            r#""line\ntab\t""#
        );
        assert_eq!(to_string(&Json::Str("\u{01}".into())), "\"\\u0001\"");
        assert_eq!(to_string(&Json::Int(-7)), "-7");
        assert_eq!(to_string(&Json::Bool(true)), "true");
        assert_eq!(
            to_string(&Json::Object(vec![
                ("a".into(), Json::Int(1)),
                ("b".into(), Json::Array(vec![Json::Bool(false)])),
            ])),
            r#"{"a":1,"b":[false]}"#
        );
        // Non-ASCII passes through as a literal UTF-8 character.
        assert_eq!(to_string(&Json::Str("\u{a7}".into())), "\"\u{a7}\"");
    }

    #[test]
    fn serialize_round_trips_through_parser() {
        // For values inside the strict subset (no control chars), serialize then
        // re-parse must reproduce the value exactly.
        for src in [
            "42",
            "-7",
            "true",
            r#""0xab""#,
            r#"[1, 2, true]"#,
            r#"{"keys": ["0xaa", "0xbb"], "m": 2, "nested": {"x": [-1]}}"#,
        ] {
            let v = parse(src).unwrap();
            let reparsed = parse(&to_string(&v)).unwrap();
            assert_eq!(v, reparsed, "round-trip failed for {src:?}");
        }
    }
}
