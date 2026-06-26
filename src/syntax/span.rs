//! Byte-offset spans and line/column mapping.
//!
//! Spans are half-open byte ranges `[start, end)` into the original source,
//! the same convention as the language's `..` ranges. Offsets are `u32`
//! (sources larger than 4 GiB are rejected up front by the lexer).

/// Half-open byte range into the source. `start <= end` always holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(start: u32, end: u32) -> Span {
        debug_assert!(start <= end, "inverted span {start}..{end}");
        Span { start, end }
    }

    /// The empty span at a position (used for EOF and zero-width diagnostics).
    pub fn at(pos: u32) -> Span {
        Span {
            start: pos,
            end: pos,
        }
    }

    pub fn len(self) -> u32 {
        self.end - self.start
    }

    pub fn is_empty(self) -> bool {
        self.start == self.end
    }

    /// Slice the source text this span covers. Panics only on a span that was
    /// not produced from `text`, a programmer error, not an input error.
    pub fn slice(self, text: &str) -> &str {
        &text[self.start as usize..self.end as usize]
    }
}

/// 1-based line/column position. Column counts characters (not bytes), so
/// diagnostics point where a human is looking.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LineCol {
    pub line: u32,
    pub col: u32,
}

/// Precomputed line-start table for offset to line/col conversion.
///
/// Newline handling: `\n` terminates a line; `\r` is treated as ordinary
/// whitespace (so `\r\n` sources map correctly, with the `\r` belonging to the
/// preceding line).
pub struct LineIndex {
    /// Byte offset of the start of each line. `line_starts[0] == 0` always.
    line_starts: Vec<u32>,
}

impl LineIndex {
    pub fn new(src: &str) -> LineIndex {
        let mut line_starts = vec![0u32];
        for (i, b) in src.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push((i + 1) as u32);
            }
        }
        LineIndex { line_starts }
    }

    /// The text of 1-based `line` (without the trailing `\n` or `\r`). Empty
    /// for an out-of-range line. Used by the diagnostic snippet renderer.
    pub fn line_str<'a>(&self, src: &'a str, line: u32) -> &'a str {
        let i = line.saturating_sub(1) as usize;
        if line == 0 || i >= self.line_starts.len() {
            return "";
        }
        let start = self.line_starts[i] as usize;
        let end = self
            .line_starts
            .get(i + 1)
            .map(|&s| s as usize)
            .unwrap_or(src.len());
        let s = &src[start..end.min(src.len())];
        let s = s.strip_suffix('\n').unwrap_or(s);
        s.strip_suffix('\r').unwrap_or(s)
    }

    /// Map a byte offset to 1-based line/column. Offsets past the end clamp to
    /// the final position (useful for EOF diagnostics).
    pub fn line_col(&self, src: &str, offset: u32) -> LineCol {
        let offset = offset.min(src.len() as u32);
        // partition_point gives the number of line starts <= offset; the line is the last one.
        let line_idx = self.line_starts.partition_point(|&s| s <= offset) - 1;
        let line_start = self.line_starts[line_idx];
        let col_chars = src[line_start as usize..offset as usize].chars().count();
        LineCol {
            line: (line_idx + 1) as u32,
            col: (col_chars + 1) as u32,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_col_basics() {
        let src = "ab\ncde\n\nf";
        let idx = LineIndex::new(src);
        let lc = |off| {
            let p = idx.line_col(src, off);
            (p.line, p.col)
        };
        assert_eq!(lc(0), (1, 1)); // a
        assert_eq!(lc(1), (1, 2)); // b
        assert_eq!(lc(2), (1, 3)); // the \n itself: still line 1
        assert_eq!(lc(3), (2, 1)); // c
        assert_eq!(lc(6), (2, 4)); // end of "cde"
        assert_eq!(lc(7), (3, 1)); // empty line
        assert_eq!(lc(8), (4, 1)); // f
        assert_eq!(lc(9), (4, 2)); // EOF position
        assert_eq!(lc(99), (4, 2)); // clamped
    }

    #[test]
    fn line_col_counts_chars_not_bytes() {
        let src = "\u{a7}\u{a7}x"; // each leading char is 2 bytes in UTF-8
        let idx = LineIndex::new(src);
        assert_eq!(idx.line_col(src, 4).col, 3); // offset 4 = start of 'x' = 3rd char
    }

    #[test]
    fn crlf_maps_to_next_line() {
        let src = "a\r\nb";
        let idx = LineIndex::new(src);
        assert_eq!(idx.line_col(src, 3).line, 2);
    }

    #[test]
    fn empty_source() {
        let idx = LineIndex::new("");
        let p = idx.line_col("", 0);
        assert_eq!((p.line, p.col), (1, 1));
    }
}
