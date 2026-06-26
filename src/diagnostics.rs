//! Diagnostics: every message the compiler emits, with a stable code and a span.
//!
//! Diagnostics teach: the primary message names what is wrong, and a `help:` or
//! `note:` subdiagnostic names the fix. A diagnostic without an actionable next
//! step is a bug.
//!
//! Rendering follows the conventions of modern compilers (rustc/clang): a
//! lowercase, period-free primary message; a `--> file:line:col` location; the
//! offending source line with a `^^^^` caret underline; and `= help:`/`= note:`
//! lines beneath. Color is applied only on a TTY (and never when `NO_COLOR` is
//! set). The renderer is hand-rolled and zero-dependency.

use crate::syntax::span::{LineIndex, Span};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
    /// A subdiagnostic level: only ever attached to an Error/Warning via
    /// `notes`, never pushed as a standalone top-level diagnostic.
    Note,
    Help,
}

impl Severity {
    fn word(self) -> &'static str {
        match self {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Note => "note",
            Severity::Help => "help",
        }
    }
}

/// A `note:` or `help:` line attached beneath a primary diagnostic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubDiag {
    pub severity: Severity,
    pub message: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    /// Top-level diagnostics are always `Error` or `Warning`.
    pub severity: Severity,
    /// Stable, grep-able code, e.g. `lex/int-underscore`. The prefix names the
    /// concern domain (not the source file). Never reused for a different
    /// meaning once shipped.
    pub code: &'static str,
    pub message: String,
    pub span: Span,
    /// Optional short label printed after the caret underline ("this is `Bytes`").
    pub label: Option<String>,
    /// `note:`/`help:` lines printed beneath the snippet.
    pub notes: Vec<SubDiag>,
}

impl Diagnostic {
    pub fn error(code: &'static str, message: impl Into<String>, span: Span) -> Diagnostic {
        Diagnostic {
            severity: Severity::Error,
            code,
            message: message.into(),
            span,
            label: None,
            notes: Vec::new(),
        }
    }

    pub fn warning(code: &'static str, message: impl Into<String>, span: Span) -> Diagnostic {
        Diagnostic {
            severity: Severity::Warning,
            code,
            message: message.into(),
            span,
            label: None,
            notes: Vec::new(),
        }
    }

    /// Short text printed after the caret underline.
    pub fn with_label(mut self, label: impl Into<String>) -> Diagnostic {
        self.label = Some(label.into());
        self
    }

    /// Attach a `help:` line (the actionable fix).
    pub fn with_help(mut self, message: impl Into<String>) -> Diagnostic {
        self.notes.push(SubDiag {
            severity: Severity::Help,
            message: message.into(),
        });
        self
    }

    /// Attach a `note:` line (context that is not itself a fix).
    pub fn with_note(mut self, message: impl Into<String>) -> Diagnostic {
        self.notes.push(SubDiag {
            severity: Severity::Note,
            message: message.into(),
        });
        self
    }

    /// Render to the multi-line snippet form. `color` enables ANSI styling
    /// (the caller computes it once from the TTY + `NO_COLOR`). Falls back to a
    /// single `--> path:line:col` location line when there is no source line to
    /// show (EOF / empty source).
    pub fn render(&self, path: &str, src: &str, index: &LineIndex, color: bool) -> String {
        let st = Style::new(color);
        let a = st.accent;
        let r = st.reset;
        let b = st.bold;
        let sev = self.severity.word();
        let sev_col = self.severity_color(&st);
        let start = index.line_col(src, self.span.start);
        let bar = " ".repeat(start.line.to_string().len());

        // Header: `error[code]: message`
        let mut out = format!("{sev_col}{sev}[{}]{r}: {b}{}{r}", self.code, self.message);

        let line_text = index.line_str(src, start.line);
        if line_text.is_empty() {
            out.push_str(&format!(
                "\n{a}{bar} -->{r} {path}:{}:{}",
                start.line, start.col
            ));
        } else {
            let shown = line_text.replace('\t', " "); // 1 char -> 1 col: caret stays aligned
            let end = index.line_col(src, self.span.end);
            let caret_len = if self.span.is_empty() {
                1
            } else if end.line == start.line {
                src[self.span.start as usize..self.span.end as usize]
                    .chars()
                    .count()
                    .max(1)
            } else {
                // multi-line span: underline to the end of the first line
                line_text
                    .chars()
                    .count()
                    .saturating_sub((start.col - 1) as usize)
                    .max(1)
            };
            let pad = " ".repeat((start.col - 1) as usize);
            let carets = "^".repeat(caret_len);
            let label = self
                .label
                .as_deref()
                .map(|l| format!(" {l}"))
                .unwrap_or_default();
            out.push_str(&format!(
                "\n{a}{bar} -->{r} {path}:{}:{}",
                start.line, start.col
            ));
            out.push_str(&format!("\n{a}{bar} |{r}"));
            out.push_str(&format!("\n{a}{} |{r} {shown}", start.line));
            out.push_str(&format!("\n{a}{bar} |{r} {pad}{sev_col}{carets}{label}{r}"));
        }

        if !self.notes.is_empty() {
            if !line_text.is_empty() {
                out.push_str(&format!("\n{a}{bar} |{r}"));
            }
            for sub in &self.notes {
                let nc = if sub.severity == Severity::Help {
                    st.help
                } else {
                    st.note
                };
                out.push_str(&format!(
                    "\n{a}{bar} ={r} {nc}{}{r}: {}",
                    sub.severity.word(),
                    sub.message
                ));
            }
        }
        out
    }

    fn severity_color<'a>(&self, st: &'a Style) -> &'a str {
        match self.severity {
            Severity::Error => st.err,
            Severity::Warning => st.warn,
            Severity::Note => st.note,
            Severity::Help => st.help,
        }
    }
}

/// ANSI styling table. All fields are empty strings when color is disabled, so
/// the rendered output is byte-for-byte identical to the uncolored form.
struct Style {
    err: &'static str,
    warn: &'static str,
    note: &'static str,
    help: &'static str,
    accent: &'static str,
    bold: &'static str,
    reset: &'static str,
}

impl Style {
    fn new(color: bool) -> Style {
        if color {
            Style {
                err: "\x1b[1;31m",
                warn: "\x1b[1;33m",
                note: "\x1b[1m",
                help: "\x1b[1;36m",
                accent: "\x1b[1;34m",
                bold: "\x1b[1m",
                reset: "\x1b[0m",
            }
        } else {
            Style {
                err: "",
                warn: "",
                note: "",
                help: "",
                accent: "",
                bold: "",
                reset: "",
            }
        }
    }
}

/// Whether to emit ANSI color: only on a TTY, never when `NO_COLOR` is set,
/// forced on by `CLICOLOR_FORCE`. Zero-dependency `isatty`.
pub fn use_color(stderr: bool) -> bool {
    if std::env::var_os("NO_COLOR").is_some() {
        return false;
    }
    if matches!(std::env::var("CLICOLOR_FORCE").as_deref(), Ok(v) if v != "0") {
        return true;
    }
    is_tty(stderr)
}

#[cfg(unix)]
fn is_tty(stderr: bool) -> bool {
    // The C `isatty` symbol is in libc, which is always linked; declaring it
    // directly avoids a `libc` crate dependency.
    unsafe extern "C" {
        fn isatty(fd: i32) -> i32;
    }
    let fd = if stderr { 2 } else { 1 };
    unsafe { isatty(fd) == 1 }
}

#[cfg(not(unix))]
fn is_tty(_stderr: bool) -> bool {
    false
}

#[cfg(test)]
mod render_tests {
    use super::*;
    use crate::syntax::span::{LineIndex, Span};

    fn lines(src: &str, d: &Diagnostic, color: bool) -> Vec<String> {
        let idx = LineIndex::new(src);
        d.render("t.sl", src, &idx, color)
            .lines()
            .map(str::to_string)
            .collect()
    }

    #[test]
    fn snippet_layout_and_caret_alignment() {
        let src = "a\n  require x == y\nb\n";
        let at = src.find("==").unwrap() as u32;
        let d = Diagnostic::error("sema/type-mismatch", "type mismatch", Span::new(at, at + 2));
        let ls = lines(src, &d, false);
        assert_eq!(ls[0], "error[sema/type-mismatch]: type mismatch");
        assert_eq!(ls[1], "  --> t.sl:2:13");
        assert_eq!(ls[2], "  |");
        assert_eq!(ls[3], "2 |   require x == y");
        // The caret underlines exactly the span, aligned under it: the first
        // `^` sits at the same column as the `=` in the source line above.
        assert_eq!(ls[4].matches('^').count(), 2);
        assert_eq!(ls[4].find('^'), ls[3].find('='));
    }

    #[test]
    fn color_wraps_label_and_carets() {
        let src = "x == y\n";
        let d = Diagnostic::error("c/d", "m", Span::new(2, 4));
        let out = d.render("t.sl", src, &LineIndex::new(src), true);
        assert!(out.contains("\x1b[1;31merror[c/d]\x1b[0m"), "{out}");
        assert!(out.contains("\x1b[0m")); // resets present
        // color=false is byte-stable (no escape bytes at all)
        let plain = d.render("t.sl", src, &LineIndex::new(src), false);
        assert!(!plain.contains('\x1b'));
    }

    #[test]
    fn help_and_note_hang_below() {
        let src = "x == y\n";
        let d = Diagnostic::error("c/d", "m", Span::new(2, 4))
            .with_label("here")
            .with_help("do this instead")
            .with_note("background");
        let ls = lines(src, &d, false);
        assert_eq!(*ls.last().unwrap(), "  = note: background");
        assert!(ls.iter().any(|l| l == "  = help: do this instead"));
        assert!(ls.iter().any(|l| l.contains("^^ here"))); // label after carets
    }

    #[test]
    fn eof_fallback_has_no_snippet() {
        let src = ""; // empty source: no line to show
        let d = Diagnostic::error("lex/eof", "unexpected end of input", Span::at(0));
        let ls = lines(src, &d, false);
        assert_eq!(ls.len(), 2);
        assert_eq!(ls[0], "error[lex/eof]: unexpected end of input");
        assert_eq!(ls[1], "  --> t.sl:1:1");
    }

    #[test]
    fn tabs_keep_the_caret_aligned() {
        // A leading tab becomes one space (1 char -> 1 column); the caret still
        // lands under the target by char-column count.
        let src = "\tx == y\n";
        let at = src.find("==").unwrap() as u32;
        let d = Diagnostic::error("c/d", "m", Span::new(at, at + 2));
        let ls = lines(src, &d, false);
        assert!(!ls[3].contains('\t'), "tab expanded in shown source");
        assert_eq!(ls[4].find('^'), ls[3].find('='));
    }
}
