//! The machine renderer of `--error-format=json` (SPEC 13.1).
//!
//! One object per line, one per diagnostic, with the fields of the text form in a
//! fixed order. Spans are byte offsets into their file, so that an edit means the
//! same without the session that produced it, and every help lists its edits with
//! its applicability: `machine-applicable` ones can be applied unattended.

use std::fmt::Write;

use enrang_base::{SourceMap, Span};

use crate::diagnostic::{Diagnostic, Edit, Help, Label, Severity};

/// The `version` of every object. It changes when a field changes.
pub const JSON_VERSION: u32 = 1;

/// Renders one JSON object per diagnostic, each ending in a newline.
///
/// Panics if a span lies in no file of `map`, which is a compiler bug.
pub fn render_json(diags: &[Diagnostic], map: &SourceMap) -> String {
    let mut out = String::new();
    for diag in diags {
        write_diagnostic(diag, map, &mut out);
        out.push('\n');
    }
    out
}

fn write_diagnostic(diag: &Diagnostic, map: &SourceMap, out: &mut String) {
    let _ = write!(out, "{{\"version\":{JSON_VERSION},\"severity\":");
    write_string(diag.severity.name(), out);
    out.push_str(",\"code\":");
    match diag.severity {
        Severity::Note => out.push_str("null"),
        _ => write_string(diag.code.name(), out),
    }
    out.push_str(",\"message\":");
    write_string(&diag.message, out);
    out.push_str(",\"primary\":");
    write_label(&diag.primary, map, out);
    out.push_str(",\"secondary\":");
    write_list(&diag.secondary, out, |label, out| {
        write_label(label, map, out);
    });
    out.push_str(",\"entries\":");
    write_list(&diag.entries, out, |entry, out| {
        out.push_str("{\"kind\":");
        write_string(entry.kind.name(), out);
        out.push_str(",\"text\":");
        write_string(&entry.text, out);
        out.push('}');
    });
    out.push_str(",\"helps\":");
    write_list(&diag.helps, out, |help, out| write_help(help, map, out));
    out.push_str(",\"explain\":");
    match diag.explain_command() {
        Some(command) => write_string(&command, out),
        None => out.push_str("null"),
    }
    out.push('}');
}

fn write_label(label: &Label, map: &SourceMap, out: &mut String) {
    out.push_str("{\"text\":");
    write_string(&label.text, out);
    out.push_str(",\"span\":");
    if label.span.is_dummy() {
        out.push_str("null");
    } else {
        write_span(label.span, map, out);
    }
    out.push('}');
}

fn write_span(span: Span, map: &SourceMap, out: &mut String) {
    let file = map.file_of(span.lo);
    let hi = span.hi.clamp(span.lo, file.end());
    let (start, end) = (map.loc(span.lo), map.loc(hi));
    out.push_str("{\"file\":");
    write_string(&file.path.to_string_lossy(), out);
    let _ = write!(
        out,
        ",\"lo\":{},\"hi\":{},\"line\":{},\"col\":{},\"end_line\":{},\"end_col\":{}}}",
        span.lo.0 - file.start.0,
        hi.0 - file.start.0,
        start.line,
        start.col,
        end.line,
        end.col,
    );
}

fn write_help(help: &Help, map: &SourceMap, out: &mut String) {
    let (commands, edits): (Vec<&Edit>, Vec<&Edit>) =
        help.edits.iter().partition(|edit| edit.span.is_dummy());
    out.push_str("{\"message\":");
    write_string(&help.message, out);
    out.push_str(",\"applicability\":");
    write_string(help.applicability.name(), out);
    out.push_str(",\"edits\":");
    write_list(&edits, out, |edit, out| write_edit(edit, map, out));
    out.push_str(",\"commands\":");
    write_list(&commands, out, |edit, out| {
        write_string(&edit.replacement, out);
    });
    out.push('}');
}

fn write_edit(edit: &Edit, map: &SourceMap, out: &mut String) {
    let file = map.file_of(edit.span.lo);
    let hi = edit.span.hi.clamp(edit.span.lo, file.end());
    out.push_str("{\"file\":");
    write_string(&file.path.to_string_lossy(), out);
    let _ = write!(
        out,
        ",\"lo\":{},\"hi\":{},\"replacement\":",
        edit.span.lo.0 - file.start.0,
        hi.0 - file.start.0,
    );
    write_string(&edit.replacement, out);
    out.push('}');
}

fn write_list<T>(items: &[T], out: &mut String, mut write: impl FnMut(&T, &mut String)) {
    out.push('[');
    for (index, item) in items.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        write(item, out);
    }
    out.push(']');
}

fn write_string(text: &str, out: &mut String) {
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c < ' ' || c == '\u{7f}' => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}
