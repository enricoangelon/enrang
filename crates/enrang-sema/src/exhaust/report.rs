//! The diagnostics of one `match` (plan d.13, e; SPEC 6 S:1134-1135; G12).
//!
//! EN0501, at the subject, names the first value no arm handles, in the order of
//! `witness::missing`: `` `match` doesn't handle `Shape.Empty` `` with the case's
//! declaration as a secondary; `` doesn't handle every `Shape.Circle` `` when only
//! guarded arms list the case, with `only when this is true` under each guard;
//! `` doesn't handle `null` ``; `doesn't handle a present null` for the null of
//! an inner level, which no arm can name; `` doesn't handle every `i64` `` for
//! numbers, strings and other types, which only `default` completes; and
//! `` `match (true)` needs a `default` arm `` when its conditions, which cover
//! nothing, leave a value (A:916). Its help
//! inserts one arm per missing value, or a `default` arm where one is needed, at
//! the start of the line of the `match`'s closing `}`, indented like the first
//! arm (G12), or before the `}` of a one-line `match`.
//!
//! EN0503, a warning, points at the first value of an arm no value reaches, or
//! at each unreachable value of an arm that some value reaches, with the value
//! above that alone covers it as a secondary.

use enrang_base::{BytePos, FileOrigin, SourceMap, Span};
use enrang_diag::{Code, Diagnostic, Edit, Help};
use enrang_hir::{AdtId, Arm, Expr, LangItem, Tcx, VariantValue};

use super::lower::{Base, Column};
use super::matrix::satisfiable;
use super::witness::{Witness, matches};
use super::{Analysis, ArmPat, Guard};

/// The body of every arm a help inserts.
const ARM_BODY: &str = "panic(\"unhandled\")";

/// One `match`, as the report reads it.
pub(crate) struct Match<'a> {
    /// The whole `match` expression, which ends at its closing `}`.
    pub span: Span,
    pub subject: &'a Expr,
    pub arms: &'a [Arm],
    pub column: &'a Column,
    pub pats: &'a [Vec<ArmPat>],
}

/// EN0501 when values are missing, then EN0503 in arm order.
pub(crate) fn diagnostics(tcx: &Tcx, m: &Match<'_>, analysis: &Analysis) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    if let Some(d) = non_exhaustive(tcx, m, analysis) {
        out.push(d);
    }
    let map = tcx.map();
    for (a, verdicts) in analysis.values.iter().enumerate() {
        if verdicts.iter().all(|v| !v.reachable) {
            out.push(unreachable(
                map,
                m,
                analysis,
                a,
                0,
                "this arm is never reached",
            ));
        } else {
            for (v, verdict) in verdicts.iter().enumerate() {
                if !verdict.reachable {
                    out.push(unreachable(
                        map,
                        m,
                        analysis,
                        a,
                        v,
                        "this value is never reached",
                    ));
                }
            }
        }
    }
    out
}

/// EN0503 at value `v` of arm `a`.
fn unreachable(
    map: &SourceMap,
    m: &Match<'_>,
    analysis: &Analysis,
    a: usize,
    v: usize,
    message: &str,
) -> Diagnostic {
    let label = if satisfiable(&m.pats[a][v].pat, &m.column.space) {
        "every value it matches is handled above"
    } else {
        "no value can match this"
    };
    let d = Diagnostic::new(Code::EN0503, message, value_span(map, &m.arms[a], v), label);
    match analysis.values[a][v].covered_by {
        Some((ca, cv)) => {
            d.with_secondary(value_span(map, &m.arms[ca], cv), "already handled here")
        }
        None => d,
    }
}

/// Where value `v` of `arm` is: its span (D7), or the `default` keyword.
fn value_span(map: &SourceMap, arm: &Arm, v: usize) -> Span {
    if arm.values.is_empty() {
        return keyword_span(map, arm.span, "default");
    }
    arm.value_spans.get(v).copied().unwrap_or(arm.span)
}

/// The first `word.len()` bytes of `span` when its text starts with `word`.
fn keyword_span(map: &SourceMap, span: Span, word: &str) -> Span {
    if !span.is_dummy() && map.text(span).starts_with(word) {
        Span {
            lo: span.lo,
            hi: span.lo + word.len() as u32,
        }
    } else {
        span
    }
}

/// What a missing value prints as.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Missing {
    /// A value an arm can name, as the arm writes it.
    Code(String),
    /// The `null` of an inner level, which `null` never names (S:1134).
    PresentNull,
    /// A value of this type, which only `default` covers.
    Every(String),
}

fn describe(tcx: &Tcx, column: &Column, w: &Witness) -> Missing {
    let (atom, depth) = w.peel();
    match (atom, column.base) {
        (Witness::Null, _) if depth == 0 => Missing::Code("null".to_owned()),
        (Witness::Null, _) => Missing::PresentNull,
        (Witness::Case(c), Base::Enum(adt)) => Missing::Code(case_name(tcx, adt, *c)),
        (Witness::Case(_), Base::ConstBool(b)) => Missing::Code(b.to_string()),
        (Witness::Bool(b), _) => Missing::Code(b.to_string()),
        _ => Missing::Every(tcx.ty_string(column.levels[depth])),
    }
}

/// A case as an arm names it: `Shape.Empty`, `Ok` and `Err` bare (S:1133), a
/// string-literal union's value as its literal.
fn case_name(tcx: &Tcx, adt: AdtId, c: u32) -> String {
    let def = tcx.adt(adt);
    let Some(e) = def.as_enum() else {
        return def.name.to_string();
    };
    let v = &e.variants[c as usize];
    if e.str_union {
        let text = match v.value {
            Some(VariantValue::Text(id)) => tcx.str(id).to_string(),
            _ => v.name.to_string(),
        };
        quote(&text)
    } else if tcx.is_lang_adt(adt, LangItem::Result) {
        v.name.to_string()
    } else {
        format!("{}.{}", def.name, v.name)
    }
}

/// `text` as a string literal.
fn quote(text: &str) -> String {
    let mut out = String::from("\"");
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            _ => out.push(c),
        }
    }
    out.push('"');
    out
}

/// A user enum's case named by `w`, for the plural of S:1134's help.
fn user_case_name(tcx: &Tcx, column: &Column, w: &Witness) -> Option<String> {
    let (Witness::Case(c), _) = w.peel() else {
        return None;
    };
    let Base::Enum(adt) = column.base else {
        return None;
    };
    let e = tcx.adt(adt).as_enum()?;
    if e.str_union || tcx.is_lang_adt(adt, LangItem::Result) {
        return None;
    }
    Some(e.variants[*c as usize].name.to_string())
}

/// The declaration of the case `w` names, when a user file holds it: the case's
/// name, or a string-literal union's literal.
fn declared_span(tcx: &Tcx, column: &Column, w: &Witness) -> Option<Span> {
    let (Witness::Case(c), _) = w.peel() else {
        return None;
    };
    let Base::Enum(adt) = column.base else {
        return None;
    };
    let e = tcx.adt(adt).as_enum()?;
    let v = e.variants.get(*c as usize)?;
    if v.span.is_dummy() {
        return None;
    }
    let map = tcx.map();
    if map.file_of(v.span.lo).origin != FileOrigin::User {
        return None;
    }
    if e.str_union {
        return Some(v.span);
    }
    Some(word_in(map, v.span, v.name.as_str()))
}

/// The first whole-word `word` inside `span` outside a string literal (a
/// decorator's argument, `@was("Old")`), or `span` itself.
fn word_in(map: &SourceMap, span: Span, word: &str) -> Span {
    let text = map.text(span);
    let ident = |c: char| c.is_alphanumeric() || c == '_' || c == '$';
    let mut in_string = false;
    let mut prev: Option<char> = None;
    for (at, c) in text.char_indices() {
        if in_string {
            if c == '"' && prev != Some('\\') {
                in_string = false;
            }
        } else if c == '"' {
            in_string = true;
        } else if text[at..].starts_with(word)
            && !prev.is_some_and(ident)
            && !text[at + word.len()..].chars().next().is_some_and(ident)
        {
            let lo = span.lo + at as u32;
            return Span {
                lo,
                hi: lo + word.len() as u32,
            };
        }
        prev = Some(c);
    }
    span
}

/// The guards of the arms whose guarded values match `w`.
fn guards_matching(m: &Match<'_>, w: &Witness) -> Vec<Span> {
    m.arms
        .iter()
        .zip(m.pats)
        .filter(|(_, pats)| {
            pats.iter()
                .any(|p| p.guard == Guard::Arm && matches(&p.pat, w))
        })
        .filter_map(|(arm, _)| arm.guard.as_ref().map(|g| g.span))
        .collect()
}

/// `Circle` as `circles`, `BadSector` as `bad sectors`: the words of a case's
/// name in lower case, the last one plural.
pub(crate) fn plural(name: &str) -> String {
    let chars: Vec<char> = name.chars().collect();
    let mut words: Vec<String> = vec![String::new()];
    for (i, &c) in chars.iter().enumerate() {
        if c == '_' {
            words.push(String::new());
            continue;
        }
        let prev = i.checked_sub(1).map(|p| chars[p]);
        let next = chars.get(i + 1).copied();
        let boundary = c.is_uppercase()
            && prev.is_some_and(|p| {
                p.is_lowercase()
                    || p.is_ascii_digit()
                    || (p.is_uppercase() && next.is_some_and(char::is_lowercase))
            });
        if boundary {
            words.push(String::new());
        }
        words.last_mut().expect("a word").extend(c.to_lowercase());
    }
    words.retain(|w| !w.is_empty());
    let Some(last) = words.pop() else {
        return "values".to_owned();
    };
    let consonant_y = last.ends_with('y')
        && !last[..last.len() - 1].ends_with(['a', 'e', 'i', 'o', 'u'])
        && last.len() > 1;
    let last = if consonant_y {
        format!("{}ies", &last[..last.len() - 1])
    } else if ["s", "x", "z", "ch", "sh"]
        .iter()
        .any(|end| last.ends_with(end))
    {
        format!("{last}es")
    } else {
        format!("{last}s")
    };
    words.push(last);
    words.join(" ")
}

/// EN0501, when some value reaches no arm.
fn non_exhaustive(tcx: &Tcx, m: &Match<'_>, analysis: &Analysis) -> Option<Diagnostic> {
    let first = analysis.missing.first()?;
    let missing: Vec<Missing> = analysis
        .missing
        .iter()
        .map(|w| describe(tcx, m.column, w))
        .collect();
    let condition = match m.column.base {
        Base::ConstBool(b) if m.pats.iter().flatten().any(|p| p.guard == Guard::Own) => Some(b),
        _ => None,
    };
    let guards = guards_matching(m, first);
    let mut d = match (condition, &missing[0]) {
        (Some(b), _) => Diagnostic::new(
            Code::EN0501,
            format!("`match ({b})` needs a `default` arm"),
            m.subject.span,
            "no arm runs when every condition is false",
        ),
        (None, Missing::Code(x)) if guards.is_empty() => {
            let d = Diagnostic::new(
                Code::EN0501,
                format!("`match` doesn't handle `{x}`"),
                m.subject.span,
                format!("missing `{x}`"),
            );
            match declared_span(tcx, m.column, first) {
                Some(span) => d.with_secondary(span, format!("`{x}` is declared here")),
                None => d,
            }
        }
        (None, Missing::Code(x)) => guards.iter().fold(
            Diagnostic::new(
                Code::EN0501,
                format!("`match` doesn't handle every `{x}`"),
                m.subject.span,
                format!("missing other `{x}` values"),
            ),
            |d, &g| d.with_secondary(g, "only when this is true"),
        ),
        (None, Missing::PresentNull) => Diagnostic::new(
            Code::EN0501,
            "`match` doesn't handle a present null",
            m.subject.span,
            "missing a present null",
        ),
        (None, Missing::Every(t)) => Diagnostic::new(
            Code::EN0501,
            format!("`match` doesn't handle every `{t}`"),
            m.subject.span,
            format!("only a `default` arm handles every `{t}`"),
        ),
    };
    let codes: Vec<&str> = missing
        .iter()
        .filter_map(|x| match x {
            Missing::Code(code) => Some(code.as_str()),
            _ => None,
        })
        .collect();
    let (text, arms) = if condition.is_some() || codes.len() < missing.len() {
        (
            "add `default => ...,`".to_owned(),
            vec![format!("default => {ARM_BODY},")],
        )
    } else {
        let arms = codes
            .iter()
            .map(|code| format!("{code} => {ARM_BODY},"))
            .collect();
        let text = if analysis.missing == [Witness::Null] {
            "add `null => ...,`".to_owned()
        } else if codes.len() == 1 && !guards.is_empty() {
            match user_case_name(tcx, m.column, first) {
                Some(name) => format!(
                    "add an arm for the other {}: `{} => ...,`",
                    plural(&name),
                    codes[0]
                ),
                None => format!("add an arm without a guard: `{} => ...,`", codes[0]),
            }
        } else {
            let listed: Vec<String> = codes.iter().map(|c| format!("`{c} => ...`")).collect();
            format!("add {}, or a `default` arm", listed.join(", "))
        };
        (text, arms)
    };
    d = d.with_help(Help::suggest(text, arm_edits(tcx.map(), m, &arms)));
    Some(d)
}

/// Whether the first token of `text` after `from`, past whitespace and comments
/// (`//` to the line's end, `/* */` unnested, as the lexer reads them), is a `,`.
fn comma_follows(text: &str, mut from: usize) -> bool {
    loop {
        let rest = &text[from..];
        let token = rest.trim_start();
        from += rest.len() - token.len();
        if token.starts_with("//") {
            match token.find('\n') {
                Some(end) => from += end,
                None => return false,
            }
        } else if let Some(body) = token.strip_prefix("/*") {
            match body.find("*/") {
                Some(end) => from += 2 + end + 2,
                None => return false,
            }
        } else {
            return token.starts_with(',');
        }
    }
}

/// The edits that add `arms` to the `match`: one line each at the start of the
/// line of its closing `}`, indented like its first arm (or two spaces deeper
/// than the `}` when it has none), with a comma after the last arm if it has
/// none; in a `match` whose `}` follows other text on its line, the arms go
/// before the `}`. None when the `match` has no place in a source.
fn arm_edits(map: &SourceMap, m: &Match<'_>, arms: &[String]) -> Vec<Edit> {
    if m.span.is_empty() {
        return Vec::new();
    }
    let close = BytePos(m.span.hi.0 - 1);
    let file = map.file_of(close);
    let text = &*file.text;
    let offset_of = |pos: BytePos| (pos.0 - file.start.0) as usize;
    let at = |offset: usize| BytePos(file.start.0 + offset as u32);
    let close_at = offset_of(close);
    if text.as_bytes().get(close_at) != Some(&b'}') {
        return Vec::new();
    }
    let line_of = |offset: usize| text[..offset].rfind('\n').map_or(0, |i| i + 1);
    let close_line = line_of(close_at);
    let before_close = &text[close_line..close_at];
    let first_line = m
        .arms
        .first()
        .filter(|a| !a.span.is_dummy())
        .map(|a| line_of(offset_of(a.span.lo)));
    let last_end = m
        .arms
        .last()
        .filter(|a| !a.span.is_dummy())
        .map(|a| offset_of(a.span.hi));
    let comma = last_end.is_some_and(|end| comma_follows(&text[..close_at], end));
    if before_close.trim().is_empty() {
        let indent = match first_line {
            Some(line) => {
                let rest = &text[line..];
                rest[..rest.len() - rest.trim_start_matches([' ', '\t']).len()].to_owned()
            }
            None => format!("{before_close}  "),
        };
        let mut edits = Vec::new();
        if let Some(end) = last_end.filter(|_| !comma) {
            edits.push(Edit::insert(at(end), ","));
        }
        let lines: String = arms.iter().map(|arm| format!("{indent}{arm}\n")).collect();
        edits.push(Edit::insert(at(close_line), lines));
        edits
    } else {
        let lo = offset_of(m.span.lo);
        let end = lo + text[lo..close_at].trim_end().len();
        let prefix = if last_end.is_none() || comma {
            " "
        } else {
            ", "
        };
        let suffix = if end == close_at { " " } else { "" };
        vec![Edit::insert(
            at(end),
            format!("{prefix}{}{suffix}", arms.join(" ")),
        )]
    }
}
