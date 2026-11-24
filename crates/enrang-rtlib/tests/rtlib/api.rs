//! The stub against the names SPEC lists: the preludes of 8.1, the `core` API of
//! 8.2 with the sections its table points to, and the must-use methods of 8.3.
//! Names are read from the doc, so a name added there fails here until the stub
//! declares it.

use std::collections::BTreeSet;

use enrang_rtlib::{all_modules, lookup};
use enrang_testkit::Harness;

use crate::support::{
    Called, Span, calls, declared, in_list, is_ident, line_with, methods, module, read, section,
    spans, words,
};

/// Names SPEC 8.2 lists that the M2 stub leaves to a later milestone (plan f.1:
/// nothing at M2 uses them).
const LATER: [(&str, &str); 1] = [("core/fmt", "hex")];

/// Words in signatures that are no names.
const KEYWORDS: [&str; 12] = [
    "fn", "function", "unsafe", "static", "let", "const", "move", "readonly", "where", "extends",
    "as", "new",
];

/// SPEC 6's compiler forms, each by its name and the receiver it is written
/// with: `console` in `console.log(...)`, `mem` in `mem.forget(x)`, a value in
/// `x.toString()`, none in `panic(m)`.
struct Forms {
    named: Vec<(Option<String>, String)>,
}

impl Forms {
    fn read() -> Forms {
        let spec = read("docs/SPEC.md");
        let six = section(&spec, "## 6. ");
        let table = &six[six.find("**Compiler forms.**").expect("the forms table")..];
        let mut named = Vec::new();
        for row in table.lines().filter(|l| l.starts_with("| ")).skip(1) {
            let first = row.split(" | ").next().unwrap_or("");
            for span in spans(first) {
                for call in calls(&span.text) {
                    named.push((call.receiver, call.name));
                }
                named.extend(words(&span.text).into_iter().map(|w| (None, w)));
            }
        }
        let forms = Forms { named };
        assert!(forms.covers("", None, "unreachable"), "{:?}", forms.named);
        forms
    }

    /// Whether `name`, listed for module `owner` with `receiver`, is a form: one
    /// written with no receiver or on any value (a one-letter receiver) covers every
    /// receiver, `mem.forget` the names of `core/mem`, and `console.log` only itself.
    fn covers(&self, owner: &str, receiver: Option<&str>, name: &str) -> bool {
        self.named.iter().any(|(r, n)| {
            n == name
                && match r {
                    None => true,
                    Some(r) if r.len() == 1 => true,
                    Some(r) => receiver == Some(r.as_str()) || owner == format!("core/{r}"),
                }
        })
    }

    /// The receivers that are objects of the compiler, named by no library module:
    /// `console`.
    fn objects(&self) -> BTreeSet<String> {
        self.named
            .iter()
            .filter_map(|(r, _)| r.clone())
            .filter(|r| r.len() > 1 && lookup(&format!("core/{r}")).is_none())
            .collect()
    }
}

/// SPEC 4.2's primitive types.
fn primitives() -> BTreeSet<String> {
    let spec = read("docs/SPEC.md");
    let table = section(&spec, "### 4.2 ");
    table
        .lines()
        .filter(|l| l.starts_with("| `"))
        .flat_map(|l| {
            let first = l.split(" | ").next().unwrap_or("");
            spans(first)
                .into_iter()
                .flat_map(|s| words(&s.text))
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Whether `name` could be a declared name: not a keyword, a type parameter or a
/// constant (which has no lowercase letter), and not a single letter.
fn plausible(name: &str) -> bool {
    name.len() >= 2 && name.chars().any(|c| c.is_ascii_lowercase()) && !KEYWORDS.contains(&name)
}

/// The spans of `text` that lie after "there is no" in their sentence, which name
/// what a type lacks.
fn negated(text: &str, all: &[Span]) -> BTreeSet<usize> {
    let mut out = BTreeSet::new();
    for (at, _) in text.match_indices("there is no ") {
        let end = text[at..].find(". ").map_or(text.len(), |i| i + at);
        out.extend(all.iter().filter(|s| s.at > at && s.at < end).map(|s| s.at));
    }
    out
}

/// The names one cell of SPEC 8.2's table lists: what its spans call, the words of
/// a span made only of words, a lowercase name in a list of spans, and each
/// `family*` with the operations the cell gives it.
fn listed(cell: &str) -> Vec<Called> {
    let all = spans(cell);
    let negated = negated(cell, &all);
    let mut out = Vec::new();
    let mut families = Vec::new();
    for span in all.iter().filter(|s| !negated.contains(&s.at)) {
        out.extend(calls(&span.text));
        let words = words(&span.text);
        let lowercase = words.len() == 1 && words[0].starts_with(|c: char| c.is_ascii_lowercase());
        if words.len() > 1 || span.text.starts_with('.') || (lowercase && in_list(span)) {
            out.extend(words.into_iter().map(|name| Called {
                receiver: None,
                name,
            }));
        }
        if let Some(prefix) = span.text.strip_suffix('*').filter(|p| is_ident(p)) {
            families.push(prefix.to_owned());
        }
    }
    if !families.is_empty() {
        let after = &cell[cell.rfind("*` for ").expect("the families' operations") + 7..];
        let ops: Vec<&str> = after
            .split(", ")
            .map_while(|w| (is_ident(w) && w.starts_with(char::is_uppercase)).then_some(w))
            .collect();
        assert!(ops.len() >= 2, "{after}");
        for family in &families {
            for op in &ops {
                out.push(Called {
                    receiver: None,
                    name: format!("{family}{op}"),
                });
            }
        }
    }
    out
}

/// The text a row of SPEC 8.2 points to, for its rows that say "section N.M":
/// the paragraph or rows of that section that list the API.
fn pointed(spec: &str, module: &str) -> Option<String> {
    let text = match module {
        "core/ptr" => line_with(section(spec, "### 7.1 "), "Safe operations:").to_owned(),
        "core/port" => line_with(section(spec, "### 7.3 "), "provides").to_owned(),
        "core/cpu" => line_with(section(spec, "### 10.3 "), "`cpu.vendor()").to_owned(),
        "core/atomic" => section(spec, "### 10.5 ")
            .lines()
            .filter(|l| l.starts_with("| `"))
            .map(|l| l.split(" | ").next().unwrap_or(""))
            .collect::<Vec<_>>()
            .join("\n"),
        _ => return None,
    };
    Some(text)
}

/// The module a name of a row belongs to: the row's, or the library module its
/// receiver names (`mem` in `mem.copy(...)`).
fn owner(row: &str, called: &Called) -> String {
    called
        .receiver
        .as_ref()
        .map(|r| format!("core/{r}"))
        .filter(|key| lookup(key).is_some())
        .unwrap_or_else(|| row.to_owned())
}

/// SPEC 8.2's rows, each with the module that declares its API, as
/// `(module, cell)`. `T[N]` is left out: it has the members of `Slice<T>`, whose
/// row lists them, and its `clone` is compiler glue.
fn rows() -> Vec<(String, String)> {
    let spec = read("docs/SPEC.md");
    let core = section(&spec, "### 8.2 ");
    let mut out = Vec::new();
    for row in core.lines().filter(|l| l.starts_with("| ")).skip(1) {
        let Some((first, cell)) = row[2..].split_once(" | ") else {
            continue;
        };
        let key = match first {
            "`T[N]`" | "---" => continue,
            "`Slice<T>`" => "core/slice".to_owned(),
            "integers" => "core/int".to_owned(),
            other => {
                let span = spans(other).into_iter().next().expect("a module");
                span.text
            }
        };
        assert!(
            lookup(&key).is_some(),
            "SPEC 8.2 names `{key}`, which lib/ lacks"
        );
        let mut text = cell.to_owned();
        if let Some(extra) = pointed(&spec, &key) {
            text.push('\n');
            text.push_str(&extra);
        }
        out.push((key, text));
    }
    out
}

/// Every name SPEC 8.2 lists, as `(row, module that declares it, name)`, without
/// compiler forms, primitive types, keywords and the names of [`LATER`].
fn required() -> Vec<(String, String, String)> {
    let forms = Forms::read();
    let primitives = primitives();
    let mut out = Vec::new();
    for (row, cell) in rows() {
        for called in listed(&cell) {
            let name = called.name.clone();
            let key = owner(&row, &called);
            let form = forms.covers(&key, called.receiver.as_deref(), &name);
            if !plausible(&name) || form || primitives.contains(&name) {
                continue;
            }
            if !LATER.contains(&(key.as_str(), name.as_str())) {
                out.push((row.clone(), key, name));
            }
        }
    }
    out
}

pub fn register(h: &mut Harness) {
    h.case(
        "api/each prelude's public names are SPEC 8.1's list for its layer",
        || {
            let spec = read("docs/SPEC.md");
            let prelude = section(&spec, "### 8.1 ");
            let markers = [
                ("`core`:", vec!["core/prelude"]),
                ("`alloc`:", vec!["alloc/prelude"]),
                (
                    "`os` (hosted only):",
                    vec![
                        "os/linux_x64/prelude",
                        "os/linux_i386/prelude",
                        "os/windows/prelude",
                        "os/vm/prelude",
                    ],
                ),
                (
                    "`os/none` (freestanding only):",
                    vec!["os/none/prelude", "os/uefi/prelude"],
                ),
            ];
            let starts: Vec<usize> = markers
                .iter()
                .map(|(m, _)| {
                    prelude
                        .find(m)
                        .unwrap_or_else(|| panic!("SPEC 8.1 has no {m}"))
                })
                .collect();
            let forms = Forms::read();
            let objects = forms.objects();
            assert!(objects.contains("console"), "{objects:?}");
            let primitives = primitives();
            for (i, (marker, preludes)) in markers.iter().enumerate() {
                let from = starts[i] + marker.len();
                let to = starts.get(i + 1).copied().unwrap_or(prelude.len());
                let mut names = BTreeSet::new();
                for span in spans(&prelude[from..to]) {
                    names.extend(words(&span.text));
                    names.extend(calls(&span.text).into_iter().map(|c| c.name));
                }
                names.retain(|n| {
                    !forms.covers("", None, n)
                        && !objects.contains(n)
                        && !primitives.contains(n)
                        && !["core", "alloc", "os"].contains(&n.as_str())
                });
                for key in preludes {
                    let public = declared(module(key), true);
                    assert_eq!(public, names, "{key} against SPEC 8.1's {marker}");
                }
            }
        },
    );
    h.case(
        "api/every name of SPEC 8.2's core table is declared in its module",
        || {
            let required = required();
            assert!(required.len() > 100, "{} names", required.len());
            for (row, key, name) in required {
                assert!(
                    declared(module(&key), false).contains(&name),
                    "SPEC 8.2 lists `{name}` for {row}, and {key} does not declare it"
                );
            }
        },
    );
    h.case("api/the table reader finds what the rows list", || {
        let required = required();
        let names = |key: &str| -> BTreeSet<String> {
            required
                .iter()
                .filter(|(_, owner, _)| owner == key)
                .map(|(_, _, name)| name.clone())
                .collect()
        };
        let slice = names("core/slice");
        for name in ["length", "some", "every", "fromRaw", "reduce", "sortBy"] {
            assert!(slice.contains(name), "{name} in {slice:?}");
        }
        for absent in ["push", "pop", "clear"] {
            assert!(
                !slice.contains(absent),
                "{absent}: SPEC says Slice has none"
            );
        }
        let int = names("core/int");
        for name in [
            "wrappingShr",
            "checkedNeg",
            "overflowingMul",
            "toBits",
            "swapBytes",
        ] {
            assert!(int.contains(name), "{name} in {int:?}");
        }
        let string = names("core/string");
        for name in ["startsWith", "compare", "codePointAt", "parseFloat"] {
            assert!(string.contains(name), "{name} in {string:?}");
        }
        assert!(names("core/atomic").contains("testAndClear"));
        assert!(names("core/port").contains("ioDelay"));
        assert!(names("core/cpu").contains("levelOf"));
        assert!(names("core/ptr").contains("writeVolatile"));
        assert!(
            names("core/mem").contains("copy"),
            "7.1's `mem.copy` is core/mem's"
        );
        let float = names("core/float");
        assert!(
            float.contains("atan2") && !float.contains("PI"),
            "{float:?}"
        );
        assert!(
            float.contains("log"),
            "`console.log` is a form, `log` on floats is not"
        );
        assert!(
            !names("core/mem").contains("forget"),
            "`mem.forget` is a form"
        );
        assert!(!names("core/fmt").contains("writeTo"), "a compiler form");
        assert!(
            !names("core/fmt").contains("hex"),
            "left to a later milestone"
        );
        assert!(!names("core/ptr").contains("usize"), "a primitive type");
    });
    h.case("api/the readers take spans, calls and declarations apart", || {
        let text = "`a.b(x)`, `c<T>()` and `@d(1)`\n```ts\n`e()`\n```\n`` `f` g `h` `` `.i`";
        let found: Vec<String> = spans(text).into_iter().map(|s| s.text).collect();
        assert_eq!(found, ["a.b(x)", "c<T>()", "@d(1)", "", "f", "h", "", ".i"]);
        let all = spans(text);
        assert_eq!(&text[all[1].at..all[1].at + 6], "c<T>()");
        assert!(in_list(&all[0]) && in_list(&all[1]) && !in_list(&all[4]));
        assert_eq!(
            calls("mem.copy(d, s) @requires(\"x\") Slice<T>.fromRaw(p, n) fn(x: u8)"),
            [
                Called { receiver: Some("mem".into()), name: "copy".into() },
                Called { receiver: None, name: "fromRaw".into() },
                Called { receiver: None, name: "fn".into() },
            ]
        );
        assert_eq!(words(".startsWith"), ["startsWith"]);
        assert_eq!(words("sqrt floor"), ["sqrt", "floor"]);
        assert!(words("p as *T").is_empty());
        let source = "public import { A, B as C } from \"./x\";\nimport { D } from \"./y\";\n\
                      @lang(\"e\") public final class E {\n  private f: u8;\n  @mustUse public let g<T>(): T;\n}\n\
                      private function h(): void { unreachable(); }\npublic enum I {\n  J { k: u8 },\n}\n";
        let all: Vec<String> = declared(source, false).into_iter().collect();
        assert_eq!(all, ["A", "C", "D", "E", "I", "J", "f", "g", "h"]);
        let public: Vec<String> = declared(source, true).into_iter().collect();
        assert_eq!(public, ["A", "C", "E", "I"]);
        assert_eq!(methods(source), [("g".to_owned(), true)]);
    });
    h.case(
        "api/SPEC 8.3's must-use methods are @mustUse wherever declared",
        || {
            let spec = read("docs/SPEC.md");
            let alloc = section(&spec, "### 8.3 ");
            let paragraph = line_with(alloc, "**Must-use methods.**");
            let mut exact = BTreeSet::new();
            let mut prefixes = BTreeSet::new();
            for span in spans(paragraph) {
                if let Some(prefix) = span.text.strip_suffix('*').filter(|p| is_ident(p)) {
                    prefixes.insert(prefix.to_owned());
                } else if is_ident(&span.text)
                    && span.text.starts_with(|c: char| c.is_ascii_lowercase())
                    && in_list(&span)
                {
                    exact.insert(span.text.clone());
                }
            }
            assert!(
                exact.contains("trim") && prefixes.contains("checked"),
                "{exact:?}"
            );
            let mut seen = BTreeSet::new();
            for (key, source) in all_modules() {
                for (name, must_use) in methods(source) {
                    let listed = exact.contains(&name)
                        || prefixes.iter().any(|p| name.starts_with(p.as_str()));
                    if listed {
                        seen.insert(name.clone());
                        assert!(must_use, "{key}: `{name}` is a must-use method (SPEC 8.3)");
                    }
                }
            }
            for name in &exact {
                assert!(seen.contains(name), "no method `{name}` in lib/");
            }
        },
    );
}
