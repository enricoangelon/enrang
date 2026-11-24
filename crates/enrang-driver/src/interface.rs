//! Module interface files (ARCHITECTURE 6.8; M3 plan b.9): at M3 written, never
//! read (the read path, the check on load, EN0315, EN0316 and the recheck are
//! M4's).
//!
//! **Choices** (plan b.9, i.6): a file is written only when `check` runs inside a
//! project, one per user module that passed phase 3, at
//! `out/interfaces/<module path>.eni` under the project root (`init`'s
//! `.gitignore` already holds `/out/`); a write that fails is skipped, since the
//! file is a cache and M4 treats a missing one as stale. Every item of the module
//! counts as reachable (the walk from its public items is M4's, when a reader
//! exists), and test parts are never stored. Only user imports are listed: the
//! embedded library is part of the compiler's identity, which the `compiler` line
//! names. The text depends on nothing but the program: no path of the checkout,
//! no import order, no interning order (A:1376).
//!
//! The hash is the compiler's own (A:105): FNV-1a 64 over the UTF-8 text, printed
//! as 16 lowercase hex digits.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::path::{Component, Path, PathBuf};

use enrang_base::{SourceMap, Span};
use enrang_borrowck::ContractSet;
use enrang_hir::{ModuleId, ModulePath, Tcx};
use enrang_mir::{Body, BodyOwner, print_body, print_module};

/// The first line of every interface file: the format and its version.
pub const FORMAT: &str = "enrang-interface 1";

/// Where a project's interface files go, under its root.
pub const DIR: &str = "out/interfaces";

/// FNV-1a 64 of `text` (A:105; plan b.9).
pub fn stable_hash(text: &str) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in text.bytes() {
        h ^= u64::from(byte);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

fn hex(h: u64) -> String {
    format!("{h:016x}")
}

/// The file of `module` under the project root, or `None` for a module path that
/// would leave `out/interfaces/` (choice: such a module gets no file).
pub fn file_of(root: &Path, module: ModulePath) -> Option<PathBuf> {
    let rel = Path::new(module.as_str());
    let plain = rel.components().all(|c| matches!(c, Component::Normal(_)));
    (plain && !module.as_str().is_empty())
        .then(|| root.join(DIR).join(format!("{}.eni", module.as_str())))
}

/// One module's interface: the text and its API hash.
pub struct Interface {
    pub text: String,
    pub api: u64,
}

/// What every module's interface needs.
pub struct Inputs<'a> {
    pub tcx: &'a Tcx,
    pub map: &'a SourceMap,
    pub contracts: &'a ContractSet,
    pub bodies: &'a enrang_mir::Bodies,
}

/// The interface text of `module`, whose bodies in owner order are `owners` and
/// whose direct user imports are `imports` with their API hashes.
pub fn text(
    cx: &Inputs<'_>,
    module: ModuleId,
    owners: &[BodyOwner],
    imports: &[(ModulePath, u64)],
) -> Interface {
    let tcx = cx.tcx;
    let info = tcx.module(module);
    let stored: Vec<&Body> = owners
        .iter()
        .filter(|o| !in_test_part(tcx, **o))
        .map(|o| &cx.bodies[o])
        .collect();
    let (decls, texts) = split(tcx, &stored);

    let mut api = stored_summary(tcx, &ContractSet::default(), module);
    api.push_str(&layouts(tcx, module));
    api.push_str(&decls);
    let mut api_key = api.clone();
    for (_, h) in imports {
        api_key.push_str(&hex(*h));
        api_key.push('\n');
    }
    let api_hash = stable_hash(&api_key);

    let mut rest = String::from("\n[api]\n");
    rest.push_str(&api);
    rest.push_str("\n[bodies]\n");
    for t in &texts {
        rest.push_str(t);
        let _ = writeln!(rest, "bodyHash {}", hex(stable_hash(t)));
    }
    rest.push_str("\n[witnesses]\n");
    let own = ContractSet {
        witnesses: (cx.contracts.witnesses.iter())
            .filter(|(p, _)| p.module == info.path)
            .map(|(p, w)| (p.clone(), w.clone()))
            .collect(),
        class_witnesses: (cx.contracts.class_witnesses.iter())
            .filter(|(p, _)| p.module == info.path)
            .map(|(p, w)| (p.clone(), w.clone()))
            .collect(),
    };
    rest.push_str(&stored_summary(tcx, &own, module));

    let mut head = String::new();
    let _ = writeln!(head, "{FORMAT}");
    let _ = writeln!(head, "compiler enrang {}", env!("CARGO_PKG_VERSION"));
    let _ = writeln!(head, "target {}", tcx.target().name);
    let source = cx.map.file(info.file).text.as_ref();
    let _ = writeln!(head, "source {}", hex(stable_hash(source)));
    for (path, h) in imports {
        let _ = writeln!(head, "import \"{}\" {}", path.as_str(), hex(*h));
    }
    let _ = writeln!(head, "used {}", hex(stable_hash(&strip_contracts(&decls))));
    let _ = writeln!(head, "api {}", hex(api_hash));
    let _ = writeln!(head, "content {}", hex(stable_hash(&rest)));
    head.push_str(&rest);
    Interface {
        text: head,
        api: api_hash,
    }
}

/// `borrowck::summary::render` of `module` without the items of its `.test.en`
/// part, which are never stored (A:1376): each entry, a declaration line and the
/// witness lines under it, is dropped when its line is a test-part item's.
fn stored_summary(tcx: &Tcx, set: &ContractSet, module: ModuleId) -> String {
    let mut test_heads: BTreeSet<String> = BTreeSet::new();
    for (d, data) in tcx.defs() {
        if data.module == module && data.test_part && tcx.contract_memo(d).is_some() {
            let empty = Body::new(BodyOwner::Fn(d), tcx.sig(d).ret, Span::DUMMY);
            let text = print_body(tcx, &empty);
            let head = text.lines().rev().nth(1).unwrap_or_default();
            test_heads.insert(format!("{};", head.trim_end_matches(" {")));
        }
    }
    for (_, adt) in tcx.adts() {
        let data = tcx.def(adt.def);
        if data.module == module && data.test_part {
            let name: Vec<String> = data.path.segments.iter().map(|s| s.to_string()).collect();
            let class = format!("class {}", name.join("::"));
            test_heads.insert(format!("{class} writes_through_fields"));
            test_heads.insert(class);
        }
    }
    let mut out = String::new();
    let mut skipping = false;
    for line in enrang_borrowck::summary::render(tcx, set, module).lines() {
        if !line.starts_with("//") {
            skipping = test_heads.contains(line);
        }
        if !skipping {
            out.push_str(line);
            out.push('\n');
        }
    }
    out
}

/// Writes `text` as `module`'s file under `root`; a failure is skipped.
pub fn write(root: &Path, module: ModulePath, text: &str) {
    let Some(file) = file_of(root, module) else {
        return;
    };
    if let Some(dir) = file.parent()
        && fs::create_dir_all(dir).is_err()
    {
        return;
    }
    let _ = fs::write(file, text);
}

/// Whether a body belongs to a `.test.en` part, which is never stored.
fn in_test_part(tcx: &Tcx, owner: BodyOwner) -> bool {
    let of_hir = |o: enrang_hir::BodyOwner| match o {
        enrang_hir::BodyOwner::Test(_) => true,
        enrang_hir::BodyOwner::Fn(d) | enrang_hir::BodyOwner::Const(d) => tcx.def(d).test_part,
        enrang_hir::BodyOwner::Statements(_) => false,
    };
    match owner {
        BodyOwner::Test(_) => true,
        BodyOwner::Fn(d) => tcx.def(d).test_part,
        BodyOwner::Arrow(o, _) => of_hir(o),
        BodyOwner::Statements(_) | BodyOwner::Shim(_) => false,
    }
}

/// The declarations the bodies reference, as `print_module` prints them before
/// the bodies, and each body's own text, in owner order. A body's text is what
/// `print_module` adds for a second copy of it.
fn split(tcx: &Tcx, bodies: &[&Body]) -> (String, Vec<String>) {
    let texts: Vec<String> = bodies
        .iter()
        .map(|b| {
            let one = print_body(tcx, b);
            let two = print_module(tcx, [*b, *b]);
            two.strip_prefix(one.as_str())
                .map(|t| t.strip_prefix('\n').unwrap_or(t).to_owned())
                .unwrap_or(one)
        })
        .collect();
    let mut full = print_module(tcx, bodies.iter().copied());
    for t in texts.iter().rev() {
        match full.strip_suffix(t.as_str()) {
            Some(rest) => {
                let rest = rest.strip_suffix('\n').unwrap_or(rest);
                full = rest.to_owned();
            }
            None => return (full, texts),
        }
    }
    (full, texts)
}

/// `layout <type> size <n> align <n> offsets(<n>, ...)` for every class and enum
/// of the module whose layout enrang-layout computes, in path order; a borrowing
/// class's is `layout <type> deferred` (plan b.9).
fn layouts(tcx: &Tcx, module: ModuleId) -> String {
    let mut lines: BTreeMap<enrang_hir::ItemPath, String> = BTreeMap::new();
    for (a, adt) in tcx.adts() {
        let data = tcx.def(adt.def);
        if data.module != module || data.test_part {
            continue;
        }
        if adt.as_class().is_none() && adt.as_enum().is_none() {
            continue;
        }
        if !tcx.generics(adt.generics).params.is_empty() {
            continue;
        }
        let ty = tcx.adt_identity(a);
        let name = tcx.ty_string(ty);
        let line = if tcx.is_borrowing_class(a) {
            format!("layout {name} deferred\n")
        } else {
            match enrang_layout::layout_of(tcx, ty) {
                Ok(l) => {
                    let offsets: Vec<String> = l.fields.iter().map(|o| o.to_string()).collect();
                    format!(
                        "layout {name} size {} align {} offsets({})\n",
                        l.size,
                        l.align,
                        offsets.join(", ")
                    )
                }
                Err(_) => continue,
            }
        };
        lines.insert(data.path.clone(), line);
    }
    lines.into_values().collect()
}

/// `text` with every contract clause and class flag removed: the used-items hash
/// covers declarations, never contracts or flags (A:1377).
pub fn strip_contracts(text: &str) -> String {
    const CLAUSES: [&str; 6] = [
        "perms(",
        "sources(",
        "through_fields(",
        "through_read(",
        "stores(",
        "moves(",
    ];
    let mut out = String::with_capacity(text.len());
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < text.len() {
        let at_word = i == 0 || bytes[i - 1] == b' ';
        let rest = &text[i..];
        if at_word {
            if let Some(c) = CLAUSES.iter().find(|c| rest.starts_with(**c)) {
                i += c.len() - 1 + balanced(&rest[c.len() - 1..]);
                continue;
            }
            if let Some(r) = rest.strip_prefix("result ") {
                let word = r.find([' ', ';', '\n', '{']).unwrap_or(r.len());
                let skip = match r.strip_prefix("readonly") {
                    Some(paren) if paren.starts_with('(') => "readonly".len() + balanced(paren),
                    _ => word,
                };
                i += "result ".len() + skip;
                continue;
            }
            if rest.starts_with("writes_through_fields")
                && !rest["writes_through_fields".len()..]
                    .starts_with(|c: char| c.is_alphanumeric() || c == '_')
            {
                i += "writes_through_fields".len();
                continue;
            }
        }
        let c = rest.chars().next().expect("not at the end");
        out.push(c);
        i += c.len_utf8();
    }
    out
}

/// The length of the balanced parenthesised group `text` starts with.
fn balanced(text: &str) -> usize {
    let mut depth = 0usize;
    for (i, c) in text.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return i + 1;
                }
            }
            _ => {}
        }
    }
    text.len()
}
