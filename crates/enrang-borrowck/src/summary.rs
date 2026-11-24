//! `--emit=summary` (M3 plan b.11; owner 2F): a module's header, then each of its
//! functions, methods and constructors with a contract, as its b.6 declaration
//! line, and each borrowing class with its flag, in `ItemPath` order, each
//! followed by its witnesses as `//   <param or flag>: <chain>` lines (A:1364).
//! A chain that ends in another module has that module's own witness appended,
//! when `set` holds it (A:1373; plan b.11): `--emit=summary` passes every
//! module's, an interface file only its own module's.
//! **Choice:** a function's line is the head `print_body` gives an empty body of
//! it; a class's is `class <path>` with ` writes_through_fields` when set.

use enrang_base::Span;
use enrang_hir::{ModuleId, Tcx};
use enrang_mir::{Body, BodyOwner, print_body};

use crate::ContractSet;
use crate::witness::text;

pub fn render(tcx: &Tcx, set: &ContractSet, module: ModuleId) -> String {
    let mut lines: Vec<(enrang_hir::ItemPath, String)> = Vec::new();
    for (d, data) in tcx.defs() {
        if data.module != module || tcx.contract_memo(d).is_none() {
            continue;
        }
        let text = print_body(
            tcx,
            &Body::new(BodyOwner::Fn(d), tcx.sig(d).ret, Span::DUMMY),
        );
        let head = text.lines().rev().nth(1).unwrap_or_default();
        let mut out = format!("{};\n", head.trim_end_matches(" {"));
        for w in set.witnesses.get(&data.path).into_iter().flatten() {
            let p = w.param.map_or("flag".into(), |i| format!("#{i}"));
            out.push_str(&format!(
                "//   {p}: {}{}\n",
                crate::witness::text(w),
                appended(set, w)
            ));
        }
        lines.push((data.path.clone(), out));
    }
    for (a, adt) in tcx.adts() {
        let data = tcx.def(adt.def);
        if data.module != module || !tcx.is_borrowing_class(a) {
            continue;
        }
        let on = crate::class_contract(tcx, a).writes_through_fields;
        let name: Vec<String> = data.path.segments.iter().map(|s| s.to_string()).collect();
        let wtf = if on { " writes_through_fields" } else { "" };
        let mut out = format!("class {}{wtf}\n", name.join("::"));
        if let Some(w) = set.class_witnesses.get(&data.path) {
            out.push_str(&format!("//   flag: {}\n", text(w)));
        }
        lines.push((data.path.clone(), out));
    }
    lines.sort();
    let mut out = format!("module \"{}\"\n", tcx.module(module).path);
    for (_, l) in lines {
        out.push_str(&l);
    }
    out
}

/// The witnesses of other modules a chain ends in, appended (A:1373): `` (`fill`
/// #0: passes it to `grow`, ...) `` after a step into `fill` of another module,
/// following each further module the appended chain ends in, each module once.
fn appended(set: &ContractSet, w: &crate::witness::Witness) -> String {
    let mut out = String::new();
    let mut seen = Vec::new();
    let mut cur = w.clone();
    while let Some(last) = cur.steps.last()
        && let (Some(callee), Some(q)) = (&last.callee, last.param)
        && !seen.contains(callee)
    {
        seen.push(callee.clone());
        let Some(next) =
            (set.witnesses.get(callee).into_iter().flatten()).find(|x| x.param == Some(q))
        else {
            break;
        };
        let name: Vec<String> = callee.segments.iter().map(|s| s.to_string()).collect();
        out.push_str(&format!(" (`{}` #{q}: {})", name.join("."), text(next)));
        cur = next.clone();
    }
    out
}
