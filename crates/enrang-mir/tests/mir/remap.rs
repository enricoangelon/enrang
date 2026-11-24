//! `remap_ids` (M3 plan b.10): each fixture under `remap/` is an old module, the
//! new declarations (`// --- new`) and the expected print of the remapped body
//! (`// --- expected`). The body printed against the new declarations without
//! remapping must differ from the expected text, so each fixture shows a change.

use enrang_base::intern;
use enrang_mir::{RemapError, print_module, redefine_adts, remap_ids};
use enrang_testkit::Harness;

use crate::support::{fixtures, parse};

fn sections(text: &str) -> (&str, &str, &str) {
    let (old, rest) = text
        .split_once("// --- new\n")
        .expect("a `// --- new` section");
    let (new, expected) = rest
        .split_once("// --- expected\n")
        .expect("a `// --- expected` section");
    (old, new, expected)
}

pub fn register(h: &mut Harness) {
    for (name, text) in fixtures("remap") {
        h.case(
            format!("remap/{name}: indices follow the names"),
            move || {
                let (old, new, expected) = sections(&text);
                let (mut tcx, mut bodies) = parse(old);
                redefine_adts(&mut tcx, new).unwrap_or_else(|e| panic!("{e}"));
                let stale = print_module(&tcx, &bodies);
                assert_ne!(
                    stale, expected,
                    "the change does not show without the remap"
                );
                for b in &mut bodies {
                    remap_ids(b, &tcx).unwrap_or_else(|e| panic!("{e}"));
                }
                assert_eq!(print_module(&tcx, &bodies), expected);
            },
        );
    }
    h.case("remap/a removed field is missing", || {
        let text = std::fs::read_to_string(crate::support::dir("remap").join("class_fields.mir"))
            .expect("a fixture");
        let (old, _, _) = sections(&text);
        let (mut tcx, mut bodies) = parse(old);
        redefine_adts(&mut tcx, "class P {\n  x: i64;\n}\n").expect("redefined");
        let e = remap_ids(&mut bodies[0], &tcx).expect_err("`y` is gone");
        let RemapError::Missing { path, name } = e;
        assert_eq!(path.to_string(), "main::P");
        assert_eq!(name, intern("y"));
    });
    h.case("remap/a removed case is missing", || {
        let text = std::fs::read_to_string(crate::support::dir("remap").join("enum_cases.mir"))
            .expect("a fixture");
        let (old, _, _) = sections(&text);
        let (mut tcx, mut bodies) = parse(old);
        redefine_adts(&mut tcx, "enum Shape { Circle { r: i64 } }\n").expect("redefined");
        let e = remap_ids(&mut bodies[0], &tcx).expect_err("`Square` is gone");
        let RemapError::Missing { name, .. } = e;
        assert_eq!(name, intern("Square"));
    });
    h.case("remap/an unchanged module remaps to itself", || {
        let text = std::fs::read_to_string(crate::support::dir("remap").join("enum_cases.mir"))
            .expect("a fixture");
        let (old, _, _) = sections(&text);
        let (tcx, mut bodies) = parse(old);
        let before = bodies.clone();
        remap_ids(&mut bodies[0], &tcx).expect("nothing to map");
        assert_eq!(bodies, before);
    });
}
