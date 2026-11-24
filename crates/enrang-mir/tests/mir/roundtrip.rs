//! The text form's round trip (M3 plan b.6, f.4): every hand-written module under
//! `roundtrip/` is in printed form, so `print_module(parse_module(t)) == t`, and
//! parsing the print again gives equal bodies but for spans.

use enrang_testkit::Harness;

use crate::support::{fixtures, parse, print, unspanned};

pub fn register(h: &mut Harness) {
    for (name, text) in fixtures("roundtrip") {
        h.case(format!("roundtrip/{name}: print(parse(t)) is t"), move || {
            let (tcx, bodies) = parse(&text);
            let printed = print(&tcx, &bodies);
            if printed != text {
                let first = printed
                    .lines()
                    .zip(text.lines())
                    .position(|(a, b)| a != b)
                    .unwrap_or(printed.lines().count().min(text.lines().count()));
                panic!(
                    "the print differs at line {}:\n  printed: {:?}\n  written: {:?}\n{printed}",
                    first + 1,
                    printed.lines().nth(first),
                    text.lines().nth(first)
                );
            }
            let (tcx2, again) = parse(&printed);
            assert_eq!(again.len(), bodies.len());
            for (a, b) in bodies.iter().zip(&again) {
                assert_eq!(unspanned(a), unspanned(b));
            }
            assert_eq!(print(&tcx2, &again), text);
        });
    }
}

/// The error `parse_module` gives for `text`, as `line:col message`.
fn error_of(text: &str) -> String {
    match enrang_mir::parse_module(text) {
        Ok(_) => panic!("parsed:\n{text}"),
        Err(e) => format!("{}:{} {}", e.line, e.col, e.message),
    }
}

pub fn register_more(h: &mut Harness) {
    use enrang_hir::{Perm, ResultPerm, RetSources};
    use enrang_mir::{BlockId, Local, Point, ProjTable, canonicalize_projs, print_module};

    h.case("roundtrip/each operator's name means that operator", || {
        use enrang_mir::{BinOp, CheckedOp, Rvalue, StatementKind};
        let binary = [
            ("add", BinOp::Add),
            ("sub", BinOp::Sub),
            ("mul", BinOp::Mul),
            ("div", BinOp::Div),
            ("rem", BinOp::Rem),
            ("shl", BinOp::Shl),
            ("shr", BinOp::Shr),
            ("ushr", BinOp::Ushr),
            ("bit_and", BinOp::BitAnd),
            ("bit_or", BinOp::BitOr),
            ("bit_xor", BinOp::BitXor),
            ("eq", BinOp::Eq),
            ("ne", BinOp::Ne),
            ("lt", BinOp::Lt),
            ("le", BinOp::Le),
            ("gt", BinOp::Gt),
            ("ge", BinOp::Ge),
        ];
        let checked = [
            ("add", CheckedOp::Add),
            ("sub", CheckedOp::Sub),
            ("mul", CheckedOp::Mul),
            ("div", CheckedOp::Div),
            ("rem", CheckedOp::Rem),
            ("shl", CheckedOp::Shl),
            ("shr", CheckedOp::Shr),
            ("ushr", CheckedOp::Ushr),
        ];
        let mut text = "fn ops(_1: i64) -> void {\n  let _2: i64 temp;\n  bb0: {\n".to_owned();
        for (name, _) in binary {
            text += &format!("    _2 = {name}(copy _1, copy _1);\n");
        }
        for (name, _) in checked {
            text += &format!("    _2 = checked_{name}(copy _1, copy _1);\n");
        }
        text += "    return;\n  }\n}\n";
        let (_, bodies) = parse(&text);
        let mut got_binary = Vec::new();
        let mut got_checked = Vec::new();
        for st in &bodies[0].blocks[BlockId(0)].stmts {
            match &st.kind {
                StatementKind::Assign {
                    value: Rvalue::Binary(op, ..),
                    ..
                } => got_binary.push(*op),
                StatementKind::Assign {
                    value: Rvalue::Checked(op, ..),
                    ..
                } => got_checked.push(*op),
                other => panic!("{other:?}"),
            }
        }
        assert_eq!(got_binary, binary.map(|(_, op)| op));
        assert_eq!(got_checked, checked.map(|(_, op)| op));
    });
    h.case("roundtrip/a negative integer constant keeps only its type's bits", || {
        use enrang_hir::ConstValue;
        use enrang_mir::{ConstKind, Operand, Rvalue, StatementKind};
        let text = "fn neg() -> void {\n  let _1: i64 temp;\n  let _2: i8 temp;\n  bb0: {\n    _1 = const -5: i64;\n    _2 = const -5: i8;\n    return;\n  }\n}\n";
        let (_, bodies) = parse(text);
        let bits: Vec<u128> = bodies[0].blocks[BlockId(0)]
            .stmts
            .iter()
            .map(|st| match &st.kind {
                StatementKind::Assign { value: Rvalue::Use(Operand::Const(c)), .. } => match c.kind {
                    ConstKind::Value(ConstValue::Int(v, _)) => v,
                    ref k => panic!("{k:?}"),
                },
                other => panic!("{other:?}"),
            })
            .collect();
        assert_eq!(bits, [u128::from(u64::MAX - 4), 0xfb]);
    });
    h.case("roundtrip/parse errors name the line and column", || {
        let cases = [
            ("fn f() -> void {\n  bb0: {\n    _0 = copy _5;\n    return;\n  }\n}\n", "3:15 _5 is not declared"),
            ("fn f(_1: Nope) -> void;\n", "1:10 no type `Nope`"),
            ("fn f() -> void {\n  bb0: {\n    return;\n  }\n  bb0: {\n    return;\n  }\n}\n", "5:3 bb0 is defined twice"),
            ("fn f() -> void {\n  bb1: {\n    return;\n  }\n}\n", "5:1 bb0 is missing"),
            ("fn f() -> void {\n  bb0: {\n    nop;\n  }\n}\n", "4:3 expected a terminator, found `}`"),
            ("class P {\n  x: i64;\n}\nfn f(_1: P) -> i64 {\n  bb0: {\n    _0 = copy _1.z;\n    return;\n  }\n}\n", "6:18 no field `z` here"),
            ("fn f() -> void;\nfn f() -> void;\n", "2:4 `main::f` is declared twice"),
            ("@shiny fn f() -> void;\n", "1:1 no attribute `@shiny`"),
            ("fn f() -> void {\n  bb0: {\n    _0 = \"oops;\n", "3:10 an unterminated string"),
        ];
        for (text, want) in cases {
            assert_eq!(error_of(text), want, "{text}");
        }
    });
    h.case("roundtrip/a stated contract is completed and prints in full", || {
        let text = "fn get(let _1: &i64, _2: &i64) -> &i64 sources(0);\nfn use_get(_1: &i64) -> void {\n  let _2: &i64 temp;\n  bb0: {\n    _2 = get(copy _1, copy _1) -> bb1;\n  }\n  bb1: {\n    return;\n  }\n}\n";
        let (tcx, bodies) = parse(text);
        let get = tcx
            .defs()
            .find(|(_, d)| d.path.to_string() == "main::get")
            .map(|(d, _)| d)
            .expect("declared");
        let c = tcx.contract_memo(get).expect("a stated contract is in the memo");
        assert_eq!(c.perms, [Perm::Write, Perm::Read]);
        assert_eq!(c.sources, RetSources::Params(vec![0]));
        assert_eq!(c.result, ResultPerm::Writable);
        let printed = print(&tcx, &bodies);
        assert!(printed.starts_with("fn get(let _1: &i64, _2: &i64) -> &i64 perms(write, read) sources(0) result writable;\n"), "{printed}");
        let use_get = tcx
            .defs()
            .find(|(_, d)| d.path.to_string() == "main::use_get")
            .map(|(d, _)| d)
            .expect("declared");
        assert!(tcx.contract_memo(use_get).is_none(), "no contract stated, none stored");
    });
    h.case(
        "roundtrip/a class flag goes into the class-contract memo",
        || {
            let (tcx, _) =
                parse("class V writes_through_fields {\n  r: &i64;\n}\nclass W {\n  r: &i64;\n}\n");
            let flags: Vec<(String, Option<bool>)> = tcx
                .adts()
                .map(|(a, d)| {
                    (
                        d.name.to_string(),
                        tcx.class_contract_memo(a).map(|c| c.writes_through_fields),
                    )
                })
                .collect();
            assert_eq!(
                flags,
                [("V".to_owned(), Some(true)), ("W".to_owned(), None)]
            );
        },
    );
    h.case("roundtrip/spans point into the text", || {
        let text = std::fs::read_to_string(crate::support::dir("roundtrip").join("stack.mir"))
            .expect("a fixture");
        let (tcx, bodies) = parse(&text);
        let b = &bodies[0];
        let st = &b.blocks[BlockId(0)].stmts[0];
        assert_eq!(tcx.map().text(st.span), "_3 = &*_1 [reborrow]");
        let term = &b.blocks[BlockId(1)].term;
        assert_eq!(
            tcx.map().text(term.span),
            "switch move _4 [0: bb2, otherwise: bb3]"
        );
        assert_eq!(
            tcx.map().text(b.locals[Local(2)].span),
            "let _2: i64 | null;"
        );
        assert!(tcx.map().text(b.span).starts_with("fn pop2("));
        let _ = Point::new(BlockId(0), 0);
    });
    h.case(
        "roundtrip/projections interned in another order compare equal once canonical",
        || {
            let text = std::fs::read_to_string(crate::support::dir("roundtrip").join("places.mir"))
                .expect("a fixture");
            let (tcx, bodies) = parse(&text);
            let mut b = bodies[0].clone();
            // Re-intern every list in reverse, with an unused one first.
            let old = b.projs.clone();
            let mut table = ProjTable::new();
            table.intern(&[
                enrang_mir::Proj::Deref,
                enrang_mir::Proj::Deref,
                enrang_mir::Proj::Deref,
            ]);
            let mut lists: Vec<Vec<enrang_mir::Proj>> = (0..old.len())
                .map(|i| old.get(enrang_mir::ProjId(i as u32)).to_vec())
                .collect();
            lists.reverse();
            for l in &lists {
                table.intern(l);
            }
            enrang_mir::visit_places_mut(&mut b, &mut |_, p| {
                p.proj = table.intern(old.get(p.proj))
            });
            b.projs = table;
            assert_ne!(b, bodies[0]);
            assert_eq!(
                print_module(&tcx, [&b]),
                text,
                "the print does not depend on the ids"
            );
            canonicalize_projs(&mut b);
            assert_eq!(b, bodies[0]);
        },
    );
    h.case(
        "roundtrip/generics: `where`, implicit parameters and `extend` define what they print",
        || {
            use enrang_hir::{Implicit, OncePerType, TyKind};
            let text =
                std::fs::read_to_string(crate::support::dir("roundtrip").join("generics.mir"))
                    .expect("a fixture");
            let (tcx, _) = parse(&text);
            let def = |path: &str| {
                tcx.defs()
                    .find(|(_, d)| d.path.to_string() == path)
                    .map(|(d, _)| d)
                    .unwrap_or_else(|| panic!("{path}"))
            };
            let copied = tcx.sig(def("core/int::Holder::copied"));
            let [(t, bounds)] = &copied.where_bounds[..] else {
                panic!("{:?}", copied.where_bounds)
            };
            assert_eq!(tcx.param(*t).name.as_str(), "T");
            assert_eq!(bounds.len(), 2);
            let meet = def("core/int::Holder::meet");
            let own = &tcx.generics(tcx.sig(meet).generics).params;
            assert_eq!(tcx.param(own[0]).implicit, None);
            assert!(matches!(
                tcx.param(own[1]).implicit,
                Some(Implicit::Interface(_))
            ));
            assert_eq!(
                tcx.sig(meet).params[1].ty,
                tcx.mk_param(own[1]),
                "`_3: Greet` is the parameter"
            );
            assert_eq!(tcx.once_per_type(meet), Some(OncePerType::OwnParams));
            let both = def("core/int::Holder::both");
            let own = &tcx.generics(tcx.sig(both).generics).params;
            let tys: Vec<_> = tcx.sig(both).params.iter().map(|p| p.ty).collect();
            assert_eq!(
                tys[0],
                tcx.mk_param(own[0]),
                "each parameter its own, in order"
            );
            assert_eq!(tys[1], tcx.mk_ref(tcx.mk_param(own[1])));
            assert!(
                matches!(tcx.kind(tys[2]), TyKind::Nullable(_)) && !tcx.has_params(tys[2]),
                "a nested `&Greet | null` is the interface"
            );
            let odd = tcx.sig(def("core/int::Holder::odd"));
            let own = &tcx.generics(odd.generics).params;
            assert!(
                matches!(tcx.kind(odd.params[0].ty), TyKind::Object(_)),
                "no `Greet`"
            );
            assert_eq!(odd.params[1].ty, tcx.mk_param(own[0]));
            let pair = def("core/int::Holder::pair");
            assert_eq!(tcx.once_per_type(pair), Some(OncePerType::ObjectParam));
            let first = def("core/int::#extend0::first");
            let [e] = tcx.extends() else {
                panic!("one block")
            };
            assert_eq!(e.members, [first]);
            assert!(matches!(tcx.kind(e.ty), TyKind::Array(_)));
            assert_eq!(tcx.def(first).parent, Some(e.def));
            assert_eq!(tcx.sig(first).where_bounds.len(), 1);
        },
    );
    h.case(
        "roundtrip/declarations no body references are not printed",
        || {
            let (tcx, bodies) =
                parse("fn unused() -> void;\nfn f() -> void {\n  bb0: {\n    return;\n  }\n}\n");
            assert_eq!(
                print(&tcx, &bodies),
                "fn f() -> void {\n  bb0: {\n    return;\n  }\n}\n"
            );
        },
    );
}
