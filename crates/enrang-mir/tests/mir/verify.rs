//! The verifier (M3 plan b.7, f.4): valid bodies pass, a narrowed `for...of` head
//! with its `CheckTag` runs included (T:1304) and a `new` in a loop among them, and
//! each rule, and each condition inside a rule, has a mutant of a valid body that
//! breaks only it, failing with exactly that rule.

use enrang_hir::Tcx;
use enrang_mir::{Body, BodyOwner, Local, LocalKind, MirPhase, Rule, ShimKind, verify};
use enrang_testkit::Harness;

use crate::support::{dir, parse};

fn fixture(name: &str) -> String {
    std::fs::read_to_string(dir("verify").join(format!("{name}.mir"))).expect("a fixture")
}

/// The rules every error of verifying `text`'s bodies names, in order.
fn rules_of(tcx: &Tcx, bodies: &[Body]) -> Vec<Rule> {
    let mut out = Vec::new();
    for b in bodies {
        if let Err(errors) = verify(tcx, b) {
            out.extend(errors.iter().map(|e| e.rule));
        }
    }
    out.dedup();
    out
}

/// A text mutant: `old` (which must occur once) replaced by `new`.
fn edit(text: &str, old: &str, new: &str) -> String {
    assert_eq!(text.matches(old).count(), 1, "`{old}` must occur once");
    text.replacen(old, new, 1)
}

type Mutate = fn(&mut Body);

fn arg_kind(b: &mut Body) {
    b.locals[Local(9)].kind = LocalKind::Arg;
}

fn elaborate(b: &mut Body) {
    b.phase = MirPhase::Elaborated;
}

fn mono(b: &mut Body) {
    b.phase = MirPhase::Mono;
}

fn temp_arg(b: &mut Body) {
    b.locals[Local(2)].kind = LocalKind::Temp;
}

fn undeclared(b: &mut Body) {
    b.meta.defaults_count = Some(Local(b.locals.len() as u32));
}

/// A mutant: the rule it breaks, what it tests, the fixture, text edits, a change to
/// the parsed body.
type Mutant = (
    Rule,
    &'static str,
    &'static str,
    &'static [(&'static str, &'static str)],
    Option<Mutate>,
);

const BEFORE_RETURN: &str = "    _0 = copy _9;";
const SPEAK: &str = "virtual Animal::speak [copy _6](copy _6)";
const SPEAK_DECL: &str = "fn Animal::speak(_1: &Animal) -> void;\n";
const REGION: &str = "  region r0: block;";

/// One mutant per rule (plan b.7), then one per condition inside a rule, each
/// breaking only that condition of a valid body.
fn mutants() -> Vec<Mutant> {
    vec![
        // A callee names one type argument per parameter of its generics (A:580),
        // else no argument or result type could be checked (gate: `id<bool, bool>`
        // verified clean).
        (
            Rule::Types,
            "a call with one type argument too many",
            "fix2",
            &[(
                "\"core/mem\"::swap<Animal>(move _4, move _5)",
                "\"core/mem\"::swap<Animal, bool>(move _4, move _5)",
            )],
            None,
        ),
        (
            Rule::Types,
            "an `fn` call through a nullable `fn` value",
            "fix2",
            &[
                (
                    "  let _3: (i64) => i64 temp;\n",
                    "  let _3: (i64) => i64 temp;\n  let _4: (fn(i64) => i64) | null temp;\n",
                ),
                (
                    "_0 = apply(move _3, const 4: i64) -> bb1;",
                    "_0 = fnptr(copy _4)(const 4: i64) -> bb1;",
                ),
            ],
            None,
        ),
        (
            Rule::Types,
            "a closure call through a reference",
            "fix2",
            &[(
                "  let _2: i64; // v\n  bb0: {\n    _0 = closure _1(copy _2) -> bb1;",
                "  let _2: i64; // v\n  let _3: &(i64) => i64 temp;\n  bb0: {\n    _3 = &_1 [explicit];\n    _0 = closure _3(copy _2) -> bb1;",
            )],
            None,
        ),
        (
            Rule::Types,
            "the closure of an `fn` value of another signature",
            "fix2",
            &[(
                "fn value(_1: fn(i64) => i64) -> i64 {\n  let _1: fn(i64) => i64; // g\n  let _2: [fn(i64) => i64] temp;",
                "fn value(_1: fn(i64) => bool) -> i64 {\n  let _1: fn(i64) => bool; // g\n  let _2: [fn(i64) => bool] temp;",
            )],
            None,
        ),
        (
            Rule::Types,
            "the closure of an env holding no `fn` value",
            "fix2",
            &[
                ("  let _2: [fn(i64) => i64] temp;", "  let _2: [i64] temp;"),
                ("    _2 = env(copy _1);", "    _2 = env(const 1: i64);"),
            ],
            None,
        ),
        (
            Rule::Types,
            "a shift by a reference",
            "fix2",
            &[
                ("fn sh(_1: u32, _2: u8)", "fn sh(_1: u32, _2: &u8)"),
                ("  let _2: u8; // r", "  let _2: &u8; // r"),
            ],
            None,
        ),
        (
            Rule::Types,
            "a fixed error text by value",
            "fix2",
            &[(
                "form failure_text(const \"e\": &string)",
                "form failure_text(const \"e\": string)",
            )],
            None,
        ),
        (
            Rule::Types,
            "a form's part counts that do not cover its operands (A:976)",
            "fix2",
            &[(
                "form failure_text(const \"e\": &string)",
                "form failure_text[2](const \"e\": &string)",
            )],
            None,
        ),
        (
            Rule::Types,
            "a form argument by value",
            "fix2",
            &[(
                "    _0 = Result<i64>::Ok { value: const 1: i64 };",
                "    _4 = form log(const 1: i64) -> bb2;\n  }\n  bb5: {\n    _0 = Result<i64>::Ok { value: const 1: i64 };",
            )],
            None,
        ),
        (
            Rule::Types,
            "a discriminant into no integer",
            "fix2",
            &[(
                "    _0 = Result<i64>::Ok { value: const 1: i64 };\n    return;",
                "    _0 = Result<i64>::Ok { value: const 1: i64 };\n    _2 = discriminant(_0);\n    return;",
            )],
            None,
        ),
        (
            Rule::Virtual,
            "a bound member of a class that is final",
            "fix2",
            &[("class Animal {", "@final class Animal {")],
            None,
        ),
        (
            Rule::GuardClass,
            "a `mem.swap` object with no check",
            "fix2",
            &[("    check_class(*_2, swap, ref);\n", "")],
            None,
        ),
        (
            Rule::GuardClass,
            "a `mem.swap` object checked after its borrow",
            "fix2",
            &[(
                "    check_class(*_2, swap, ref);\n    _5 = &*_2 [reborrow];\n",
                "    _5 = &*_2 [reborrow];\n    check_class(*_2, swap, ref);\n",
            )],
            None,
        ),
        (
            Rule::LocalOnce,
            "a user local",
            "valid",
            &[],
            Some(arg_kind),
        ),
        (
            Rule::LocalOnce,
            "an environment outside an arrow",
            "valid",
            &[(
                "  let _8: isize temp;",
                "  let _1: &i64[] env;\n  let _8: isize temp;",
            )],
            None,
        ),
        (
            Rule::LocalOnce,
            "a temporary among the arguments",
            "valid",
            &[],
            Some(temp_arg),
        ),
        (
            Rule::LocalOnce,
            "the first local past the last",
            "valid",
            &[],
            Some(undeclared),
        ),
        (
            Rule::Types,
            "a binary of two types",
            "valid",
            &[(
                "_15 = div(copy _15, const 2.0: f64);",
                "_9 = add(copy _9, copy _2);",
            )],
            None,
        ),
        (
            Rule::Types,
            "a length into no `isize`",
            "valid",
            &[(BEFORE_RETURN, "    _9 = len(*_1);\n    _0 = copy _9;")],
            None,
        ),
        (
            Rule::Types,
            "a cast of another kind",
            "valid",
            &[(
                BEFORE_RETURN,
                "    _9 = cast(int_to_int, copy _15, i64);\n    _0 = copy _9;",
            )],
            None,
        ),
        (
            Rule::Types,
            "an assignment",
            "valid",
            &[("    _9 = copy (*_1)[_2];", "    _12 = copy (*_1)[_2];")],
            None,
        ),
        (
            Rule::Types,
            "a call's destination",
            "valid",
            &[("_11 = virtual", "_9 = virtual")],
            None,
        ),
        (
            Rule::Types,
            "`div` of integers",
            "valid",
            &[(
                "_15 = div(copy _15, const 2.0: f64);",
                "_9 = div(copy _9, copy _9);",
            )],
            None,
        ),
        (
            Rule::Types,
            "`checked_div` of floats",
            "valid",
            &[(
                "_15 = div(copy _15, const 2.0: f64);",
                "_15 = checked_div(copy _15, const 2.0: f64);",
            )],
            None,
        ),
        (
            Rule::HostCallPlace,
            "outside `os/vm`",
            "valid",
            &[(
                BEFORE_RETURN,
                "    host_call \"vm.x\"();\n    _0 = copy _9;",
            )],
            None,
        ),
        (
            Rule::SetTable,
            "a class with no table",
            "valid",
            &[(
                BEFORE_RETURN,
                "    set_table(*_7, Leaf);\n    _0 = copy _9;",
            )],
            None,
        ),
        (
            Rule::SetTable,
            "an argument's existing object",
            "valid",
            &[(
                BEFORE_RETURN,
                "    set_table(*_6, Animal);\n    _0 = copy _9;",
            )],
            None,
        ),
        (
            Rule::SetTable,
            "a local written before",
            "valid",
            &[(
                "    _14 = copy *_6;\n",
                "    _14 = copy *_6;\n    set_table(_14, Animal);\n",
            )],
            None,
        ),
        (
            Rule::SetTable,
            "an object reached through a box",
            "valid",
            &[(
                "    _8 = len(*_1);\n",
                "    set_table(*_17, Dog);\n    _8 = len(*_1);\n",
            )],
            None,
        ),
        (
            Rule::SetTable,
            "another class's table",
            "valid",
            &[(
                "    _8 = len(*_1);\n",
                "    set_table(_14, Dog);\n    _8 = len(*_1);\n",
            )],
            None,
        ),
        (
            Rule::SetTable,
            "an object built on an earlier turn",
            "newobj",
            &[
                ("    storage_live(_2);\n", ""),
                ("    storage_dead(_2);\n", ""),
            ],
            None,
        ),
        (
            Rule::SetTable,
            "a temporary built on an earlier turn and never moved",
            "newobj",
            &[("take(move _2)", "take(copy _2)")],
            None,
        ),
        (
            Rule::SetTable,
            "a temporary built again after a copy",
            "newobj",
            &[("_5 = move _2;", "_5 = copy _2;")],
            None,
        ),
        (
            Rule::SetTable,
            "a temporary built again after it is copied into a literal",
            "newobj",
            &[("tuple(move _2,", "tuple(copy _2,")],
            None,
        ),
        (
            Rule::SetTable,
            "a temporary built on an earlier turn and never ended",
            "newobj",
            &[("    storage_dead(_3);\n", "")],
            None,
        ),
        (
            Rule::Regions,
            "its own parent",
            "valid",
            &[(REGION, "  region r0: block in r0;")],
            None,
        ),
        (
            Rule::Regions,
            "a parent",
            "valid",
            &[("  region r0: block;", "  region r0: block in r3;")],
            None,
        ),
        (
            Rule::NoDropAfterElab,
            "`drop`",
            "valid",
            &[(BEFORE_RETURN, "    drop(_14);\n    _0 = copy _9;")],
            Some(elaborate),
        ),
        (
            Rule::NoDropAfterElab,
            "`drop_glue` before elaboration",
            "valid",
            &[(BEFORE_RETURN, "    drop_glue(_14);\n    _0 = copy _9;")],
            None,
        ),
        (Rule::NoParams, "a parameter", "generic", &[], Some(mono)),
        (
            Rule::CheckRuns,
            "a statement after a run",
            "valid",
            &[(
                "    check_tag(_3, Present);\n",
                "    check_tag(_3, Present);\n    nop;\n",
            )],
            Some(elaborate),
        ),
        (
            Rule::CheckRuns,
            "a bounds check before a call",
            "valid",
            &[(
                "    _14 = copy *_6;\n",
                "    _14 = copy *_6;\n    check_bounds(copy _2, copy _8);\n",
            )],
            None,
        ),
        (
            Rule::CheckRuns,
            "a bounds check on another index",
            "valid",
            &[(
                "check_bounds(copy _2, copy _8);",
                "check_bounds(copy _8, copy _8);",
            )],
            Some(elaborate),
        ),
        (
            Rule::CheckRuns,
            "a write before a `for...of` bind's bounds check",
            "forof",
            &[
                (
                    "    storage_live(_5);\n",
                    "    storage_live(_5);\n    _2 = const 5: isize;\n",
                ),
                ("bind bb2[3]", "bind bb2[4]"),
            ],
            None,
        ),
        (
            Rule::CheckRuns,
            "a write after a `for...of` head's compare",
            "forof",
            &[(
                "    _4 = lt(copy _2, copy _3);\n",
                "    _4 = lt(copy _2, copy _3);\n    _3 = const 99: isize;\n",
            )],
            None,
        ),
        (
            Rule::CheckRuns,
            "a second compare in a `for...of` head",
            "forof",
            &[(
                "    _4 = lt(copy _2, copy _3);\n",
                "    _4 = lt(copy _2, copy _3);\n    _4 = gt(copy _2, copy _3);\n",
            )],
            None,
        ),
        (
            Rule::CheckRuns,
            "a block between a `for...of` head and its bind",
            "forof",
            &[
                ("otherwise: bb2];", "otherwise: bb5];"),
                (
                    "  bb4: {\n    return;\n  }\n",
                    "  bb4: {\n    return;\n  }\n  bb5: {\n    goto bb2;\n  }\n",
                ),
            ],
            None,
        ),
        (
            Rule::MoveRef,
            "a conversion's operand",
            "valid",
            &[("convert(upcast, copy _4)", "convert(upcast, move _4)")],
            None,
        ),
        (
            Rule::MoveRef,
            "a reference in a temporary's part",
            "valid",
            &[
                (REGION, "  let _18: [&Animal] temp;\n  region r0: block;"),
                (BEFORE_RETURN, "    _10 = move _18.0;\n    _0 = copy _9;"),
            ],
            None,
        ),
        (
            Rule::MoveRef,
            "a call's argument",
            "valid",
            &[("[copy _6](copy _6) -> bb1;", "[copy _6](move _6) -> bb1;")],
            None,
        ),
        // Phase 3 reads an operand's loans from its local: a reference or a
        // borrowing value out of a part goes through a `Use` into a temporary
        // first (A:935), or an aggregate, a conversion or a call would hold none.
        (
            Rule::MoveRef,
            "a reference part as a conversion's operand",
            "valid",
            &[
                (REGION, "  let _18: [&Dog] temp;\n  region r0: block;"),
                ("convert(upcast, copy _4)", "convert(upcast, copy _18.0)"),
            ],
            None,
        ),
        (
            Rule::MoveRef,
            "a reference part as an aggregate's operand",
            "valid",
            &[
                (
                    REGION,
                    "  let _18: [&Animal, i64] temp;\n  let _19: [&Animal] temp;\n  region r0: block;",
                ),
                (
                    BEFORE_RETURN,
                    "    _19 = tuple(copy _18.0);\n    _0 = copy _9;",
                ),
            ],
            None,
        ),
        (
            Rule::MoveRef,
            "a reference part as a call's argument",
            "valid",
            &[
                (REGION, "  let _18: [&Animal] temp;\n  region r0: block;"),
                (
                    "[copy _6](copy _6) -> bb1;",
                    "[copy _18.0](copy _18.0) -> bb1;",
                ),
            ],
            None,
        ),
        (
            Rule::ConvertPairs,
            "a fixed array's view",
            "valid",
            &[(
                "convert(array_to_slice, copy _1)",
                "convert(fixed_to_slice, copy _1)",
            )],
            None,
        ),
        (
            Rule::ConvertPairs,
            "a class missing an interface member",
            "classes",
            &[(
                "fn Greet::greet(_1: &Self) -> void;\n",
                "fn Greet::greet(_1: &Self) -> void;\nfn Greet::wave(_1: &Self) -> void;\n",
            )],
            None,
        ),
        (
            Rule::ConvertPairs,
            "a `Box` upcast to a reference",
            "valid",
            &[("convert(upcast, copy _4)", "convert(upcast, copy _17)")],
            None,
        ),
        (
            Rule::FieldInit,
            "outside a constructor",
            "valid",
            &[(
                BEFORE_RETURN,
                "    field_init((*_6).name, const 1: i64);\n    _0 = copy _9;",
            )],
            None,
        ),
        (
            Rule::FieldInit,
            "an edge that is an arm as well as `otherwise`",
            "ctor",
            &[(
                "[0: bb1, otherwise: bb2]",
                "[0: bb1, 1: bb2, otherwise: bb2]",
            )],
            None,
        ),
        (
            Rule::GuardBounds,
            "no bounds check",
            "valid",
            &[("    check_bounds(copy _2, copy _8);\n", "")],
            None,
        ),
        (
            Rule::GuardBounds,
            "a length of another part of the local",
            "valid",
            &[
                (
                    REGION,
                    "  let _18: [i64[], i64[]] temp;\n  let _19: isize temp;\n  region r0: block;",
                ),
                (
                    BEFORE_RETURN,
                    "    _19 = len(_18.1);\n    check_bounds(copy _2, copy _19);\n    _9 = copy _18.0[_2];\n    _0 = copy _9;",
                ),
            ],
            None,
        ),
        (
            Rule::GuardBounds,
            "a length of another place",
            "valid",
            &[("_8 = len(*_1);", "_8 = len(*_13);")],
            None,
        ),
        (
            Rule::GuardBounds,
            "a constant index equal to a fixed array's length",
            "never",
            &[("_2[2]", "_2[3]")],
            None,
        ),
        (
            Rule::GuardTag,
            "no tag check",
            "valid",
            &[("    check_tag(_3, Present);\n", "")],
            None,
        ),
        (
            Rule::GuardTag,
            "a tag check of another base",
            "valid",
            &[(
                "    check_tag((_16 as Present).0.0, Present);\n",
                "    check_tag(_16, Present);\n",
            )],
            None,
        ),
        (
            Rule::GuardClass,
            "no class check",
            "valid",
            &[("    check_class(*_6, copy_out, ref);\n", "")],
            None,
        ),
        (
            Rule::GuardClass,
            "a copy out through a box",
            "classes",
            &[("    check_class(*_2, copy_out, box);\n", "")],
            None,
        ),
        (
            Rule::GuardClass,
            "a copy out as a call's argument",
            "classes",
            &[(
                "    check_class(*_1, copy_out, ref);\n    _8 = take",
                "    _8 = take",
            )],
            None,
        ),
        (
            Rule::GuardClass,
            "a whole object written through a reference",
            "classes",
            &[("    check_class(*_1, assign, ref);\n", "")],
            None,
        ),
        (
            Rule::GuardClass,
            "a write's class check after the old value's drop",
            "classes",
            &[(
                "    check_class(*_1, assign, ref);\n    drop(*_1) [assign];\n",
                "    drop(*_1) [assign];\n    check_class(*_1, assign, ref);\n",
            )],
            None,
        ),
        (
            Rule::GuardClass,
            "the object of `clone`",
            "classes",
            &[("    check_class(*_1, clone, ref);\n", "")],
            None,
        ),
        (
            Rule::GuardClass,
            "the object of `clone` on a narrowed payload, named through the receiver",
            "classes",
            &[("    check_class(*_3, clone, ref);\n", "")],
            None,
        ),
        (
            Rule::GuardClass,
            "a move out of a box",
            "classes",
            &[(
                "    check_class(*_2, unbox, box);\n    _5 = move *_2;",
                "    _5 = move *_2;",
            )],
            None,
        ),
        (
            Rule::GuardClass,
            "the object of a box's `clone`",
            "classes",
            &[("    check_class(*_2, clone, box);\n", "")],
            None,
        ),
        (
            Rule::GuardClass,
            "the object of `unbox`",
            "classes",
            &[(
                "    check_class(*_2, unbox, box);\n    _5 = Box",
                "    _5 = Box",
            )],
            None,
        ),
        (
            Rule::GuardClass,
            "a `move` method's entry",
            "classes",
            &[("    check_class(*_1, move_this(into), ref);\n", "")],
            None,
        ),
        (
            Rule::GuardClass,
            "a `move_this` naming another method",
            "classes",
            &[("move_this(into)", "move_this(other)")],
            None,
        ),
        (
            Rule::GuardClass,
            "a class check of another event",
            "valid",
            &[(
                "check_class(*_6, copy_out, ref);",
                "check_class(*_6, assign, ref);",
            )],
            None,
        ),
        (
            Rule::UnsafeIntrinsic,
            "a region",
            "valid",
            &[(" @ r0;", ";")],
            None,
        ),
        (
            Rule::Virtual,
            "a `final` class",
            "valid",
            &[(SPEAK, "virtual Leaf::get [copy _7](copy _7)")],
            None,
        ),
        (
            Rule::Virtual,
            "a `private` method",
            "valid",
            &[
                (
                    SPEAK_DECL,
                    "fn Animal::speak(_1: &Animal) -> void;\n@private fn Animal::hide(_1: &Animal) -> void;\n",
                ),
                (SPEAK, "virtual Animal::hide [copy _6](copy _6)"),
            ],
            None,
        ),
        (
            Rule::Virtual,
            "a `static` method",
            "valid",
            &[
                (
                    SPEAK_DECL,
                    "fn Animal::speak(_1: &Animal) -> void;\nstatic fn Animal::make() -> void;\n",
                ),
                (SPEAK, "virtual Animal::make [copy _6](copy _6)"),
            ],
            None,
        ),
        (
            Rule::Virtual,
            "a method with type parameters of its own",
            "valid",
            &[
                (
                    SPEAK_DECL,
                    "fn Animal::speak(_1: &Animal) -> void;\nfn Animal::show<U>(_1: &Animal) -> void;\n",
                ),
                (SPEAK, "virtual Animal::show<i64> [copy _6](copy _6)"),
            ],
            None,
        ),
        (
            Rule::Virtual,
            "a method taking an interface by value",
            "valid",
            &[
                (
                    SPEAK_DECL,
                    "fn Animal::speak(_1: &Animal) -> void;\nfn Animal::meet<implicit Greet>(_1: &Animal, _2: Greet) -> void;\ninterface Greet { }\n",
                ),
                (
                    SPEAK,
                    "virtual Animal::meet<i64> [copy _6](copy _6, copy _9)",
                ),
            ],
            None,
        ),
        (
            Rule::Virtual,
            "a method taking an object type",
            "valid",
            &[
                (
                    SPEAK_DECL,
                    "fn Animal::speak(_1: &Animal) -> void;\nfn Animal::at<implicit { x: i64 }>(_1: &Animal, _2: { x: i64 }) -> void;\n",
                ),
                (SPEAK, "virtual Animal::at<i64> [copy _6](copy _6, copy _9)"),
            ],
            None,
        ),
        (
            Rule::Virtual,
            "a table read from another object",
            "valid",
            &[(SPEAK, "virtual Animal::speak [copy _10](copy _6)")],
            None,
        ),
        (
            Rule::Cfg,
            "a block",
            "valid",
            &[("[copy _6](copy _6) -> bb1;", "[copy _6](copy _6) -> bb7;")],
            None,
        ),
        (
            Rule::Cfg,
            "a switch value twice",
            "forof",
            &[("[0: bb4, otherwise: bb2]", "[0: bb4, 0: bb2]")],
            None,
        ),
        (
            Rule::Meta,
            "a loop's bind that is no `for-of-element` borrow",
            "forof",
            &[("[for-of-element]", "[explicit]")],
            None,
        ),
        (
            Rule::Meta,
            "a fact's test in no block",
            "valid",
            &[(
                REGION,
                "  region r0: block;\n  fact f0: _3 nonnull;\n  test f0 at bb9;",
            )],
            None,
        ),
        (
            Rule::Meta,
            "the test of no fact",
            "valid",
            &[(
                REGION,
                "  region r0: block;\n  fact f0: _3 nonnull;\n  test f1 at bb0;",
            )],
            None,
        ),
        (
            Rule::Meta,
            "a narrowed use at no point",
            "valid",
            &[(
                REGION,
                "  region r0: block;\n  fact f0: _3 nonnull;\n  use f0 at bb9[0];",
            )],
            None,
        ),
        (
            Rule::Meta,
            "a loop's pre-header that is no block",
            "forof",
            &[("preheader bb0", "preheader bb9")],
            None,
        ),
        (
            Rule::Meta,
            "a loop's head that is no block",
            "forof",
            &[("head bb1", "head bb9")],
            None,
        ),
        (
            Rule::Meta,
            "a record of no fact",
            "valid",
            &[(
                REGION,
                "  region r0: block;\n  record f0 at bb0[0] _9 copy;",
            )],
            None,
        ),
        (
            Rule::Meta,
            "an assigned value",
            "valid",
            &[(
                "  region r0: block;",
                "  region r0: block;\n  assign_value bb0[0];",
            )],
            None,
        ),
    ]
}

pub fn register(h: &mut Harness) {
    for name in [
        "valid", "forof", "ctor", "generic", "newobj", "never", "classes", "fix2",
    ] {
        h.case(format!("verify/{name}: a valid body passes"), move || {
            let (tcx, bodies) = parse(&fixture(name));
            for b in &bodies {
                if let Err(e) = verify(&tcx, b) {
                    panic!("{e:#?}");
                }
            }
        });
    }
    for (rule, what, name, edits, f) in mutants() {
        h.case(
            format!("verify/mutant {rule:?}, {what}: fails with exactly that rule"),
            move || {
                // In `Built` MIR a check out of place also leaves its use unguarded
                // (V12-V14), so those `CheckRuns` mutants are elaborated bodies.
                let mut source = fixture(name);
                for (old, new) in edits {
                    source = edit(&source, old, new);
                }
                let (tcx, mut bodies) = parse(&source);
                if let Some(f) = f {
                    f(&mut bodies[0]);
                }
                assert_eq!(rules_of(&tcx, &bodies), [rule], "{source}");
            },
        );
    }
    h.case(
        "verify/a region outside its parent's span breaks V05",
        || {
            use enrang_base::{BytePos, Span};
            let source = edit(
                &fixture("valid"),
                "  region r0: block;\n",
                "  region r0: block;\n  region r1: block in r0;\n",
            );
            let (tcx, mut bodies) = parse(&source);
            assert_eq!(
                rules_of(&tcx, &bodies),
                [],
                "a parsed region has no span to compare"
            );
            let span = |lo, hi| Span {
                lo: BytePos(lo),
                hi: BytePos(hi),
            };
            let regions = &mut bodies[0].unsafe_regions;
            regions[enrang_mir::RegionId(0)].span = span(10, 20);
            regions[enrang_mir::RegionId(1)].span = span(12, 18);
            assert_eq!(rules_of(&tcx, &bodies), []);
            bodies[0].unsafe_regions[enrang_mir::RegionId(1)].span = span(5, 15);
            assert_eq!(rules_of(&tcx, &bodies), [Rule::Regions]);
        },
    );
    h.case(
        "verify/newobj: elaborated, and with drop glue ending a temporary, it passes",
        || {
            let glue = edit(&fixture("newobj"), "storage_dead(_3);", "drop_glue(_3);");
            for source in [fixture("newobj"), glue] {
                let (tcx, mut bodies) = parse(&source);
                bodies.iter_mut().for_each(elaborate);
                assert_eq!(rules_of(&tcx, &bodies), [], "{source}");
            }
        },
    );
    h.case(
        "verify/`set_table` on an existing object passes in a drop glue shim",
        || {
            let source = edit(
                &fixture("valid"),
                BEFORE_RETURN,
                "    set_table(*_6, Animal);\n    _0 = copy _9;",
            );
            let (tcx, mut bodies) = parse(&source);
            let ty = bodies[0].locals[Local(14)].ty;
            bodies[0].owner = BodyOwner::Shim(ShimKind::DropGlue(ty));
            assert_eq!(rules_of(&tcx, &bodies), []);
        },
    );
    h.case(
        "verify/ctor: a missing override initialiser before `super`",
        || {
            let source = edit(
                &fixture("ctor"),
                "    field_init((*_1).a, const 5: i64);\n",
                "",
            );
            let (tcx, bodies) = parse(&source);
            assert_eq!(rules_of(&tcx, &bodies), [Rule::FieldInit]);
        },
    );
    h.case("verify/ctor: an initialiser outside its switch", || {
        let source = edit(
            &fixture("ctor"),
            "    (*_1).b = copy _2;\n",
            "    (*_1).b = copy _2;\n    field_init((*_1).a, const 6: i64);\n",
        );
        let (tcx, bodies) = parse(&source);
        assert_eq!(rules_of(&tcx, &bodies), [Rule::FieldInit]);
    });
    h.case(
        "verify/ctor: `this` is a constructor's first argument (A:1333 stores (1, 0))",
        || {
            // The base constructor called with the written argument where `this`
            // goes: V02 zips arguments against `this` first, then the parameters.
            let source = edit(
                &fixture("ctor"),
                "    _3 = Base::#ctor(move _4) -> bb3;\n",
                "    _3 = Base::#ctor(copy _2) -> bb3;\n",
            );
            let (tcx, bodies) = parse(&source);
            assert_eq!(rules_of(&tcx, &bodies), [Rule::Types]);
            // And the constructor's own `this` is `_1: &Mid`, an argument.
            let (_, bodies) = parse(&fixture("ctor"));
            let mid = bodies
                .iter()
                .find(|b| b.arg_count == 2)
                .expect("Mid::#ctor");
            assert_eq!(mid.locals[Local(1)].kind, LocalKind::Arg);
        },
    );
    h.case(
        "verify/forof: the head's tag run moved off its `Len` fails",
        || {
            let source = edit(
                &fixture("forof"),
                "    check_tag(*_1, Present);\n    _3 = len",
                "    _3 = len",
            );
            let (tcx, bodies) = parse(&source);
            assert_eq!(rules_of(&tcx, &bodies), [Rule::GuardTag]);
        },
    );
    h.case(
        "verify/a host call in a module under `os/vm` passes",
        || {
            let call = "    host_call \"vm.x\"();\n    _0 = copy _9;";
            for (module, want) in [
                ("os/vm", vec![]),
                ("os/vm/io", vec![]),
                ("os/vmx", vec![Rule::HostCallPlace]),
            ] {
                let source = format!(
                    "module \"{module}\";\n{}",
                    edit(&fixture("valid"), BEFORE_RETURN, call)
                );
                let (tcx, bodies) = parse(&source);
                assert_eq!(rules_of(&tcx, &bodies), want, "{module}");
            }
        },
    );
    h.case("verify/V16: a method taking an interface by reference has a slot", || {
        let source = edit(
            &fixture("valid"),
            SPEAK_DECL,
            "fn Animal::speak(_1: &Animal) -> void;\nfn Animal::meet<implicit Greet>(_1: &Animal, _2: &Greet) -> void;\ninterface Greet { }\n",
        );
        let source = edit(&source, SPEAK, "virtual Animal::meet<Animal> [copy _6](copy _6, copy _6)");
        let (tcx, bodies) = parse(&source);
        assert_eq!(rules_of(&tcx, &bodies), []);
    });
    h.case(
        "verify/V13: a tag check of another local guards nothing",
        || {
            let source = edit(
                &fixture("valid"),
                "    check_tag(_3, Present);\n",
                "    check_tag(_16, Present);\n",
            );
            let (tcx, bodies) = parse(&source);
            assert_eq!(rules_of(&tcx, &bodies), [Rule::CheckRuns, Rule::GuardTag]);
        },
    );
    h.case(
        "verify/V11: an initialiser under a switch on another field",
        || {
            let source = edit(&fixture("ctor"), "overridden(a)", "overridden(b)");
            let (tcx, bodies) = parse(&source);
            let errors = verify(&tcx, &bodies[0]).expect_err("misplaced");
            let at: Vec<_> = errors.iter().map(|e| (e.rule, e.at)).collect();
            let init = Some(enrang_mir::Point::new(enrang_mir::BlockId(1), 0));
            assert!(at.contains(&(Rule::FieldInit, init)), "{at:?}");
        },
    );
    h.case(
        "verify/V14: a copy out of a `final` class needs no check",
        || {
            let (tcx, bodies) = parse(&fixture("classes"));
            assert_eq!(rules_of(&tcx, &bodies), []);
            let source = edit(&fixture("classes"), "@final class Leaf", "class Leaf");
            let (tcx, bodies) = parse(&source);
            assert_eq!(rules_of(&tcx, &bodies), [Rule::GuardClass]);
        },
    );
    h.case("verify/forof: the bind with no bounds check fails", || {
        let source = edit(
            &fixture("forof"),
            "    check_bounds(copy _2, copy _3);\n",
            "",
        );
        let source = edit(&source, "bind bb2[3]", "bind bb2[2]");
        let (tcx, bodies) = parse(&source);
        assert_eq!(rules_of(&tcx, &bodies), [Rule::GuardBounds]);
    });
    h.case(
        "verify/errors come in point order, each with its rule",
        || {
            let source = edit(&fixture("valid"), "    check_tag(_3, Present);\n", "");
            let source = edit(&source, "    check_bounds(copy _2, copy _8);\n", "");
            let (tcx, bodies) = parse(&source);
            let errors = verify(&tcx, &bodies[0]).expect_err("two guards are missing");
            let rules: Vec<Rule> = errors.iter().map(|e| e.rule).collect();
            assert_eq!(rules, [Rule::GuardBounds, Rule::GuardTag]);
            let points: Vec<_> = errors.iter().map(|e| e.at).collect();
            let mut sorted = points.clone();
            sorted.sort();
            assert_eq!(points, sorted);
        },
    );
}
