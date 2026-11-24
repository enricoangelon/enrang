//! Calls (plan d.9's `call.rs`; owner 3B): one known signature (arity EN0423,
//! counting defaults and `?`; each argument at its parameter), the callee forms
//! (functions, methods with their receivers, `static` methods through types,
//! namespaces' functions, `fn` and closure values, forms, `super`), and the codes
//! EN0219, EN0303, EN0428, EN0606 and EN0908 at calls; then SPEC's programs, which
//! report none of 3B's codes beyond what their cases expect.

use enrang_hir::{Adjust, Callee, ExprKind, FormKind, IntrinsicKind, LocalKind, StmtKind, TyKind};
use enrang_sema::LibSource;
use enrang_target::Feature;
use enrang_testkit::{Harness, extract_cases};

use crate::paths::{body, diags, expr_stmt, init, main_en, main_lib, returned, ty};
use crate::support::{MINI_LIB, fake_lib, run, run_with};

/// The codes stage 3B reports (plan h.1).
const CALL_CODES: &[&str] = &[
    "EN0219", "EN0303", "EN0308", "EN0413", "EN0423", "EN0428", "EN0441", "EN0606",
];

const COUNTER: &str = "public class Counter {
  public n: i64;
  public bump(): void {}
  public move close(): i64 { return 0; }
  public static make(): Counter { unreachable(); }
}
";

pub fn register(h: &mut Harness) {
    functions(h);
    methods(h);
    statics(h);
    values(h);
    forms(h);
    supers(h);
    inherited(h);
    spec(h);
    fixes(h);
    pinned(h);
    review(h);
}

fn functions(h: &mut Harness) {
    h.case("calls/a function call: `Callee::Fn`, no receiver, at its result type", || {
        let r = main_en(
            "public function g(x: i64): bool { return true; }
public function f(a: i64): bool { return g(a); }
",
        );
        r.clean();
        let e = returned(body(&r, "main::f"));
        let ExprKind::Call {
            callee,
            receiver,
            args,
        } = &e.kind
        else {
            panic!("{e:?}");
        };
        assert!(matches!(callee, Callee::Fn(f) if f.def == r.def("main::g") && r.tcx.list(f.args).is_empty()));
        assert!(receiver.is_none());
        assert_eq!(args.len(), 1);
        assert_eq!(ty(&r, args[0].ty), "i64");
        assert_eq!(ty(&r, e.ty), "bool");
    });
    h.case("calls/EN0423: too many arguments", || {
        let r = main_en(
            "public function g(x: i64): void {}
public function f(a: i64): void { g(a, a); }
",
        );
        assert_eq!(
            r.rendered(),
            "error[EN0423]: `g` takes 1 argument, but 2 were given
 --> main.en:2:35
  |
1 | public function g(x: i64): void {}
  |                 - `g` is declared here
2 | public function f(a: i64): void { g(a, a); }
  |                                   ^^^^^^^ too many arguments
  |
  = explain: run `enrang explain EN0423`

error: aborting due to 1 previous error
"
        );
    });
    h.case("calls/EN0423: too few, counting defaults and `?` (S:827)", || {
        let r = main_en(
            "public function greet(name: &string, greeting: &string = \"hello\", end?: &string): void {}
public function none(): void {}
public function f(n: &string): void {
  greet(n);
  greet(n, n);
  greet(n, n, n);
  greet();
  greet(n, n, n, n);
  none(n);
}
",
        );
        assert_eq!(
            diags(&r),
            [
                "EN0423 7:3 `greet` takes 1 to 3 arguments, but none were given [too few arguments]",
                "EN0423 8:3 `greet` takes 1 to 3 arguments, but 4 were given [too many arguments]",
                "EN0423 9:3 `none` takes no arguments, but 1 was given [too many arguments]",
            ]
        );
    });
    h.case(
        "calls/the arguments of a rejected call are still typed",
        || {
            let r = main_en(
                "public function g(x: i64): void {}
public function f(): void { g(1, nope); }
",
            );
            assert_eq!(r.codes(), ["EN0423", "EN0301"], "{}", r.rendered());
        },
    );
    h.case(
        "calls/an unresolved callee is EN0301 and its arguments are typed",
        || {
            let r = main_en("public function f(): void { gree(missing); }\n");
            assert_eq!(
                diags(&r),
                [
                    "EN0301 1:29 cannot find `gree` in this scope [not found]",
                    "EN0301 1:34 cannot find `missing` in this scope [not found]",
                ]
            );
        },
    );
}

fn methods(h: &mut Harness) {
    h.case("calls/a method's receiver: auto-borrowed place, reference as it is, `Box` derefs", || {
        let r = main_en(&format!(
            "{COUNTER}public function f(c: Counter, r: &Counter, b: Box<Counter>): void {{ c.bump(); r.bump(); b.bump(); }}\n"
        ));
        r.clean();
        let b = body(&r, "main::f");
        let receiver = |n: usize| match &expr_stmt(b, n).kind {
            ExprKind::Call {
                callee: Callee::Fn(f),
                receiver: Some(recv),
                args,
            } => {
                assert_eq!(f.def, r.def("main::Counter::bump"));
                assert!(args.is_empty());
                (recv.kind.clone(), recv.adjust.clone(), ty(&r, recv.ty))
            }
            other => panic!("{other:?}"),
        };
        let (kind, adjust, recv_ty) = receiver(0);
        assert!(matches!(kind, ExprKind::Local(_)));
        assert_eq!(adjust, [Adjust::AutoBorrow]);
        assert_eq!(recv_ty, "Counter");
        let (kind, adjust, recv_ty) = receiver(1);
        assert!(matches!(kind, ExprKind::Local(_)));
        assert!(adjust.is_empty());
        assert_eq!(recv_ty, "&Counter");
        let (kind, adjust, recv_ty) = receiver(2);
        assert!(matches!(kind, ExprKind::Local(_)));
        assert_eq!(adjust, [Adjust::BoxDeref, Adjust::AutoBorrow]);
        assert_eq!(recv_ty, "Box<Counter>");
    });
    h.case(
        "calls/a `move` method takes the place the lookup reached",
        || {
            let r = main_en(&format!(
                "{COUNTER}public function f(c: Counter): i64 {{ return c.close(); }}\n"
            ));
            r.clean();
            let e = returned(body(&r, "main::f"));
            let ExprKind::Call {
                receiver: Some(recv),
                ..
            } = &e.kind
            else {
                panic!("{e:?}");
            };
            assert!(matches!(recv.kind, ExprKind::Local(_)));
            assert!(recv.adjust.is_empty());
            assert_eq!(ty(&r, e.ty), "i64");
        },
    );
    h.case(
        "calls/an integer variable not yet decided reaches the `__Int` members (d.8)",
        || {
            let r = main_lib(
                "public function f(): void {
  let a = 5;
  const b = a.checkedAdd(1);
  const c = a;
  let d = 7;
  const e = d.checkedAdd(1);
  const g: i64 = d;
}
",
            );
            r.clean();
            let b = body(&r, "main::f");
            // Decided by nothing, `a` takes the default; `Self` is `a`'s type.
            assert_eq!(ty(&r, init(b, 0).ty), "int");
            let call = init(b, 1);
            let ExprKind::Call {
                receiver: Some(recv),
                ..
            } = &call.kind
            else {
                panic!("{call:?}");
            };
            assert_eq!(ty(&r, recv.ty), "int");
            assert_eq!(ty(&r, call.ty), "int | null");
            // Decided after the call, `d`'s `Self` follows it.
            assert_eq!(ty(&r, init(b, 3).ty), "i64");
            assert_eq!(ty(&r, init(b, 4).ty), "i64 | null");
        },
    );
    h.case("calls/a method of a generic class at the receiver's arguments", || {
        let r = main_en(
            "public class Stack<T> { private items: T[]; public push(x: T): void {} public peek(): T { unreachable(); } }
public function f(s: &Stack<string>, v: string): string { s.push(v); return s.peek(); }
",
        );
        r.clean();
        let b = body(&r, "main::f");
        let ExprKind::Call {
            callee: Callee::Fn(f),
            args,
            ..
        } = &expr_stmt(b, 0).kind
        else {
            panic!();
        };
        assert_eq!(r.tcx.list(f.args).iter().map(|&t| ty(&r, t)).collect::<Vec<_>>(), ["string"]);
        assert_eq!(ty(&r, args[0].ty), "string");
        assert_eq!(ty(&r, returned(b).ty), "string");
    });
    h.case("calls/a chain of members and calls: `w.inner.get()`", || {
        let r = main_en(
            "public class Inner { public get(): i64 { return 1; } }
public class Wrap { public inner: Inner; }
public function f(w: &Wrap): i64 { return w.inner.get(); }
",
        );
        r.clean();
        let e = returned(body(&r, "main::f"));
        let ExprKind::Call {
            receiver: Some(recv),
            ..
        } = &e.kind
        else {
            panic!("{e:?}");
        };
        assert!(matches!(&recv.kind, ExprKind::Field(base, _) if matches!(base.kind, ExprKind::Deref(_))));
        assert_eq!(recv.adjust, [Adjust::AutoBorrow]);
    });
    h.case("calls/a `Slice` member from an array: C18 on the receiver (G9)", || {
        let r = main_en("public function f(xs: &i64[], fixed: i64[3]): isize { xs.length(); return fixed.length(); }\n");
        r.clean();
        let b = body(&r, "main::f");
        let ExprKind::Call {
            receiver: Some(recv),
            ..
        } = &expr_stmt(b, 0).kind
        else {
            panic!();
        };
        assert_eq!(recv.adjust, [Adjust::ArrayToSlice]);
        assert_eq!(ty(&r, recv.ty), "&i64[]");
        let ExprKind::Call {
            receiver: Some(recv),
            ..
        } = &returned(b).kind
        else {
            panic!();
        };
        assert_eq!(recv.adjust, [Adjust::AutoBorrow, Adjust::FixedToSlice]);
    });
    h.case(
        "calls/a member of a nullable type: `extend<T> T | null` at `T := i64`",
        || {
            let r = main_en("public function f(p: i64 | null): i64 { return p.unwrapOr(0); }\n");
            r.clean();
            let e = returned(body(&r, "main::f"));
            let ExprKind::Call {
                receiver: Some(recv),
                ..
            } = &e.kind
            else {
                panic!("{e:?}");
            };
            assert_eq!(recv.adjust, [Adjust::AutoBorrow]);
            assert_eq!(ty(&r, e.ty), "i64");
        },
    );
    h.case("calls/`p?.m()` is `R | null`, and `void` for a `void` method (S:750)", || {
        let r = main_en(&format!(
            "{COUNTER}public function f(p: Counter | null): void {{ const a: i64 | null = p?.close(); p?.bump(); }}\n"
        ));
        r.clean();
        let b = body(&r, "main::f");
        let a = init(b, 0);
        assert_eq!(ty(&r, a.ty), "i64 | null");
        let ExprKind::OptionalChain(chain) = &a.kind else {
            panic!("{a:?}");
        };
        assert!(!chain.void_result);
        let bump = expr_stmt(b, 0);
        assert_eq!(ty(&r, bump.ty), "void");
        assert!(matches!(&bump.kind, ExprKind::OptionalChain(c) if c.void_result));
    });
    h.case(
        "calls/an interface parameter's method is a bound member (D5)",
        || {
            let r = main_en(
                "public interface Speaker { speak(): i64; }
public function f(s: &Speaker): i64 { return s.speak(); }
",
            );
            r.clean();
            let e = returned(body(&r, "main::f"));
            let ExprKind::Call {
                callee: Callee::BoundMember { found, member, .. },
                ..
            } = &e.kind
            else {
                panic!("{e:?}");
            };
            assert_eq!(*found, r.def("main::Speaker::speak"));
            assert_eq!(member.as_str(), "speak");
            assert_eq!(ty(&r, e.ty), "i64");
        },
    );
    h.case("calls/a class-bounded `T` calls the bound's public method (S:764)", || {
        let r = main_en(
            "public class Animal { public name: string; public fetch(): string { return this.name; } }
public function f<T extends Animal>(x: &T): string { return x.fetch(); }
",
        );
        r.clean();
        let e = returned(body(&r, "main::f"));
        assert!(matches!(&e.kind, ExprKind::Call { callee: Callee::BoundMember { found, .. }, .. } if *found == r.def("main::Animal::fetch")));
    });
    h.case(
        "calls/`Self` in an interface member is the receiver's class",
        || {
            let r = main_en(
                "public interface Maker { make(): Self; }
public function f<T extends Maker>(x: &T): void { const y: T = x.make(); }
",
            );
            r.clean();
            let e = init(body(&r, "main::f"), 0);
            assert!(
                matches!(r.tcx.kind(e.ty), TyKind::Param(_)),
                "{}",
                ty(&r, e.ty)
            );
            assert_eq!(ty(&r, e.ty), "T");
        },
    );
    h.case("calls/EN0606: `x.destructor()`, on a class and on a generic `T` (T:585)", || {
        let r = main_en(
            "public class R { private n: i64; public destructor() {} }
public function f(r: R): void { r.destructor(); }
public function g<T>(x: &T): void { x.destructor(); }
",
        );
        assert_eq!(
            diags(&r),
            [
                "EN0606 2:33 a destructor runs by itself: call `dispose(r)` [a destructor is never called by name]",
                "EN0606 3:37 a destructor runs by itself: call `dispose(x)` [a destructor is never called by name]",
            ]
        );
    });
    h.case("calls/`this.m()` passes `this`, already a reference", || {
        let r = main_en(
            "public class C { public n: i64; public a(): void {} public b(): void { this.a(); } }\n",
        );
        r.clean();
        let b = body(&r, "main::C::b");
        let ExprKind::Call {
            receiver: Some(recv),
            ..
        } = &expr_stmt(b, 0).kind
        else {
            panic!();
        };
        assert!(matches!(recv.kind, ExprKind::Local(l) if b.locals[l].kind == LocalKind::This));
        assert!(recv.adjust.is_empty());
    });
    h.case(
        "calls/a lang class's method: `s.length()` on a `&string`",
        || {
            let r = main_en("public function f(s: &string): isize { return s.length(); }\n");
            r.clean();
            let e = returned(body(&r, "main::f"));
            let ExprKind::Call {
                callee: Callee::Fn(f),
                receiver: Some(recv),
                ..
            } = &e.kind
            else {
                panic!("{e:?}");
            };
            assert_eq!(
                r.tcx.def(f.def).path.to_string(),
                "core/prelude::string::length"
            );
            assert!(recv.adjust.is_empty());
            assert_eq!(ty(&r, e.ty), "isize");
        },
    );
    h.case("calls/a field holding an `fn` value is called through it", || {
        let r = main_en(
            "public class H { public f: fn(x: i64) => bool; }
public function g(h: &H, v: i64): bool { return h.f(v); }
",
        );
        r.clean();
        let e = returned(body(&r, "main::g"));
        assert!(matches!(&e.kind, ExprKind::Call { callee: Callee::FnPtr(f), .. } if matches!(f.kind, ExprKind::Field(..))));
        assert_eq!(ty(&r, e.ty), "bool");
    });
    h.case("calls/EN0423 at a method, with its declaration", || {
        let r = main_en(&format!(
            "{COUNTER}public function f(c: &Counter): void {{ c.bump(1); }}\n"
        ));
        assert_eq!(
            diags(&r),
            ["EN0423 7:40 `bump` takes no arguments, but 1 was given [too many arguments]"]
        );
        assert_eq!(r.diags[0].secondary[0].text, "`bump` is declared here");
    });
    h.case(
        "calls/EN0303: a method called on an unnarrowed nullable, with the `?.` fix-it",
        || {
            let r = main_en(&format!(
                "{COUNTER}public function f(p: Counter | null): void {{ p.bump(); p.bmp(); }}\n"
            ));
            assert_eq!(
                diags(&r),
                [
                    "EN0303 7:48 `Counter | null` has no member `bump` [this value may be `null`]",
                    "EN0303 7:58 `Counter | null` has no member `bmp` [no such member]",
                ]
            );
            assert_eq!(
                r.diags[0].helps[0].message,
                "use `?.bump`, which reads it only when the value is not `null`"
            );
            assert_eq!(r.diags[1].helps[0].message, "did you mean `bump`?");
        },
    );
    h.case(
        "calls/EN0308: a private `static` method through its type",
        || {
            let r = main_en(
                "public class K { public n: i64; private static secret(): void {} }
public function f(): void { K.secret(); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0308 2:31 `secret` is private to `K` [only the body of `K` can use it]"]
            );
        },
    );
    h.case("calls/EN0303: a `static` method called on a value", || {
        let r = main_en(&format!(
            "{COUNTER}public function f(c: &Counter): void {{ c.make(); }}\n"
        ));
        assert_eq!(
            diags(&r),
            ["EN0303 7:42 `Counter` has no member `make` [a `static` method, not a member of each value]"]
        );
        assert_eq!(
            r.diags[0].entries[0].text,
            "`make` is `static`: call it through the type, `Counter.make()`"
        );
    });
}

fn statics(h: &mut Harness) {
    h.case("calls/a `static` method through its type: `Counter.make()`", || {
        let r = main_en(&format!(
            "{COUNTER}public function f(): Counter {{ return Counter.make(); }}\n"
        ));
        r.clean();
        let e = returned(body(&r, "main::f"));
        assert!(matches!(&e.kind, ExprKind::Call { callee: Callee::Fn(f), receiver: None, .. } if f.def == r.def("main::Counter::make")));
        assert_eq!(ty(&r, e.ty), "Counter");
    });
    h.case("calls/`Stack<i64>.empty()` and `i64[].withCapacity(8)` compile (T:641)", || {
        let r = main_lib(
            "public class Stack<T> { private items: T[]; public static empty(): Stack<T> { unreachable(); } }
public function f(): void { const s: Stack<i64> = Stack<i64>.empty(); const xs: i64[] = i64[].withCapacity(8); }
",
        );
        r.clean();
        let b = body(&r, "main::f");
        let s = init(b, 0);
        assert_eq!(ty(&r, s.ty), "Stack<i64>");
        let ExprKind::Call {
            callee: Callee::Fn(f),
            ..
        } = &s.kind
        else {
            panic!("{s:?}");
        };
        assert_eq!(r.tcx.list(f.args).iter().map(|&t| ty(&r, t)).collect::<Vec<_>>(), ["i64"]);
        assert_eq!(ty(&r, init(b, 1).ty), "i64[]");
    });
    h.case("calls/an `@intrinsic` member is `Callee::Intrinsic` with its payload", || {
        let r = main_lib(
            "public function f(p: *u8, n: isize): void { unsafe { const s: &Slice<u8> = Slice<u8>.fromRaw(p, n); } }\n",
        );
        r.clean();
        let b = body(&r, "main::f");
        let StmtKind::Unsafe(block) = &b.root.stmts[0].kind else {
            panic!("{:?}", b.root.stmts[0]);
        };
        let StmtKind::Let { init: Some(e), .. } = &block.stmts[0].kind else {
            panic!("{:?}", block.stmts[0]);
        };
        let ExprKind::Call {
            callee: Callee::Intrinsic(kind, _),
            receiver: None,
            ..
        } = &e.kind
        else {
            panic!("{e:?}");
        };
        assert_eq!(*kind, IntrinsicKind::SliceFromRaw(r.tcx.common().u8));
        assert_eq!(ty(&r, e.ty), "&Slice<u8>");
    });
    h.case("calls/EN0303: a member of each value called through the type", || {
        let r = main_en(&format!(
            "{COUNTER}public function f(): void {{ Counter.bump(); Counter.nope(); }}\n"
        ));
        assert_eq!(
            diags(&r),
            [
                "EN0303 7:37 `Counter` has no static member `bump` [a member of each value, not of the type]",
                "EN0303 7:53 `Counter` has no member `nope` [no such member]",
            ]
        );
    });
    h.case(
        "calls/EN0428: a case, a constant and a class called",
        || {
            let r = main_en(&format!(
                "{COUNTER}public enum Color {{ Red, Green }}
public function f(): void {{ Color.Red(); i64.MAX(); Counter(); }}
"
            ));
            assert_eq!(
                diags(&r),
                [
                    "EN0428 8:29 `Color.Red` is not callable [an enum case, not a function]",
                    "EN0428 8:42 `i64.MAX` is not callable [a constant, not a function]",
                    "EN0428 8:53 `Counter` is not callable [a type, not a function]",
                ]
            );
            // `Counter` has no constructor: it is made by naming its fields
            // (S:580), so arguments to `new` would be EN0449 (fix-6).
            assert_eq!(
                r.diags[2].helps[0].message,
                "create one by naming its fields: `new Counter { ... }`"
            );
            assert!(r.diags[2].helps[0].edits.is_empty());
        },
    );
    h.case(
        "calls/a namespace's function, and its private and missing ones",
        || {
            let r = run(&[
                (
                    "main.en",
                    "import * as u from \"./u\";
public function f(): i64 { u.hidden(); u.helpr(1); return u.helper(1); }
",
                ),
                (
                    "u.en",
                    "public function helper(n: i64): i64 { return n; }
private function hidden(): void {}
",
                ),
            ]);
            assert_eq!(
                diags(&r),
                [
                    "EN0311 2:30 `hidden` is private to `u.en` [a private item]",
                    "EN0301 2:42 cannot find `helpr` in `u` [not found]",
                ]
            );
            assert_eq!(r.diags[1].helps[0].message, "did you mean `helper`?");
        },
    );
    h.case("calls/a namespace's function is a `Callee::Fn`", || {
        let r = run(&[
            (
                "main.en",
                "import * as u from \"./u\";
public function f(): i64 { return u.helper(1); }
",
            ),
            ("u.en", "public function helper(n: i64): i64 { return n; }\n"),
        ]);
        r.clean();
        let e = returned(body(&r, "main::f"));
        assert!(matches!(&e.kind, ExprKind::Call { callee: Callee::Fn(f), .. } if f.def == r.def("u::helper")));
    });
}

fn values(h: &mut Harness) {
    h.case("calls/an `fn` value: `Callee::FnPtr`, arity checked", || {
        let r = main_en(
            "public function f(g: fn(x: i64) => bool, v: i64): bool { g(v, v); return g(v); }\n",
        );
        assert_eq!(
            diags(&r),
            ["EN0423 1:58 `g` takes 1 argument, but 2 were given [too many arguments]"]
        );
        assert!(r.diags[0].secondary.is_empty());
    });
    h.case("calls/an `fn` value's call is at its result type", || {
        let r = main_en("public function f(g: fn(x: i64) => bool, v: i64): bool { return g(v); }\n");
        r.clean();
        let e = returned(body(&r, "main::f"));
        assert!(matches!(&e.kind, ExprKind::Call { callee: Callee::FnPtr(f), .. } if matches!(f.kind, ExprKind::Local(_))));
        assert_eq!(ty(&r, e.ty), "bool");
    });
    h.case("calls/a closure parameter: `Callee::Closure`", || {
        let r = main_en(
            "public function on(key: u8, handler: (k: u8) => void): void { handler(key); }\n",
        );
        r.clean();
        let b = body(&r, "main::on");
        let ExprKind::Call {
            callee: Callee::Closure(local),
            ..
        } = &expr_stmt(b, 0).kind
        else {
            panic!();
        };
        assert!(matches!(b.locals[*local].kind, LocalKind::Param(_)));
    });
    h.case("calls/EN0428: an unnarrowed nullable closure (OQ24-onKey, T:916)", || {
        let r = main_en("private function onKey(key: u8, handler?: (k: u8) => void): void { handler(key); }\n");
        assert_eq!(
            r.rendered(),
            "error[EN0428]: `handler` may be `null`, so it can't be called
 --> main.en:1:68
  |
1 | private function onKey(key: u8, handler?: (k: u8) => void): void { handler(key); }
  |                                                                    ^^^^^^^ this may be `null`
  |
help: check it first: `if (handler != null) { handler(...); }`
  = explain: run `enrang explain EN0428`

error: aborting due to 1 previous error
"
        );
    });
    h.case("calls/EN0428: a value that is no function", || {
        let r = main_en("public function f(n: i64): void { n(1); }\n");
        assert_eq!(
            diags(&r),
            ["EN0428 1:35 `n` is not callable [its type is `i64`]"]
        );
    });
}

fn forms(h: &mut Harness) {
    h.case("calls/`console.log` reaches the form", || {
        let r = main_en("public function f(n: i64): void { console.log(n); }\n");
        r.clean();
        let e = expr_stmt(body(&r, "main::f"), 0);
        assert!(matches!(
            &e.kind,
            ExprKind::Call {
                callee: Callee::Form(FormKind::ConsoleLog),
                ..
            }
        ));
    });
    h.case("calls/`mem.forget` and `cpu.has` are forms through their namespaces", || {
        let r = main_lib(
            "import * as cpu from \"core/cpu\";
public function f(s: string): bool { mem.forget(s); return cpu.has(\"sse2\"); }
",
        );
        r.clean();
        let b = body(&r, "main::f");
        assert!(matches!(&expr_stmt(b, 0).kind, ExprKind::Call { callee: Callee::Form(FormKind::MemForget), args, .. } if args.len() == 1));
        let e = returned(b);
        assert!(matches!(&e.kind, ExprKind::Call { callee: Callee::Form(FormKind::CpuHas(Feature::Sse2)), .. }));
        assert_eq!(ty(&r, e.ty), "bool");
    });
    h.case("calls/EN0908 and EN0423 at the namespace forms", || {
        let r = main_lib(
            "import * as cpu from \"core/cpu\";
public function f(s: string, name: &string): void { cpu.has(\"sse9\"); cpu.has(name); mem.forget(s, s); }
",
        );
        assert_eq!(
            diags(&r),
            [
                "EN0908 2:61 unknown feature name `sse9` [a feature name, written as a string literal]",
                "EN0908 2:78 a feature name must be a string literal [a feature name, written as a string literal]",
                "EN0423 2:85 `mem.forget` takes 1 argument, but 2 were given [too many arguments]",
            ]
        );
    });
}

fn supers(h: &mut Harness) {
    h.case(
        "calls/`super.m()` calls the base's method directly, `this` upcast",
        || {
            let r = main_en(
                "public class A { public n: i64; public m(): i64 { return 1; } }
public class B extends A { public override m(): i64 { return super.m(); } }
",
            );
            r.clean();
            let e = returned(body(&r, "main::B::m"));
            let ExprKind::Call {
                callee: Callee::Super(f),
                receiver: Some(recv),
                ..
            } = &e.kind
            else {
                panic!("{e:?}");
            };
            assert_eq!(f.def, r.def("main::A::m"));
            assert_eq!(recv.adjust, [Adjust::Upcast]);
            assert_eq!(ty(&r, e.ty), "i64");
        },
    );
    h.case(
        "calls/`super(...)` calls the base's constructor, or its implicit one",
        || {
            let r = main_en(
                "public class A { public n: i64; public constructor(n: i64) {} }
public class B extends A { public constructor() { super(1); } }
public class C { public n: i64; }
public class D extends C { public constructor() { super(); } }
",
            );
            r.clean();
            let ctor = |path: &str| {
                let b = body(&r, path);
                match &expr_stmt(b, 0).kind {
                    ExprKind::Call {
                        callee: Callee::SuperCtor { ctor, .. },
                        ..
                    } => *ctor,
                    other => panic!("{other:?}"),
                }
            };
            assert_eq!(ctor("main::B::#ctor"), Some(r.def("main::A::#ctor")));
            assert_eq!(ctor("main::D::#ctor"), None);
        },
    );
    h.case("calls/EN0423 at `super(...)`", || {
        let r = main_en(
            "public class A { public n: i64; public constructor(n: i64) {} }
public class B extends A { public constructor() { super(); } }
",
        );
        assert_eq!(
            diags(&r),
            ["EN0423 2:51 `super` takes 1 argument, but none were given [too few arguments]"]
        );
    });
    h.case("calls/EN0219: `super` with no receiver, no base, or outside a constructor", || {
        let r = main_en(
            "public function f(): void { super.m(); }
public class C { public n: i64; public m(): void { super.m(); } }
public class A { public n: i64; }
public class B extends A { public m(): void { super(); } }
",
        );
        assert_eq!(
            diags(&r),
            [
                "EN0219 1:29 `super` outside a method [there is no object here]",
                "EN0219 2:52 `super` in `C`, which extends no class [there is no base class here]",
                "EN0219 4:47 `super(...)` outside a constructor [only a constructor calls its base's]",
            ]
        );
    });
    h.case("calls/EN0303 and EN0308 at `super.m()`", || {
        let r = main_en(
            "public class A { public n: i64; private p(): void {} }
public class B extends A { public m(): void { super.q(); super.p(); } }
",
        );
        assert_eq!(
            diags(&r),
            [
                "EN0303 2:53 `A` has no method `q` [no such method in the base class]",
                "EN0308 2:64 `p` is private to `A` [only the body of `A` can use it]",
            ]
        );
    });
}

/// The classes of TESTING `C21-inherited`, with a grandchild, a generic method and
/// an override.
const ANIMALS: &str = "public class Animal {
  public name: string = \"\";
  public label(): &string { return &this.name; }
  public rename(n: &string): void { this.name = n.toString(); }
  public show<T>(x: &T): void { console.log(x); }
  public static make(): Animal { return new Animal(); }
}
public class Dog extends Animal {
  public override rename(n: &string): void { this.name = n.toString(); }
  public fetch(): void { this.label(); this.rename(&\"a\".toString()); }
}
public class Puppy extends Dog {}
";

/// The receiver adjusts of each statement-level method call in `path`'s body.
fn receivers(r: &crate::support::Run, path: &str) -> Vec<Vec<Adjust>> {
    let b = body(r, path);
    (0..b.root.stmts.len())
        .filter_map(|n| match &b.root.stmts[n].kind {
            StmtKind::Expr(e) => match &e.kind {
                ExprKind::Call {
                    receiver: Some(recv),
                    ..
                } => Some(recv.adjust.clone()),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

/// C21 on an inherited method's receiver (A:2.4, A:4, XC-03(5)): typing records
/// `Upcast` after the receiver's `AutoBorrow` or `Reborrow` whenever the method
/// lookup reaches is declared in a proper base class, so MIR building reads it.
fn inherited(h: &mut Harness) {
    h.case(
        "calls/C21-inherited: an inherited method's receiver is auto-borrowed, then upcast",
        || {
            let r = main_en(&format!(
                "public function f(): void {{
  let d = new Dog();
  d.label();
  d.rename(&\"Max\".toString());
  let p = new Puppy();
  p.label();
  p.rename(&\"Rex\".toString());
  p.fetch();
}}
{ANIMALS}"
            ));
            r.clean();
            assert_eq!(
                receivers(&r, "main::f"),
                [
                    // `Animal.label`, inherited.
                    vec![Adjust::AutoBorrow, Adjust::Upcast],
                    // `Dog.rename`, the class's own override.
                    vec![Adjust::AutoBorrow],
                    // From the grandchild: one `Upcast`, to the declaring class.
                    vec![Adjust::AutoBorrow, Adjust::Upcast],
                    vec![Adjust::AutoBorrow, Adjust::Upcast],
                    vec![Adjust::AutoBorrow, Adjust::Upcast],
                ]
            );
        },
    );
    h.case(
        "calls/C21-inherited: a reference receiver, `this` and a `Box` upcast too",
        || {
            let r = main_en(&format!(
                "public function f(d: &Dog, b: Box<Dog>): void {{
  d.label();
  d.rename(&\"Max\".toString());
  b.label();
}}
{ANIMALS}"
            ));
            r.clean();
            assert_eq!(
                receivers(&r, "main::f"),
                [
                    vec![Adjust::Upcast],
                    Vec::new(),
                    vec![Adjust::BoxDeref, Adjust::AutoBorrow, Adjust::Upcast],
                ]
            );
            // In `Dog.fetch`: `this.label()` is inherited, `this.rename` is Dog's.
            assert_eq!(
                receivers(&r, "main::Dog::fetch"),
                [vec![Adjust::Upcast], Vec::new()]
            );
        },
    );
    h.case(
        "calls/C21-inherited: a generic inherited method upcasts at the candidate run",
        || {
            let r = main_en(&format!(
                "public function f(d: &Dog): void {{
  let p = new Puppy();
  p.show(&1);
  d.show(&2);
}}
{ANIMALS}"
            ));
            r.clean();
            assert_eq!(
                receivers(&r, "main::f"),
                [
                    vec![Adjust::AutoBorrow, Adjust::Upcast],
                    vec![Adjust::Upcast]
                ]
            );
        },
    );
    h.case(
        "calls/C21-inherited: no upcast for a class's own method, a static one or a bound `T`",
        || {
            let r = main_en(&format!(
                "public function f<T extends Dog>(t: &T): void {{
  const a = new Animal();
  a.label();
  t.label();
  Animal.make();
}}
{ANIMALS}"
            ));
            r.clean();
            assert_eq!(
                receivers(&r, "main::f"),
                [vec![Adjust::AutoBorrow], Vec::new()]
            );
            // `super.m()` keeps its own single `Upcast`.
            let r = main_en(&format!(
                "public class Hound extends Puppy {{
  public override rename(n: &string): void {{ super.rename(n); super.label(); super.show(&1); }}
}}
{ANIMALS}"
            ));
            r.clean();
            // `super.show(&1)` reaches the generic `Animal.show` through 4A's seam,
            // which adds no second `Upcast`.
            assert_eq!(
                receivers(&r, "main::Hound::rename"),
                [
                    vec![Adjust::Upcast],
                    vec![Adjust::Upcast],
                    vec![Adjust::Upcast]
                ]
            );
        },
    );
}

fn spec(h: &mut Harness) {
    h.case(
        "calls/SPEC's programs report none of 3B's codes beyond what their cases expect",
        || {
            let doc =
                std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/../../docs/SPEC.md"))
                    .expect("SPEC");
            let cases = extract_cases(&doc).expect("the cases extract");
            let ours = |code: &str| CALL_CODES.contains(&code);
            let mut seen = 0;
            for case in cases {
                if case.files.is_empty() || case.files.iter().any(|f| !f.name.ends_with(".en")) {
                    continue;
                }
                let target = ["i386-none", "i386-linux", "x86_64-none"]
                    .into_iter()
                    .find(|t| case.cmd.contains(t))
                    .unwrap_or("x86_64-linux");
                let files: Vec<(&str, &str)> = case
                    .files
                    .iter()
                    .map(|f| (f.name.as_str(), f.contents.as_str()))
                    .collect();
                let r = run_with(&files, LibSource::Embedded, target);
                let reported: Vec<String> = r
                    .diags
                    .iter()
                    .map(|d| d.code.name().to_owned())
                    .filter(|c| ours(c))
                    .collect();
                let expected: Vec<String> = case
                    .stderr
                    .text
                    .lines()
                    .filter_map(|l| l.split_once('[').and_then(|(_, rest)| rest.split_once(']')))
                    .map(|(code, _)| code.to_owned())
                    .filter(|c| ours(c))
                    .collect();
                assert_eq!(reported, expected, "{}: {}", case.id, r.rendered());
                seen += 1;
            }
            assert!(seen >= 30, "the tour, ownership, G and S cases: {seen}");
        },
    );
}

// Review fixes: inferred callees, `new` only for classes, `fn` fields through `?.`.
fn fixes(h: &mut Harness) {
    h.case(
        "calls/a local a later assignment made an `fn` is called",
        || {
            let r = main_en(
                "public function inc(n: i64): i64 { return n + 1; }
public function f(): void { let g; g = inc; const v = g(1); }
",
            );
            r.clean();
            let b = body(&r, "main::f");
            let v = b
                .root
                .stmts
                .iter()
                .find_map(|s| match &s.kind {
                    StmtKind::Let { init: Some(e), .. } => Some(e),
                    _ => None,
                })
                .expect("`const v`");
            assert!(
                matches!(
                    v.kind,
                    ExprKind::Call {
                        callee: Callee::FnPtr(_),
                        ..
                    }
                ),
                "{v:?}"
            );
            assert_eq!(ty(&r, v.ty), "i64");
        },
    );
    h.case(
        "calls/EN0428: only a class called as a function gets the `new` fix-it",
        || {
            let r = main_en(
                "public enum E { A }
public interface Speaker { speak(): i64; }
public type Num = i64;
public class K { public constructor() {} }
public type Kay = K;
public function f(): void { E(); Speaker(); Num(); K(); Kay(); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0428 6:29 `E` is not callable [a type, not a function]",
                    "EN0428 6:34 `Speaker` is not callable [a type, not a function]",
                    "EN0428 6:45 `Num` is not callable [a type, not a function]",
                    "EN0428 6:52 `K` is not callable [a type, not a function]",
                    "EN0428 6:57 `Kay` is not callable [a type, not a function]",
                ]
            );
            let fixits: Vec<usize> = r.diags.iter().map(|d| d.helps.len()).collect();
            assert_eq!(fixits, [0, 0, 0, 1, 1]);
            let edit = &r.diags[3].helps[0].edits[0];
            assert_eq!(edit.replacement, "new ");
            assert_eq!(edit.span.lo, r.diags[3].primary.span.lo);
            assert_eq!(edit.span.hi, r.diags[3].primary.span.lo);
        },
    );
    h.case(
        "calls/EN0428: an `fn` field called through `?.` asks for the check first",
        || {
            let r = main_en(
                "public class W { public on: fn(k: u8) => void; public maybe: (fn(k: u8) => void) | null; }
public function f(w: &W, o: W | null): void { w.on(1); w.maybe(2); o?.on(3); }
",
            );
            assert_eq!(
                diags(&r),
                [
                    "EN0428 2:56 `w.maybe` may be `null`, so it can't be called [this may be `null`]",
                    "EN0428 2:68 `o?.on` may be `null`, so it can't be called [this may be `null`]",
                ]
            );
            assert_eq!(
                r.diags[1].helps[0].message,
                "check it first: `if (o != null) { o.on(...); }`"
            );
        },
    );
}

/// The fake library with `extra` added to the module `key` (replacing it when
/// the library has none), for `target`'s OS layer at `os`.
fn lib_plus(key: &str, extra: &str, os: &str) -> LibSource {
    let mut modules: Vec<(String, String)> = MINI_LIB
        .iter()
        .map(|(k, t)| {
            let k = if k.starts_with("os/") {
                os.to_owned()
            } else {
                (*k).to_owned()
            };
            (k, (*t).to_owned())
        })
        .collect();
    match modules.iter_mut().find(|(k, _)| k == key) {
        Some((_, text)) => text.push_str(extra),
        None => modules.push((key.to_owned(), extra.to_owned())),
    }
    let borrowed: Vec<(&str, &str)> = modules
        .iter()
        .map(|(k, t)| (k.as_str(), t.as_str()))
        .collect();
    fake_lib(&borrowed)
}

/// The callee of the call in the `n`th statement of the first `unsafe` block of
/// `main::f`.
fn unsafe_callee(r: &crate::support::Run, n: usize) -> Callee {
    let b = body(r, "main::f");
    let block = b
        .root
        .stmts
        .iter()
        .find_map(|s| match &s.kind {
            StmtKind::Unsafe(block) => Some(block),
            _ => None,
        })
        .expect("an `unsafe` block");
    match &block.stmts[n].kind {
        StmtKind::Expr(e) => match &e.kind {
            ExprKind::Call { callee, .. } => callee.clone(),
            other => panic!("{other:?}"),
        },
        other => panic!("{other:?}"),
    }
}

// Behaviour the mutation gate showed untested.
fn pinned(h: &mut Harness) {
    h.case(
        "calls/a method through `&Box<T[]>`: the receiver after its `Deref` and `BoxDeref`",
        || {
            let r = main_lib("public function f(r: &Box<i64[]>): isize { return r.length(); }\n");
            r.clean();
            let ExprKind::Call {
                receiver: Some(recv),
                ..
            } = &returned(body(&r, "main::f")).kind
            else {
                panic!("a call");
            };
            assert!(matches!(recv.kind, ExprKind::Deref(_)), "{recv:?}");
            assert_eq!(recv.adjust, vec![Adjust::BoxDeref, Adjust::AutoBorrow]);
        },
    );
    h.case(
        "calls/`c?.h()` with a nullable result is not wrapped again",
        || {
            let r = main_en(
                "public class C { public h(): i64 | null { return null; } }
public function f(c: C | null): void { const v = c?.h(); }
",
            );
            r.clean();
            assert_eq!(ty(&r, init(body(&r, "main::f"), 0).ty), "i64 | null");
        },
    );
    h.case(
        "calls/an intrinsic, a host call and a foreign function are their callees",
        || {
            let mem = "public final class Mem<T> {\n  private x: usize;\n  @intrinsic(\"SizeOf\") public static size(): usize;\n}\n";
            let lib = lib_plus("core/prelude", mem, "os/linux_x64/prelude");
            let src = "public function f(): void { const n = Mem<i64>.size(); }\n";
            let r = run_with(&[("main.en", src)], lib, "x86_64-linux");
            r.clean();
            let ExprKind::Call {
                callee: Callee::Intrinsic(kind, _),
                ..
            } = &init(body(&r, "main::f"), 0).kind
            else {
                panic!("an intrinsic call");
            };
            assert_eq!(*kind, IntrinsicKind::SizeOf(r.tcx.common().i64));

            let host = "@hostCall(\"vm.tick\") public declare function tick(): void;\n";
            let lib = lib_plus("os/vm/prelude", host, "os/vm/prelude");
            let src = "public function f(): void { unsafe { tick(); } }\n";
            let r = run_with(&[("main.en", src)], lib, "vm64");
            r.clean();
            assert!(matches!(unsafe_callee(&r, 0), Callee::HostCall(_)));

            let dll = "@dll(\"kernel32\") public declare function Sleep(ms: u32): void;\n";
            let lib = lib_plus("os/windows/prelude", dll, "os/windows/prelude");
            let src = "public function f(): void { unsafe { Sleep(1); } }\n";
            let r = run_with(&[("main.en", src)], lib, "x86_64-windows");
            r.clean();
            assert_eq!(
                unsafe_callee(&r, 0),
                Callee::Foreign(r.def("os/windows/prelude::Sleep"))
            );
        },
    );
    h.case("calls/`mem.forget()` with no argument is EN0423", || {
        let r = main_lib("public function f(): void { mem.forget(); }\n");
        assert_eq!(
            diags(&r),
            ["EN0423 1:29 `mem.forget` takes 1 argument, but none were given [too few arguments]"]
        );
    });
    h.case(
        "calls/an extra argument and an unresolved callee's arguments keep their own errors",
        || {
            let r = main_en(
                "public function one(a: i64): void { }
public function f(): void { one(1, \"a\" - 1); nope(\"b\" - 1); }
",
            );
            assert_eq!(
                r.codes(),
                vec!["EN0423", "EN0420", "EN0301", "EN0420"],
                "{}",
                r.rendered()
            );
        },
    );
    h.case("calls/a member of a form that has none is EN0303", || {
        let r = main_en("public function f(): void { panic.x(); }\n");
        assert_eq!(
            diags(&r),
            ["EN0303 1:35 `panic` has no member `x` [no such member]"]
        );
    });
    h.case(
        "calls/EN0423 at a library method names no declaration",
        || {
            let r = main_en("public function f(s: &string): isize { return s.length(1); }\n");
            assert_eq!(
                diags(&r),
                ["EN0423 1:47 `length` takes no arguments, but 1 was given [too many arguments]"]
            );
            assert!(r.diags[0].secondary.is_empty());
        },
    );
    h.case(
        "calls/a nullable `fn` field is EN0428 `may be null`",
        || {
            let r = main_en(
                "public class W { public maybe: (fn(k: u8) => void) | null; }
public function f(w: &W): void { w.maybe(2); }
",
            );
            assert_eq!(
                diags(&r),
                ["EN0428 2:34 `w.maybe` may be `null`, so it can't be called [this may be `null`]"]
            );
        },
    );
}

/// Stage 6's review fixes of member lookup: `where` bounds and `Box<?T>`.
fn review(h: &mut Harness) {
    h.case(
        "calls/S:323: a method's body calls the members its `where` clause adds to `T`",
        || {
            let r = main_lib(
                "public interface Speaker { speak(): string; }
public class Bag<T> {
  public items: T[] = [];
  public cmp(a: &T, b: &T): i32 where T extends Ord { return a.compare(b); }
  public talk(x: &T): string where T extends Speaker { return x.speak(); }
  public plain(x: &T): string { return x.speak(); }
}
",
            );
            assert_eq!(
                diags(&r),
                ["EN0303 6:42 `T` has no member `speak` [no such member]"]
            );
        },
    );
    h.case(
        "calls/S:607: lookup through an unannotated `new Box(x)` reaches the boxed class",
        || {
            let r = main_lib(
                "public class P { public x: i64 = 0; public m(): i64 { return 1; } }
public function g(): void { const b = new Box(new P {}); const s: i64 = b.m(); const t: i64 = b.x; }
",
            );
            r.clean();
            let b = body(&r, "main::g");
            assert_eq!(ty(&r, init(b, 1).ty), "i64");
            assert_eq!(ty(&r, init(b, 2).ty), "i64");
        },
    );
}
