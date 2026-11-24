//! GenTypes (TESTING 14, plan g.1; owner 5A): generated well-typed programs pass
//! phase 2 with no diagnostic, and one mutation of each gives exactly the code it
//! was made to give, at the line it changed; nothing panics.
//!
//! A program is built from a seeded tape of choices: integer, float, string and
//! `bool` locals from literals and arithmetic of one type, calls to generated
//! functions, a class with written field defaults built with a named form and read
//! through a `&` parameter, a `T | null` narrowed by `!= null` before arithmetic,
//! and an exhaustive `match` over a generated enum. Each local is read once, by
//! `console.log`, which takes any type, so a mutation changes one statement's
//! verdict and no other. The mutations are TESTING 14's four: a type changed (an
//! annotation made `string` or `bool` against a value of another type, EN0401), a
//! `&` dropped from an argument of class type (EN0612), an arm dropped from a
//! `match` (EN0501), and a field added to a named form (EN0434).
//!
//! `scaled(200)` programs by default, a tenth of TESTING 23's 2k as TESTING 14 sets
//! the default scale; `ENRANG_SCALE=10` runs the full volume. A failure prints
//! `ENRANG_SEED` and the program.

use enrang_base::Span;
use enrang_sema::LibSource;
use enrang_testkit::{Harness, Rng, Xoshiro256, catch_panic, rng_for, scaled, seed};

use crate::support::{Run, run_with};

/// What a mutation must report.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Kind {
    /// An annotation of another type than its value's: EN0401.
    ChangeType,
    /// A class value passed where `&C` is taken: EN0612.
    DropRef,
    /// A `match` missing a case: EN0501.
    DropArm,
    /// A named form naming a field its class lacks: EN0434.
    AddField,
}

impl Kind {
    fn code(self) -> &'static str {
        match self {
            Kind::ChangeType => "EN0401",
            Kind::DropRef => "EN0612",
            Kind::DropArm => "EN0501",
            Kind::AddField => "EN0434",
        }
    }
}

/// A mutation: the statement line it replaces, by index, and with what.
#[derive(Clone, Debug)]
struct Mutation {
    kind: Kind,
    line: usize,
    text: String,
}

/// A generated program: its statement lines, its declaration lines, and the
/// mutations each statement offers.
#[derive(Clone, Debug, Default)]
struct Program {
    stmts: Vec<String>,
    decls: Vec<String>,
    mutations: Vec<Mutation>,
}

impl Program {
    /// The program's text, statements first (SPEC 3: imports, statements, then
    /// declarations), with the statement at `replace` swapped for the mutant's.
    fn text(&self, replace: Option<&Mutation>) -> String {
        let mut out = String::new();
        for (i, line) in self.stmts.iter().enumerate() {
            match replace {
                Some(m) if m.line == i => out.push_str(&m.text),
                _ => out.push_str(line),
            }
            out.push('\n');
        }
        out.push('\n');
        for line in &self.decls {
            out.push_str(line);
            out.push('\n');
        }
        out
    }

    /// The 1-based line the statement at `index` starts on.
    fn line_of_stmt(&self, index: usize) -> usize {
        1 + self.stmts[..index]
            .iter()
            .map(|s| s.lines().count())
            .sum::<usize>()
    }

    fn stmt(&mut self, text: String) -> usize {
        self.stmts.push(text);
        self.stmts.len() - 1
    }

    fn offer(&mut self, kind: Kind, line: usize, text: String) {
        self.mutations.push(Mutation { kind, line, text });
    }
}

/// A scalar type the generator writes, with literals and an operator of it.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Scalar {
    I64,
    F64,
    Str,
    Bool,
}

impl Scalar {
    const ALL: [Scalar; 4] = [Scalar::I64, Scalar::F64, Scalar::Str, Scalar::Bool];

    fn name(self) -> &'static str {
        match self {
            Scalar::I64 => "i64",
            Scalar::F64 => "f64",
            Scalar::Str => "string",
            Scalar::Bool => "bool",
        }
    }

    /// A type no value of `self` converts to.
    fn other(self) -> Scalar {
        match self {
            Scalar::Str => Scalar::Bool,
            _ => Scalar::Str,
        }
    }

    fn default_text(self) -> &'static str {
        match self {
            Scalar::I64 => "0",
            Scalar::F64 => "0.0",
            Scalar::Str => "\"\"",
            Scalar::Bool => "false",
        }
    }
}

/// The generator's state: its tape and the names it has made.
struct Gen<'r> {
    rng: &'r mut Xoshiro256,
    next: usize,
    /// Functions of one scalar type: name, parameter count, type.
    fns: Vec<(String, usize, Scalar)>,
}

impl Gen<'_> {
    fn below(&mut self, n: usize) -> usize {
        self.rng.below(n as u64) as usize
    }

    fn fresh(&mut self, stem: &str) -> String {
        self.next += 1;
        format!("{stem}{}", self.next)
    }

    fn scalar(&mut self) -> Scalar {
        Scalar::ALL[self.below(4)]
    }

    fn literal(&mut self, t: Scalar) -> String {
        match t {
            Scalar::I64 => format!("{}", self.below(1000)),
            Scalar::F64 => format!("{}.5", self.below(100)),
            Scalar::Str => format!("\"s{}\"", self.below(100)),
            Scalar::Bool => ["true", "false"][self.below(2)].to_owned(),
        }
    }

    /// An expression of type `t`, `depth` levels deep at most, with `vars` the
    /// parameters in scope.
    fn expr(&mut self, t: Scalar, depth: usize, vars: &[(String, Scalar)]) -> String {
        let in_scope: Vec<&String> = vars
            .iter()
            .filter(|(_, vt)| *vt == t)
            .map(|(name, _)| name)
            .collect();
        let choice = if depth == 0 { 0 } else { self.below(5) };
        match choice {
            1 if !in_scope.is_empty() => in_scope[self.below(in_scope.len())].clone(),
            2 => {
                let a = self.expr(t, depth - 1, vars);
                let b = self.expr(t, depth - 1, vars);
                match t {
                    Scalar::I64 => format!("({a} {} {b})", ["+", "-", "*"][self.below(3)]),
                    Scalar::F64 => format!("({a} {} {b})", ["+", "-", "*", "/"][self.below(4)]),
                    Scalar::Str => format!("({a} + {b})"),
                    Scalar::Bool => format!("({a} {} {b})", ["&&", "||"][self.below(2)]),
                }
            }
            3 if t == Scalar::Bool => {
                let n = [Scalar::I64, Scalar::F64][self.below(2)];
                let a = self.expr(n, depth - 1, vars);
                let b = self.expr(n, depth - 1, vars);
                format!("({a} {} {b})", ["<", "<=", "==", "!="][self.below(4)])
            }
            4 => {
                let fitting: Vec<(String, usize)> = self
                    .fns
                    .iter()
                    .filter(|(_, _, ft)| *ft == t)
                    .map(|(name, arity, _)| (name.clone(), *arity))
                    .collect();
                if fitting.is_empty() {
                    return self.literal(t);
                }
                let (name, arity) = fitting[self.below(fitting.len())].clone();
                let args: Vec<String> = (0..arity).map(|_| self.expr(t, depth - 1, vars)).collect();
                format!("{name}({})", args.join(", "))
            }
            _ => self.literal(t),
        }
    }

    /// A function of one scalar type, declared for later statements to call.
    fn function(&mut self, p: &mut Program) {
        let t = self.scalar();
        let name = self.fresh("f");
        let arity = 1 + self.below(3);
        let params: Vec<(String, Scalar)> = (0..arity).map(|i| (format!("a{i}"), t)).collect();
        let body = self.expr(t, 2, &params);
        let list: Vec<String> = params
            .iter()
            .map(|(n, pt)| format!("{n}: {}", pt.name()))
            .collect();
        p.decls.push(format!(
            "public function {name}({}): {} {{\n  return {body};\n}}",
            list.join(", "),
            t.name()
        ));
        self.fns.push((name, arity, t));
    }

    /// A scalar local, annotated or inferred, printed.
    fn local(&mut self, p: &mut Program) {
        let t = self.scalar();
        let name = self.fresh("v");
        let value = self.expr(t, 3, &[]);
        let line = p.stmt(format!("const {name}: {} = {value};", t.name()));
        p.offer(
            Kind::ChangeType,
            line,
            format!("const {name}: {} = {value};", t.other().name()),
        );
        p.stmt(format!("console.log({name});"));
    }

    /// A nullable integer narrowed before arithmetic.
    fn nullable(&mut self, p: &mut Program) {
        let name = self.fresh("p");
        let cond = self.expr(Scalar::Bool, 1, &[]);
        let value = self.expr(Scalar::I64, 2, &[]);
        p.stmt(format!(
            "const {name}: i64 | null = {cond} ? {value} : null;"
        ));
        p.stmt(format!(
            "if ({name} != null) {{\n  console.log({name} + 1);\n}}"
        ));
    }

    /// A class with written defaults, a named form of it, and a function reading it
    /// through `&`.
    fn class(&mut self, p: &mut Program) {
        let class = self.fresh("C");
        let count = 1 + self.below(3);
        let fields: Vec<(String, Scalar)> = (0..count)
            .map(|i| (format!("f{i}"), self.scalar()))
            .collect();
        let mut decl = format!("public final class {class} {{\n");
        for (name, t) in &fields {
            decl.push_str(&format!(
                "  public {name}: {} = {};\n",
                t.name(),
                t.default_text()
            ));
        }
        decl.push('}');
        p.decls.push(decl);
        let (first, first_ty) = fields[0].clone();
        let reader = self.fresh("read");
        p.decls.push(format!(
            "public function {reader}(c: &{class}): {} {{\n  return c.{first};\n}}",
            first_ty.name()
        ));
        let mut named = Vec::new();
        for (name, t) in &fields {
            if self.below(3) != 0 {
                named.push(format!("{name}: {}", self.literal(*t)));
            }
        }
        let value = self.fresh("o");
        let form = |extra: &str| {
            let mut all = named.clone();
            if !extra.is_empty() {
                all.push(extra.to_owned());
            }
            if all.is_empty() {
                format!("const {value} = new {class} {{}};")
            } else {
                format!("const {value} = new {class} {{ {} }};", all.join(", "))
            }
        };
        let line = p.stmt(form(""));
        p.offer(Kind::AddField, line, form("zz: 1"));
        let call = p.stmt(format!("console.log({reader}(&{value}));"));
        p.offer(
            Kind::DropRef,
            call,
            format!("console.log({reader}({value}));"),
        );
    }

    /// An enum, a value of it, and an exhaustive `match` over it.
    fn matching(&mut self, p: &mut Program) {
        let name = self.fresh("E");
        let count = 2 + self.below(3);
        let cases: Vec<String> = (0..count).map(|i| format!("K{i}")).collect();
        p.decls
            .push(format!("public enum {name} {{ {} }}", cases.join(", ")));
        let subject = self.fresh("e");
        let pick = cases[self.below(count)].clone();
        p.stmt(format!("const {subject}: {name} = {name}.{pick};"));
        let t = [Scalar::I64, Scalar::Str][self.below(2)];
        let arms: Vec<String> = cases
            .iter()
            .map(|case| format!("{name}.{case} => {}", self.literal(t)))
            .collect();
        let result = self.fresh("m");
        let line = p.stmt(format!(
            "const {result} = match ({subject}) {{ {} }};",
            arms.join(", ")
        ));
        let dropped = self.below(count);
        let fewer: Vec<String> = arms
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != dropped)
            .map(|(_, arm)| arm.clone())
            .collect();
        p.offer(
            Kind::DropArm,
            line,
            format!(
                "const {result} = match ({subject}) {{ {} }};",
                fewer.join(", ")
            ),
        );
        p.stmt(format!("console.log({result});"));
    }
}

/// One program from the tape.
fn program(rng: &mut Xoshiro256) -> Program {
    let mut g = Gen {
        rng,
        next: 0,
        fns: Vec::new(),
    };
    let mut p = Program::default();
    for _ in 0..g.below(3) {
        g.function(&mut p);
    }
    for _ in 0..1 + g.below(6) {
        match g.below(4) {
            0 => g.nullable(&mut p),
            1 => g.class(&mut p),
            2 => g.matching(&mut p),
            _ => g.local(&mut p),
        }
    }
    p
}

/// The 1-based line of a span's start in a run.
fn line_of(run: &Run, span: Span) -> usize {
    run.map.loc(span.lo).line as usize
}

/// Checks `text`, failing if phase 2 panics.
fn checked(text: &str) -> Result<Run, String> {
    let mut run = None;
    if let Some(message) = catch_panic(|| {
        run = Some(run_with(
            &[("m.en", text)],
            LibSource::Embedded,
            enrang_target::host_target(),
        ));
    }) {
        return Err(format!("phase 2 panicked: {message}"));
    }
    Ok(run.expect("set when the run returns"))
}

/// A generated program passes, and each of its mutants gives exactly its code at
/// its line.
fn verify(p: &Program) -> Result<usize, String> {
    let text = p.text(None);
    let run = checked(&text)?;
    if !run.diags.is_empty() {
        return Err(format!(
            "the program is rejected:\n{text}\n{}",
            run.rendered()
        ));
    }
    for m in &p.mutations {
        let mutant = p.text(Some(m));
        let run = checked(&mutant)?;
        let codes = run.codes();
        let line = p.line_of_stmt(m.line);
        let at_line = run
            .diags
            .first()
            .is_some_and(|d| line_of(&run, d.primary.span) == line);
        if codes.is_empty() || codes.iter().any(|c| c != m.kind.code()) || !at_line {
            return Err(format!(
                "{:?} at line {line} should give {} there:\n{mutant}\n{}",
                m.kind,
                m.kind.code(),
                run.rendered()
            ));
        }
    }
    Ok(p.mutations.len())
}

pub fn register(h: &mut Harness) {
    h.case(
        "gen_types/generated programs pass and their mutants give their codes",
        || {
            let mut rng = rng_for("sema/gen_types");
            let mut kinds = [0usize; 4];
            for n in 0..scaled(200) {
                let p = program(&mut rng);
                if let Err(message) = verify(&p) {
                    panic!("program {n} of ENRANG_SEED={}: {message}", seed());
                }
                for m in &p.mutations {
                    kinds[m.kind as usize] += 1;
                }
            }
            assert!(
                kinds.iter().all(|&count| count > 0),
                "every mutation kind was made: {kinds:?}"
            );
        },
    );
    h.case("gen_types/a broken program or mutant is caught", || {
        let mut p = Program::default();
        let line = p.stmt("const v: i64 = 1;".to_owned());
        p.stmt("console.log(v);".to_owned());
        assert_eq!(verify(&p), Ok(0));
        p.offer(Kind::ChangeType, line, "const v: string = 1;".to_owned());
        assert_eq!(verify(&p), Ok(1));
        let mut wrong = p.clone();
        wrong.mutations[0].kind = Kind::DropArm;
        assert!(verify(&wrong).is_err(), "the wrong code is caught");
        let mut elsewhere = p.clone();
        elsewhere.mutations[0].text = "const v: i64 = 1;".to_owned();
        assert!(
            verify(&elsewhere).is_err(),
            "a mutant that passes is caught"
        );
        let mut rejected = p.clone();
        rejected.stmts[0] = "const v: i64 = \"s\";".to_owned();
        assert!(verify(&rejected).is_err(), "a rejected program is caught");
    });
}
