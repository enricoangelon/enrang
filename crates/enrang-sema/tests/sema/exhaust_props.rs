//! Maranget against brute force (owner 2D; TESTING 23's M2 row; plan d.13, g.1, g.3).
//!
//! Random columns: a subject type (an enum of 1 to 6 cases, `bool`, an integer, a
//! float, a string or a class, under zero to two levels of `| null`; half of the
//! columns are nullable enums) and a list of arms (cases, `null`, `default`,
//! integer literals and half-open ranges, empty ones included, float and string
//! literals, guards, conditions, duplicates). For each, the engine's verdicts are
//! compared with a direct evaluation over a finite model of the subject's values:
//! each case, `null`, `Present(...)` of each inner value, both booleans, and for
//! numbers and strings every literal and every boundary of every range, the value
//! below it, and one value no arm names. They must agree on whether the `match` is
//! exhaustive and on whether each arm value is reachable; every witness must
//! really be unmatched, the finite witnesses must be exactly the unmatched model
//! values, an arm value's `covered_by` must alone cover it, and adding the arms
//! the help would add must make the `match` exhaustive.
//!
//! `scaled(2_000)` columns run at scale 1 (TESTING 14's tenth of the full volume),
//! and `scaled(300)` more go through the HIR adapter as source text: their EN0501
//! and EN0503 must match the brute force, and applying EN0501's edits to the text
//! must leave a `match` with no EN0501. A disagreement is shrunk with the
//! testkit's shrinker and reported with `ENRANG_SEED` and the shrunk column in the
//! format of `corpus/regress/exhaust/*.txt`, where it then stays as a permanent
//! case (TESTING 14); every file there is run first.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::fs;

use enrang_testkit::{
    Harness, Rng, Shrink, Xoshiro256, rng_for, scaled, seed, shrink_within, workspace_root,
};

use crate::exhaust::build;
use crate::exhaust::engine::matrix::{Pat, Space, float_key};
use crate::exhaust::engine::witness::Witness;
use crate::exhaust::engine::{ArmPat, Guard, analyze};

/// The innermost type of a generated subject.
#[derive(Clone, Debug, PartialEq)]
pub enum Base {
    Enum(u32),
    Bool,
    Int,
    Float,
    Str,
    Opaque,
}

/// One arm value as written: everything but `default`, `null` and a condition
/// wraps in `Present` once per level of `| null`.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Default,
    Null,
    Cond,
    Case(u32),
    Bool(bool),
    Int(i128),
    Range(i128, i128),
    Float(f64),
    Str(String),
}

#[derive(Clone, Debug, PartialEq)]
pub struct InArm {
    pub values: Vec<Value>,
    pub guarded: bool,
}

/// A random column: the subject's type and the arms.
#[derive(Clone, Debug, PartialEq)]
pub struct Column {
    pub base: Base,
    pub depth: u32,
    pub arms: Vec<InArm>,
}

impl Column {
    fn space(&self) -> Space {
        let mut space = match self.base {
            Base::Enum(n) => Space::Enum(n),
            Base::Bool => Space::Bool,
            Base::Int => Space::Int,
            Base::Float => Space::Float,
            Base::Str => Space::Str,
            Base::Opaque => Space::Opaque,
        };
        for _ in 0..self.depth {
            space = Space::Nullable(Box::new(space));
        }
        space
    }

    fn wrap(&self, mut pat: Pat) -> Pat {
        for _ in 0..self.depth {
            pat = Pat::Present(Box::new(pat));
        }
        pat
    }

    /// The arms as the adapter (`lower.rs`) gives them to the engine.
    fn pats(&self) -> Vec<Vec<ArmPat>> {
        self.arms
            .iter()
            .map(|arm| {
                let guard = if arm.guarded { Guard::Arm } else { Guard::None };
                arm.values
                    .iter()
                    .map(|v| match v {
                        Value::Default => ArmPat {
                            pat: Pat::Wild,
                            guard,
                        },
                        Value::Cond => ArmPat {
                            pat: Pat::Wild,
                            guard: Guard::Own,
                        },
                        Value::Null => ArmPat {
                            pat: Pat::Null,
                            guard,
                        },
                        Value::Case(c) => ArmPat {
                            pat: self.wrap(Pat::Case(*c)),
                            guard,
                        },
                        Value::Bool(b) => ArmPat {
                            pat: self.wrap(Pat::Bool(*b)),
                            guard,
                        },
                        Value::Int(n) => ArmPat {
                            pat: self.wrap(Pat::Range(*n, n + 1)),
                            guard,
                        },
                        Value::Range(lo, hi) => ArmPat {
                            pat: self.wrap(Pat::Range(*lo, *hi)),
                            guard,
                        },
                        Value::Float(f) => ArmPat {
                            pat: self.wrap(float_key(*f).map_or(Pat::Empty, Pat::Float)),
                            guard,
                        },
                        Value::Str(s) => ArmPat {
                            pat: self.wrap(Pat::Str(s.clone())),
                            guard,
                        },
                    })
                    .collect()
            })
            .collect()
    }

    /// The column in the format of `corpus/regress/exhaust/*.txt`.
    pub fn to_text(&self) -> String {
        let mut out = String::from("space: ");
        match self.base {
            Base::Enum(n) => write!(out, "enum {n}").unwrap(),
            Base::Bool => out.push_str("bool"),
            Base::Int => out.push_str("int"),
            Base::Float => out.push_str("float"),
            Base::Str => out.push_str("str"),
            Base::Opaque => out.push_str("opaque"),
        }
        for _ in 0..self.depth {
            out.push_str(" | null");
        }
        out.push('\n');
        for arm in &self.arms {
            let values: Vec<String> = arm
                .values
                .iter()
                .map(|v| match v {
                    Value::Default => "default".to_owned(),
                    Value::Null => "null".to_owned(),
                    Value::Cond => "cond".to_owned(),
                    Value::Case(c) => format!("case {c}"),
                    Value::Bool(b) => b.to_string(),
                    Value::Int(n) => format!("int {n}"),
                    Value::Range(lo, hi) => format!("range {lo} {hi}"),
                    Value::Float(f) => format!("float {f:?}"),
                    Value::Str(s) => format!("str \"{s}\""),
                })
                .collect();
            let guard = if arm.guarded { " if" } else { "" };
            writeln!(out, "arm: {}{guard}", values.join(", ")).unwrap();
        }
        out
    }

    /// Reads [`Column::to_text`]'s format; `#` starts a comment line.
    pub fn parse(text: &str) -> Result<Column, String> {
        let mut column: Option<Column> = None;
        for line in text.lines().map(str::trim) {
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            if let Some(space) = line.strip_prefix("space: ") {
                let mut parts = space.split(" | ");
                let base = match parts
                    .next()
                    .unwrap_or("")
                    .split_whitespace()
                    .collect::<Vec<_>>()[..]
                {
                    ["enum", n] => Base::Enum(n.parse().map_err(|_| format!("bad count {n}"))?),
                    ["bool"] => Base::Bool,
                    ["int"] => Base::Int,
                    ["float"] => Base::Float,
                    ["str"] => Base::Str,
                    ["opaque"] => Base::Opaque,
                    _ => return Err(format!("bad space `{space}`")),
                };
                let depth = parts.filter(|p| *p == "null").count() as u32;
                column = Some(Column {
                    base,
                    depth,
                    arms: Vec::new(),
                });
            } else if let Some(arm) = line.strip_prefix("arm: ") {
                let column = column.as_mut().ok_or("an arm before the space")?;
                let (arm, guarded) = match arm.strip_suffix(" if") {
                    Some(arm) => (arm, true),
                    None => (arm, false),
                };
                let values = arm
                    .split(", ")
                    .map(|v| {
                        let words: Vec<&str> = v.split_whitespace().collect();
                        Ok(match words[..] {
                            ["default"] => Value::Default,
                            ["null"] => Value::Null,
                            ["cond"] => Value::Cond,
                            ["true"] => Value::Bool(true),
                            ["false"] => Value::Bool(false),
                            ["case", c] => Value::Case(c.parse().map_err(|_| v.to_owned())?),
                            ["int", n] => Value::Int(n.parse().map_err(|_| v.to_owned())?),
                            ["range", lo, hi] => Value::Range(
                                lo.parse().map_err(|_| v.to_owned())?,
                                hi.parse().map_err(|_| v.to_owned())?,
                            ),
                            ["float", f] => Value::Float(f.parse().map_err(|_| v.to_owned())?),
                            _ => match v.strip_prefix("str \"").and_then(|s| s.strip_suffix('"')) {
                                Some(s) => Value::Str(s.to_owned()),
                                None => return Err(format!("bad value `{v}`")),
                            },
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                column.arms.push(InArm { values, guarded });
            } else {
                return Err(format!("bad line `{line}`"));
            }
        }
        column.ok_or_else(|| "no space line".to_owned())
    }
}

impl Shrink for Column {
    /// Fewer arms, fewer values, no guard, a simpler value, fewer cases or levels.
    fn candidates(&self) -> Box<dyn Iterator<Item = Column> + '_> {
        let mut out = Vec::new();
        for a in 0..self.arms.len() {
            let mut c = self.clone();
            c.arms.remove(a);
            out.push(c);
        }
        for (a, arm) in self.arms.iter().enumerate() {
            if arm.values.len() > 1 {
                for v in 0..arm.values.len() {
                    let mut c = self.clone();
                    c.arms[a].values.remove(v);
                    out.push(c);
                }
            }
            if arm.guarded {
                let mut c = self.clone();
                c.arms[a].guarded = false;
                out.push(c);
            }
            for (v, value) in arm.values.iter().enumerate() {
                let simpler = match value {
                    Value::Range(lo, hi) => Some(Value::Range(lo / 2, hi / 2)),
                    Value::Int(n) => Some(Value::Int(n / 2)),
                    Value::Case(c) if *c > 0 => Some(Value::Case(c - 1)),
                    Value::Str(s) if !s.is_empty() => Some(Value::Str(String::new())),
                    _ => None,
                };
                if let Some(simpler) = simpler.filter(|s| s != value) {
                    let mut c = self.clone();
                    c.arms[a].values[v] = simpler;
                    out.push(c);
                }
            }
        }
        if let Base::Enum(n) = self.base
            && n > 1
            && self
                .arms
                .iter()
                .flat_map(|a| &a.values)
                .all(|v| *v != Value::Case(n - 1))
        {
            let mut c = self.clone();
            c.base = Base::Enum(n - 1);
            out.push(c);
        }
        if self.depth > 0
            && self
                .arms
                .iter()
                .flat_map(|a| &a.values)
                .all(|v| *v != Value::Null)
        {
            let mut c = self.clone();
            c.depth -= 1;
            out.push(c);
        }
        Box::new(out.into_iter())
    }
}

// ---------------------------------------------------------------------------------
// The brute-force model, written apart from the engine.

/// A value of the subject.
#[derive(Clone, Debug, PartialEq)]
enum Val {
    Null,
    Present(Box<Val>),
    Case(u32),
    Bool(bool),
    Int(i128),
    Float(f64),
    Str(String),
    Other,
}

impl Val {
    /// Whether the value is one of a type's finitely many: `null` at any level,
    /// a case, a boolean.
    fn finite(&self) -> bool {
        match self {
            Val::Present(inner) => inner.finite(),
            Val::Null | Val::Case(_) | Val::Bool(_) => true,
            _ => false,
        }
    }
}

/// Whether `pat` matches `v`, by the meaning SPEC 6 gives arm values.
fn eval(pat: &Pat, v: &Val) -> bool {
    match (pat, v) {
        (Pat::Wild, _) => true,
        (Pat::Null, Val::Null) => true,
        (Pat::Present(p), Val::Present(inner)) => eval(p, inner),
        (Pat::Case(a), Val::Case(b)) => a == b,
        (Pat::Bool(a), Val::Bool(b)) => a == b,
        (Pat::Range(lo, hi), Val::Int(n)) => lo <= n && n < hi,
        (Pat::Float(bits), Val::Float(f)) => f64::from_bits(*bits) == *f,
        (Pat::Str(a), Val::Str(b)) => a == b,
        _ => false,
    }
}

/// The patterns at one level: those under exactly `depth` `Present`s.
fn at_depth<'p>(pats: &[&'p Pat], depth: u32) -> Vec<&'p Pat> {
    pats.iter()
        .filter_map(|p| {
            let mut p: &Pat = p;
            for _ in 0..depth {
                match p {
                    Pat::Present(inner) => p = inner,
                    _ => return None,
                }
            }
            Some(p)
        })
        .collect()
}

/// A finite model of the subject's values that every arm value tells apart as
/// the infinite set would.
fn model(space: &Space, pats: &[&Pat], depth: u32) -> Vec<Val> {
    let here = at_depth(pats, depth);
    match space {
        Space::Nullable(inner) => {
            let mut out = vec![Val::Null];
            out.extend(
                model(inner, pats, depth + 1)
                    .into_iter()
                    .map(|v| Val::Present(Box::new(v))),
            );
            out
        }
        Space::Enum(n) => (0..*n).map(Val::Case).collect(),
        Space::Bool => vec![Val::Bool(false), Val::Bool(true)],
        Space::Int => {
            let mut points = BTreeSet::from([0i128]);
            for p in &here {
                if let Pat::Range(lo, hi) = p {
                    for end in [*lo, *hi] {
                        points.insert(end);
                        points.insert(end - 1);
                    }
                }
            }
            points.into_iter().map(Val::Int).collect()
        }
        Space::Float => {
            let mut values: Vec<f64> = here
                .iter()
                .filter_map(|p| match p {
                    Pat::Float(bits) => Some(f64::from_bits(*bits)),
                    _ => None,
                })
                .collect();
            let mut fresh = 0.25;
            while values.contains(&fresh) {
                fresh += 1.0;
            }
            values.push(fresh);
            values.into_iter().map(Val::Float).collect()
        }
        Space::Str => {
            let mut values: Vec<String> = here
                .iter()
                .filter_map(|p| match p {
                    Pat::Str(s) => Some(s.clone()),
                    _ => None,
                })
                .collect();
            let mut fresh = String::from("fresh");
            while values.contains(&fresh) {
                fresh.push('!');
            }
            values.push(fresh);
            values.into_iter().map(Val::Str).collect()
        }
        Space::Opaque => vec![Val::Other],
    }
}

/// The brute-force verdicts.
struct Brute {
    model: Vec<Val>,
    reachable: Vec<Vec<bool>>,
    unmatched: Vec<Val>,
}

/// Whether value `v` of arm `a` is shadowed for `x` by a value above it: an
/// unguarded value of an earlier arm, or an earlier value of its own arm that
/// has no condition of its own (an arm's guard is shared by its values).
fn shadowed(pats: &[Vec<ArmPat>], a: usize, v: usize, x: &Val) -> bool {
    pats[..a]
        .iter()
        .flatten()
        .any(|p| p.guard == Guard::None && eval(&p.pat, x))
        || pats[a][..v]
            .iter()
            .any(|p| p.guard != Guard::Own && eval(&p.pat, x))
}

fn brute(space: &Space, pats: &[Vec<ArmPat>]) -> Brute {
    let all: Vec<&Pat> = pats.iter().flatten().map(|p| &p.pat).collect();
    let model = model(space, &all, 0);
    let reachable = pats
        .iter()
        .enumerate()
        .map(|(a, arm)| {
            (0..arm.len())
                .map(|v| {
                    model
                        .iter()
                        .any(|x| eval(&arm[v].pat, x) && !shadowed(pats, a, v, x))
                })
                .collect()
        })
        .collect();
    let unmatched = model
        .iter()
        .filter(|x| {
            !pats
                .iter()
                .flatten()
                .any(|p| p.guard == Guard::None && eval(&p.pat, x))
        })
        .cloned()
        .collect();
    Brute {
        model,
        reachable,
        unmatched,
    }
}

fn val_of(w: &Witness) -> Val {
    match w {
        Witness::Null => Val::Null,
        Witness::Present(inner) => Val::Present(Box::new(val_of(inner))),
        Witness::Case(c) => Val::Case(*c),
        Witness::Bool(b) => Val::Bool(*b),
        Witness::Int(n) => Val::Int(*n),
        Witness::Float(bits) => Val::Float(f64::from_bits(*bits)),
        Witness::Str(s) => Val::Str(s.clone()),
        Witness::Other => Val::Other,
    }
}

/// The arm the help adds for a witness: the value itself when an arm can name
/// it, `default` otherwise (an inner `null`, numbers, strings, other types).
fn fix_arm(w: &Witness) -> Pat {
    match w {
        Witness::Null => Pat::Null,
        Witness::Present(inner) => match fix_arm(inner) {
            Pat::Wild | Pat::Null => Pat::Wild,
            p => Pat::Present(Box::new(p)),
        },
        Witness::Case(c) => Pat::Case(*c),
        Witness::Bool(b) => Pat::Bool(*b),
        _ => Pat::Wild,
    }
}

/// Every disagreement between the engine and the brute force on `column`.
pub fn disagreements(column: &Column) -> Vec<String> {
    let space = column.space();
    let pats = column.pats();
    let engine = analyze(&space, &pats);
    let truth = brute(&space, &pats);
    let mut out = Vec::new();
    for (a, arm) in pats.iter().enumerate() {
        for v in 0..arm.len() {
            let verdict = engine.values[a][v];
            if verdict.reachable != truth.reachable[a][v] {
                out.push(format!(
                    "arm {a} value {v}: engine says reachable={}, brute force {}",
                    verdict.reachable, truth.reachable[a][v]
                ));
            }
            if let Some((ca, cv)) = verdict.covered_by {
                let cover = &pats[ca][cv];
                let above = ca < a && cover.guard == Guard::None
                    || ca == a && cv < v && cover.guard != Guard::Own;
                let covers = truth
                    .model
                    .iter()
                    .all(|x| !eval(&arm[v].pat, x) || eval(&cover.pat, x));
                if !above || !covers || verdict.reachable {
                    out.push(format!(
                        "arm {a} value {v}: covered_by ({ca}, {cv}) is wrong"
                    ));
                }
            }
            let matches_some = truth.model.iter().any(|x| eval(&arm[v].pat, x));
            if verdict.covered_by.is_some() && !matches_some {
                out.push(format!(
                    "arm {a} value {v} matches nothing, yet has a covered_by"
                ));
            }
            if verdict.covered_by.is_none() && !verdict.reachable && matches_some {
                let single = (0..=a)
                    .flat_map(|ca| (0..pats[ca].len()).map(move |cv| (ca, cv)))
                    .find(|&(ca, cv)| {
                        let cover = &pats[ca][cv];
                        let above = ca < a && cover.guard == Guard::None
                            || ca == a && cv < v && cover.guard != Guard::Own;
                        above
                            && truth
                                .model
                                .iter()
                                .all(|x| !eval(&arm[v].pat, x) || eval(&cover.pat, x))
                    });
                if let Some(found) = single {
                    out.push(format!(
                        "arm {a} value {v}: no covered_by, but {found:?} alone covers it"
                    ));
                }
            }
        }
    }
    if engine.missing.is_empty() != truth.unmatched.is_empty() {
        out.push(format!(
            "exhaustive: engine {}, brute force {} (unmatched {:?})",
            engine.missing.is_empty(),
            truth.unmatched.is_empty(),
            truth.unmatched
        ));
    }
    let unguarded: Vec<&Pat> = pats
        .iter()
        .flatten()
        .filter(|p| p.guard == Guard::None)
        .map(|p| &p.pat)
        .collect();
    let witnesses: Vec<Val> = engine.missing.iter().map(val_of).collect();
    for w in &witnesses {
        if unguarded.iter().any(|p| eval(p, w)) {
            out.push(format!("witness {w:?} is matched"));
        }
    }
    let engine_finite: Vec<&Val> = witnesses.iter().filter(|w| w.finite()).collect();
    let model_finite: Vec<&Val> = truth.unmatched.iter().filter(|w| w.finite()).collect();
    let same = engine_finite.len() == model_finite.len()
        && engine_finite.iter().all(|w| model_finite.contains(w));
    if !same {
        out.push(format!(
            "finite witnesses: engine {engine_finite:?}, brute force {model_finite:?}"
        ));
    }
    let engine_infinite = witnesses.iter().filter(|w| !w.finite()).count();
    let model_infinite = truth.unmatched.iter().any(|w| !w.finite());
    if engine_infinite != usize::from(model_infinite) {
        out.push(format!(
            "infinite witnesses: engine {engine_infinite}, brute force has some: {model_infinite}"
        ));
    }
    // Cases in declaration order; at each level, present values before `null`.
    let cases: Vec<u32> = engine
        .missing
        .iter()
        .filter_map(|w| match w.peel().0 {
            Witness::Case(c) => Some(*c),
            _ => None,
        })
        .collect();
    if cases.windows(2).any(|p| p[0] >= p[1]) {
        out.push(format!("cases out of order: {cases:?}"));
    }
    let depths: Vec<usize> = engine
        .missing
        .iter()
        .filter(|w| matches!(w.peel().0, Witness::Null))
        .map(|w| w.peel().1)
        .collect();
    if depths.windows(2).any(|p| p[0] <= p[1]) {
        out.push(format!("nulls not innermost first: {depths:?}"));
    }
    // The help's arms make the `match` exhaustive.
    let mut fixed = pats.clone();
    for w in &engine.missing {
        fixed.push(vec![ArmPat {
            pat: fix_arm(w),
            guard: Guard::None,
        }]);
    }
    if !analyze(&space, &fixed).missing.is_empty() {
        out.push("the help's arms leave values missing".to_owned());
    }
    out
}

// ---------------------------------------------------------------------------------
// Generation.

const STRS: &[&str] = &["", "a", "b", "ab", "é"];
const FLOATS: &[f64] = &[0.0, -0.0, 1.5, -2.0, 1e300];

fn gen_value(rng: &mut Xoshiro256, base: &Base, depth: u32) -> Value {
    if depth > 0 && rng.below(5) == 0 {
        return Value::Null;
    }
    if rng.below(24) == 0 {
        return Value::Cond;
    }
    match base {
        Base::Enum(n) => Value::Case(rng.below(u64::from(*n)) as u32),
        Base::Bool => Value::Bool(rng.below(2) == 0),
        Base::Int => {
            let small = |rng: &mut Xoshiro256| rng.below(17) as i128 - 6;
            if rng.below(2) == 0 {
                Value::Int(small(rng))
            } else {
                let lo = small(rng);
                let hi = if rng.below(6) == 0 {
                    lo - rng.below(3) as i128
                } else {
                    lo + 1 + rng.below(8) as i128
                };
                Value::Range(lo, hi)
            }
        }
        Base::Float => match rng.below(10) {
            0 => Value::Float(f64::NAN),
            i => Value::Float(FLOATS[i as usize % FLOATS.len()]),
        },
        Base::Str => Value::Str(STRS[rng.below(STRS.len() as u64) as usize].to_owned()),
        Base::Opaque if depth > 0 => Value::Null,
        Base::Opaque => Value::Default,
    }
}

fn gen_arms(rng: &mut Xoshiro256, base: &Base, depth: u32) -> Vec<InArm> {
    let count = rng.below(8);
    (0..count)
        .map(|_| {
            let guarded = rng.below(4) == 0;
            if rng.below(8) == 0 {
                return InArm {
                    values: vec![Value::Default],
                    guarded,
                };
            }
            let n = 1 + rng.below(3);
            let mut values: Vec<Value> = (0..n).map(|_| gen_value(rng, base, depth)).collect();
            if values.contains(&Value::Default) {
                values = vec![Value::Default];
            }
            InArm { values, guarded }
        })
        .collect()
}

/// A random column; when `nullable_enum`, a nullable enum.
pub fn gen_column(rng: &mut Xoshiro256, nullable_enum: bool) -> Column {
    let (base, depth) = if nullable_enum {
        let depth = if rng.below(4) == 0 { 2 } else { 1 };
        (Base::Enum(1 + rng.below(6) as u32), depth)
    } else {
        let base = match rng.below(6) {
            0 => Base::Enum(1 + rng.below(6) as u32),
            1 => Base::Bool,
            2 => Base::Int,
            3 => Base::Float,
            4 => Base::Str,
            _ => Base::Opaque,
        };
        let depth = match rng.below(6) {
            0..=2 => 0,
            3 | 4 => 1,
            _ => 2,
        };
        (base, depth)
    };
    let arms = gen_arms(rng, &base, depth);
    Column { base, depth, arms }
}

/// The shrunk failure of `column`, in the regression format, with the seed.
fn report(
    label: &str,
    index: usize,
    column: Column,
    check: impl Fn(&Column) -> Vec<String>,
) -> String {
    let shrunk = shrink_within(column, 5_000, |c| !check(c).is_empty());
    format!(
        "{label}: column {index} disagrees (ENRANG_SEED={}); shrunk, to keep as corpus/regress/exhaust/<name>.txt:\n# seed {}, {label} column {index}\n{}{}",
        seed(),
        seed(),
        shrunk.to_text(),
        check(&shrunk).join("\n")
    )
}

/// `corpus/regress/exhaust/*.txt`, by name; none until a disagreement is kept.
fn regressions() -> Vec<(String, String)> {
    let dir = workspace_root().join("corpus/regress/exhaust");
    let Ok(entries) = fs::read_dir(&dir) else {
        return Vec::new();
    };
    let mut found: Vec<(String, String)> = entries
        .map(|e| e.expect("a directory entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "txt"))
        .map(|p| {
            let name = p
                .file_name()
                .and_then(|n| n.to_str())
                .expect("a name")
                .to_owned();
            (name, fs::read_to_string(&p).expect("a regression case"))
        })
        .collect();
    found.sort();
    found
}

// ---------------------------------------------------------------------------------
// The same columns through the HIR adapter, as source text.

/// Names of the cases of `E1`..`E6`.
const CASES: &[&str] = &["A", "B", "C", "D", "E", "F"];

/// The declarations every adapter column's program starts with.
fn prelude() -> String {
    let mut out = String::new();
    for n in 1..=6 {
        writeln!(out, "public enum E{n} {{ {} }}", CASES[..n].join(", ")).unwrap();
    }
    out.push_str("public final class C { }\n");
    out
}

/// A column the adapter can be given as source: no NaN (no literal writes it),
/// no condition (only under `match (true)`), non-negative range ends.
fn writable(column: &Column) -> bool {
    column.arms.iter().flat_map(|a| &a.values).all(|v| match v {
        Value::Cond => false,
        Value::Float(f) => !f.is_nan() && f.abs() < 1e10,
        Value::Range(lo, hi) => *lo >= 0 && *hi >= 0,
        _ => true,
    })
}

/// The program of `column` in one of three layouts: one arm per line with a
/// comma after each; the subject behind `&` and no comma after the last arm; or
/// the whole `match` on one line.
fn program(column: &Column, layout: u64) -> String {
    let mut ty = match column.base {
        Base::Enum(n) => format!("E{n}"),
        Base::Bool => "bool".to_owned(),
        Base::Int => "i64".to_owned(),
        Base::Float => "f64".to_owned(),
        Base::Str => "string".to_owned(),
        Base::Opaque => "C".to_owned(),
    };
    if layout == 1 {
        ty = format!("&{ty}");
    }
    for level in 0..column.depth {
        ty = if level == 0 {
            format!("{ty} | null")
        } else {
            format!("({ty}) | null")
        };
    }
    let arms: Vec<String> = column
        .arms
        .iter()
        .map(|arm| {
            let values: Vec<String> = arm
                .values
                .iter()
                .map(|v| match v {
                    Value::Default => "default".to_owned(),
                    Value::Null => "null".to_owned(),
                    Value::Cond => unreachable!("not writable"),
                    Value::Case(c) => match column.base {
                        Base::Enum(n) => format!("E{n}.{}", CASES[*c as usize]),
                        _ => unreachable!("a case of an enum"),
                    },
                    Value::Bool(b) => b.to_string(),
                    Value::Int(n) => n.to_string(),
                    Value::Range(lo, hi) => format!("{lo}..{hi}"),
                    Value::Float(f) => format!("{f:?}"),
                    Value::Str(s) => format!("\"{s}\""),
                })
                .collect();
            let guard = if arm.guarded { " if g" } else { "" };
            format!("{}{guard} => 1", values.join(", "))
        })
        .collect();
    let body = match layout {
        0 => format!(
            "match (s) {{\n{}  }}",
            arms.iter()
                .map(|a| format!("    {a},\n"))
                .collect::<String>()
        ),
        1 => format!("match (s) {{\n    {}\n  }}", arms.join(",\n    ")),
        _ => format!("match (s) {{ {} }}", arms.join(", ")),
    };
    format!(
        "{}public function f(s: {ty}, g: bool): i64 {{\n  return {body};\n}}\n",
        prelude()
    )
}

/// Every disagreement between the adapter's diagnostics on `column`'s program
/// and the brute force.
fn adapter_disagreements(column: &Column, layout: u64) -> Vec<String> {
    let text = program(column, layout);
    let built = build("src/main.en", &text);
    let diags = built.diags();
    let space = column.space();
    let pats = column.pats();
    let truth = brute(&space, &pats);
    let mut out = Vec::new();
    let en0501 = diags.iter().filter(|d| d.code.name() == "EN0501").count();
    if en0501 != usize::from(!truth.unmatched.is_empty()) {
        out.push(format!(
            "{en0501} EN0501, brute force unmatched {:?}",
            truth.unmatched
        ));
    }
    let mut expected = Vec::new();
    for (a, arm) in built.arms().iter().enumerate() {
        let reach = &truth.reachable[a];
        let span = |v: usize| arm.value_spans.get(v).copied().unwrap_or(arm.span);
        if reach.iter().all(|r| !r) {
            expected.push(if arm.values.is_empty() {
                built.span(
                    "default",
                    column.arms[..a]
                        .iter()
                        .filter(|x| x.values == [Value::Default])
                        .count(),
                )
            } else {
                span(0)
            });
        } else {
            for (v, r) in reach.iter().enumerate() {
                if !r {
                    expected.push(span(v));
                }
            }
        }
    }
    let actual: Vec<_> = diags
        .iter()
        .filter(|d| d.code.name() == "EN0503")
        .map(|d| d.primary.span)
        .collect();
    if actual != expected {
        out.push(format!("EN0503 at {actual:?}, expected {expected:?}"));
    }
    if en0501 == 1 {
        let fixed = built.fixed(&diags);
        let again = build("src/main.en", &fixed);
        if again.diags().iter().any(|d| d.code.name() == "EN0501") {
            out.push(format!("EN0501 after its fix:\n{fixed}"));
        }
    }
    if !out.is_empty() {
        out.push(text);
    }
    out
}

pub fn register(h: &mut Harness) {
    for (name, text) in regressions() {
        h.case(format!("exhaust_props/regress/{name}"), move || {
            let column = Column::parse(&text)?;
            let found = disagreements(&column);
            if found.is_empty() {
                Ok(())
            } else {
                Err(found.join("\n"))
            }
        });
    }
    h.case(
        "exhaust_props/a pattern matches the values it names",
        || {
            use crate::exhaust::engine::witness::matches;
            let present = |w: Witness| Witness::Present(Box::new(w));
            let yes = [
                (Pat::Range(-2, 3), Witness::Int(-2)),
                (Pat::Range(-2, 3), Witness::Int(2)),
                (
                    Pat::Float(0.0f64.to_bits()),
                    Witness::Float((-0.0f64).to_bits()),
                ),
                (Pat::Str("a".to_owned()), Witness::Str("a".to_owned())),
                (
                    Pat::Present(Box::new(Pat::Case(1))),
                    present(Witness::Case(1)),
                ),
                (Pat::Wild, present(Witness::Null)),
                (Pat::Null, Witness::Null),
                (Pat::Bool(false), Witness::Bool(false)),
            ];
            let no = [
                (Pat::Range(-2, 3), Witness::Int(3)),
                (Pat::Range(-2, 3), Witness::Int(-3)),
                (Pat::Range(3, 3), Witness::Int(3)),
                (
                    Pat::Float(1.5f64.to_bits()),
                    Witness::Float(2.5f64.to_bits()),
                ),
                (Pat::Str("a".to_owned()), Witness::Str("b".to_owned())),
                (Pat::Null, present(Witness::Null)),
                (
                    Pat::Present(Box::new(Pat::Case(1))),
                    present(Witness::Case(0)),
                ),
                (Pat::Empty, Witness::Other),
                (Pat::Case(0), Witness::Other),
            ];
            for (p, w) in &yes {
                assert!(matches(p, w), "{p:?} should match {w:?}");
            }
            for (p, w) in &no {
                assert!(!matches(p, w), "{p:?} should not match {w:?}");
            }
        },
    );
    h.case("exhaust_props/the regression format reads back", || {
        let mut rng = rng_for("exhaust_props/format");
        for i in 0..200 {
            let column = gen_column(&mut rng, i % 2 == 0);
            let text = column.to_text();
            let back = Column::parse(&text).map_err(|e| format!("{e}\n{text}"))?;
            if back.to_text() != text {
                return Err(format!("{text}\nreads back as\n{}", back.to_text()));
            }
        }
        Ok::<(), String>(())
    });
    h.case("exhaust_props/Maranget agrees with brute force", || {
        let mut rng = rng_for("exhaust_props/columns");
        let total = scaled(2_000);
        let mut nullable_enums = 0;
        let mut exhaustive = 0;
        let mut unreachable = 0;
        for i in 0..total {
            let column = gen_column(&mut rng, i % 2 == 0);
            if matches!(column.base, Base::Enum(_)) && column.depth > 0 {
                nullable_enums += 1;
            }
            let found = disagreements(&column);
            if !found.is_empty() {
                return Err(report("engine", i, column, disagreements));
            }
            let space = column.space();
            let analysis = analyze(&space, &column.pats());
            exhaustive += usize::from(analysis.missing.is_empty());
            unreachable += usize::from(analysis.values.iter().flatten().any(|v| !v.reachable));
        }
        // The generator reaches both verdicts often, and half its columns are
        // nullable enums (plan g.3).
        if nullable_enums * 2 < total || exhaustive * 10 < total || unreachable * 10 < total {
            return Err(format!(
                "{total} columns: {nullable_enums} nullable enums, {exhaustive} exhaustive, {unreachable} with an unreachable value"
            ));
        }
        Ok(())
    });
    h.case(
        "exhaust_props/the adapter agrees with brute force on source",
        || {
            let mut rng = rng_for("exhaust_props/adapter");
            let total = scaled(300);
            let mut done = 0;
            let mut i = 0;
            while done < total {
                let column = gen_column(&mut rng, i % 2 == 0);
                i += 1;
                if !writable(&column) {
                    continue;
                }
                let layout = rng.below(3);
                let found = adapter_disagreements(&column, layout);
                if !found.is_empty() {
                    return Err(report("adapter", i, column, |c| {
                        if writable(c) {
                            adapter_disagreements(c, layout)
                        } else {
                            Vec::new()
                        }
                    }));
                }
                done += 1;
            }
            Ok::<(), String>(())
        },
    );
    h.case("exhaust_props/a planted disagreement is found and shrunk", || {
        // A mutant engine that lets guarded arms cover their values, a plausible
        // bug: the check must see it disagree with the brute force, and shrink
        // the column to a small one that still shows it.
        let mutant = |c: &Column| -> Vec<String> {
            let space = c.space();
            let pats = c.pats();
            let unguarded: Vec<Vec<ArmPat>> = pats
                .iter()
                .map(|arm| {
                    arm.iter()
                        .map(|p| ArmPat {
                            pat: p.pat.clone(),
                            guard: match p.guard {
                                Guard::Arm => Guard::None,
                                g => g,
                            },
                        })
                        .collect()
                })
                .collect();
            let engine = analyze(&space, &unguarded);
            let truth = brute(&space, &pats);
            if engine.missing.is_empty() == truth.unmatched.is_empty() {
                Vec::new()
            } else {
                vec!["exhaustiveness differs".to_owned()]
            }
        };
        let column = Column::parse(
            "# planted\nspace: enum 3 | null\narm: case 0, case 1\narm: case 2, case 0 if\narm: null\narm: default if\n",
        )
        .expect("parses");
        assert!(disagreements(&column).is_empty(), "the real engine agrees");
        assert!(!mutant(&column).is_empty(), "the mutant does not");
        let text = report("planted", 0, column, mutant);
        let shrunk = text
            .lines()
            .filter(|l| l.starts_with("arm: "))
            .collect::<Vec<_>>();
        assert!(shrunk.iter().any(|l| l.ends_with(" if")), "{text}");
        assert!(shrunk.len() <= 2, "{text}");
        assert!(text.contains("ENRANG_SEED="), "{text}");
    });
}
