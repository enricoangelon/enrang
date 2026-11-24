//! Generated types (TESTING 14): seeded by `ENRANG_SEED` through `rng_for`, scaled
//! by `ENRANG_SCALE`, shrunk on failure and reported with the seed. Each type is a
//! tree of SPEC-valid forms (primitives, descriptors, pointers and the two-word
//! forms, fixed arrays, nullables, tuples, anonymous objects, classes with and
//! without a base, `@packed` and `@align`, enums with and without payloads and
//! `@repr`), built through `Tcx::define_*`. Every node is checked against an
//! independent model of SPEC 11 written here, and against what holds of any
//! layout: power-of-two alignments that divide the size, fields aligned, inside
//! the value and not overlapping, a subclass's prefix, objects and tuples sorted by
//! alignment, and a cached layout equal to a fresh one.

use enrang_base::intern;
use enrang_hir::{Attrs, ClassModifier, Repr, Ty};
use enrang_layout::{Layout, LayoutCx};
use enrang_testkit::{Harness, Rng, Shrink, Xoshiro256, rng_for, scaled, seed, shrink};

use crate::support::{Case, TARGETS, World};

const PRIMS: [&str; 14] = [
    "bool", "i8", "u8", "i16", "u16", "i32", "u32", "f32", "i64", "u64", "f64", "isize", "usize",
    "void",
];

/// Spellings with no generated part: descriptors, one-word pointers, two-word forms.
const WORDS: [&str; 6] = [
    "string",
    "u8[]",
    "Box<u8>",
    "*u8",
    "fn(i64) => void",
    "Box<Speaker>",
];

/// References, which only a slot may hold: at the top, or under a top `| null`.
const REFS: [&str; 3] = ["&u8", "&Slice<u8>", "&Speaker"];

const NAMES: [&str; 7] = ["a", "b", "c", "Z", "aa", "count", "_x"];

/// A generated type.
#[derive(Clone, Debug)]
enum Node {
    Prim(&'static str),
    Word(&'static str),
    Fixed(Box<Node>, u64),
    Nullable(Box<Node>),
    Tuple(Vec<Node>),
    Object(Vec<(&'static str, Node)>),
    Class(Box<ClassNode>),
    Enum {
        repr: Option<Repr>,
        cases: Vec<Vec<Node>>,
    },
}

#[derive(Clone, Debug)]
struct ClassNode {
    final_: bool,
    packed: bool,
    align: Option<u32>,
    /// A class that is not `final`.
    base: Option<Box<ClassNode>>,
    fields: Vec<Node>,
}

fn gen_node(rng: &mut Xoshiro256, depth: u32, refs: bool) -> Node {
    let leaf = depth == 0 || rng.below(3) == 0;
    if leaf {
        return match rng.below(if refs { 6 } else { 5 }) {
            0..=2 => Node::Prim(PRIMS[rng.below(PRIMS.len() as u64) as usize]),
            3 | 4 => Node::Word(WORDS[rng.below(WORDS.len() as u64) as usize]),
            _ => Node::Word(REFS[rng.below(REFS.len() as u64) as usize]),
        };
    }
    match rng.below(6) {
        0 => Node::Fixed(Box::new(gen_node(rng, depth - 1, false)), rng.below(5)),
        // A nullable reference, `&I | null` among them, is the one place a slot form
        // sits inside another type: make it common.
        1 if refs && rng.below(2) == 0 => Node::Nullable(Box::new(Node::Word(
            REFS[rng.below(REFS.len() as u64) as usize],
        ))),
        1 => Node::Nullable(Box::new(gen_node(rng, depth - 1, refs))),
        2 => Node::Tuple(
            (0..rng.below(5))
                .map(|_| gen_node(rng, depth - 1, false))
                .collect(),
        ),
        3 => {
            let mut fields = Vec::new();
            for name in NAMES {
                if rng.below(3) == 0 {
                    fields.push((name, gen_node(rng, depth - 1, false)));
                }
            }
            Node::Object(fields)
        }
        4 => Node::Class(Box::new(gen_class(rng, depth - 1))),
        _ => {
            let cases: Vec<Vec<Node>> = (0..rng.below(5))
                .map(|_| {
                    let fields = if rng.below(2) == 0 { 0 } else { rng.below(4) };
                    (0..fields)
                        .map(|_| gen_node(rng, depth - 1, false))
                        .collect()
                })
                .collect();
            let repr = match rng.below(5) {
                0 => Some(Repr::U8),
                1 => Some(Repr::U16),
                2 => Some(Repr::U32),
                _ => None,
            };
            Node::Enum { repr, cases }
        }
    }
}

fn gen_class(rng: &mut Xoshiro256, depth: u32) -> ClassNode {
    let base = if depth > 0 && rng.below(3) == 0 {
        let mut base = gen_class(rng, depth - 1);
        base.final_ = false;
        base.packed = false;
        base.align = None;
        Some(Box::new(base))
    } else {
        None
    };
    let final_ = rng.below(2) == 0;
    // The layout decorators need a `final` class with no base (EN0827).
    let decorated = final_ && base.is_none();
    let packed = decorated && rng.below(3) == 0;
    let align = (decorated && rng.below(3) == 0).then(|| 1 << rng.below(7));
    let fields = (0..rng.below(5))
        .map(|_| gen_node(rng, depth, false))
        .collect();
    ClassNode {
        final_,
        packed,
        align,
        base,
        fields,
    }
}

impl Shrink for Node {
    fn candidates(&self) -> Box<dyn Iterator<Item = Node> + '_> {
        let mut out: Vec<Node> = Vec::new();
        if !matches!(self, Node::Prim("u8")) {
            out.push(Node::Prim("u8"));
        }
        match self {
            Node::Prim(_) | Node::Word(_) => {}
            Node::Fixed(inner, n) => {
                out.push((**inner).clone());
                if *n > 0 {
                    out.push(Node::Fixed(inner.clone(), n - 1));
                }
                out.extend(inner.candidates().map(|c| Node::Fixed(Box::new(c), *n)));
            }
            Node::Nullable(inner) => {
                out.push((**inner).clone());
                out.extend(inner.candidates().map(|c| Node::Nullable(Box::new(c))));
            }
            Node::Tuple(parts) => {
                out.extend(parts.iter().cloned());
                for i in 0..parts.len() {
                    let mut fewer = parts.clone();
                    fewer.remove(i);
                    out.push(Node::Tuple(fewer));
                    for c in parts[i].candidates() {
                        let mut simpler = parts.clone();
                        simpler[i] = c;
                        out.push(Node::Tuple(simpler));
                    }
                }
            }
            Node::Object(fields) => {
                out.extend(fields.iter().map(|(_, n)| n.clone()));
                for i in 0..fields.len() {
                    let mut fewer = fields.clone();
                    fewer.remove(i);
                    out.push(Node::Object(fewer));
                    for c in fields[i].1.candidates() {
                        let mut simpler = fields.clone();
                        simpler[i].1 = c;
                        out.push(Node::Object(simpler));
                    }
                }
            }
            Node::Class(class) => {
                out.extend(class.fields.iter().cloned());
                if let Some(base) = &class.base {
                    out.push(Node::Class(base.clone()));
                    out.push(Node::Class(Box::new(ClassNode {
                        base: None,
                        ..(**class).clone()
                    })));
                }
                for flag in [class.packed, class.align.is_some()] {
                    if flag {
                        out.push(Node::Class(Box::new(ClassNode {
                            packed: false,
                            align: None,
                            ..(**class).clone()
                        })));
                    }
                }
                for i in 0..class.fields.len() {
                    let mut fewer = (**class).clone();
                    fewer.fields.remove(i);
                    out.push(Node::Class(Box::new(fewer)));
                    for c in class.fields[i].candidates() {
                        let mut simpler = (**class).clone();
                        simpler.fields[i] = c;
                        out.push(Node::Class(Box::new(simpler)));
                    }
                }
            }
            Node::Enum { repr, cases } => {
                out.extend(cases.iter().flatten().cloned());
                if repr.is_some() {
                    out.push(Node::Enum {
                        repr: None,
                        cases: cases.clone(),
                    });
                }
                for i in 0..cases.len() {
                    let mut fewer = cases.clone();
                    fewer.remove(i);
                    out.push(Node::Enum {
                        repr: *repr,
                        cases: fewer,
                    });
                    for j in 0..cases[i].len() {
                        let mut fewer = cases.clone();
                        fewer[i].remove(j);
                        out.push(Node::Enum {
                            repr: *repr,
                            cases: fewer,
                        });
                    }
                }
            }
        }
        Box::new(out.into_iter())
    }
}

/// What the model says of a node.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Model {
    size: u64,
    align: u64,
    /// The offsets of an aggregate's fields, in `Layout::fields` order.
    fields: Vec<u64>,
    /// The payload offset of a sum type.
    payload: Option<u64>,
}

fn up(x: u64, a: u64) -> u64 {
    x.div_ceil(a) * a
}

/// SPEC 11, written again from the text, independently of the library.
struct Spec11 {
    p: u64,
    i64_align: u64,
}

impl Spec11 {
    fn scalar(size: u64, align: u64) -> Model {
        Model {
            size,
            align,
            fields: Vec::new(),
            payload: None,
        }
    }

    fn model(&self, node: &Node) -> Model {
        let p = self.p;
        match node {
            Node::Prim(name) => match *name {
                "bool" | "i8" | "u8" => Spec11::scalar(1, 1),
                "i16" | "u16" => Spec11::scalar(2, 2),
                "i32" | "u32" | "f32" => Spec11::scalar(4, 4),
                "i64" | "u64" | "f64" => Spec11::scalar(8, self.i64_align),
                "isize" | "usize" => Spec11::scalar(p, p),
                "void" => Spec11::scalar(0, 1),
                other => panic!("no primitive {other}"),
            },
            Node::Word(word) => match *word {
                "string" | "u8[]" => Model {
                    size: 3 * p,
                    align: p,
                    fields: vec![0, p, 2 * p],
                    payload: None,
                },
                "Box<Speaker>" | "&Slice<u8>" | "&Speaker" => Model {
                    size: 2 * p,
                    align: p,
                    fields: vec![0, p],
                    payload: None,
                },
                _ => Spec11::scalar(p, p),
            },
            Node::Fixed(inner, n) => {
                let inner = self.model(inner);
                Spec11::scalar(inner.size * n, inner.align)
            }
            Node::Nullable(inner) => {
                if matches!(**inner, Node::Word("&Speaker")) {
                    return Model {
                        size: 2 * p,
                        align: p,
                        fields: Vec::new(),
                        payload: Some(0),
                    };
                }
                let inner = self.model(inner);
                let payload = up(4, inner.align);
                let align = inner.align.max(4);
                Model {
                    size: up(payload + inner.size, align),
                    align,
                    fields: Vec::new(),
                    payload: Some(payload),
                }
            }
            Node::Tuple(parts) => {
                let models: Vec<Model> = parts.iter().map(|n| self.model(n)).collect();
                let mut order: Vec<usize> = (0..models.len()).collect();
                order.sort_by_key(|&i| (std::cmp::Reverse(models[i].align), i));
                Spec11::by_order(&models, &order)
            }
            Node::Object(fields) => {
                let mut fields: Vec<&(&str, Node)> = fields.iter().collect();
                fields.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
                let models: Vec<Model> = fields.iter().map(|(_, n)| self.model(n)).collect();
                let mut order: Vec<usize> = (0..models.len()).collect();
                order
                    .sort_by_key(|&i| (std::cmp::Reverse(models[i].align), fields[i].0.as_bytes()));
                Spec11::by_order(&models, &order)
            }
            Node::Class(class) => self.class(class),
            Node::Enum { repr, cases } => {
                let models: Vec<Vec<Model>> = cases
                    .iter()
                    .map(|case| case.iter().map(|n| self.model(n)).collect())
                    .collect();
                let payload_free = cases.iter().all(Vec::is_empty);
                let tag = match (payload_free, repr) {
                    (true, Some(Repr::U8)) => 1,
                    (true, Some(Repr::U16)) => 2,
                    _ => 4,
                };
                let case_align = models.iter().flatten().map(|m| m.align).max().unwrap_or(1);
                let payload = up(tag, case_align);
                let align = tag.max(case_align);
                let mut end = payload;
                for case in &models {
                    let mut at = payload;
                    for field in case {
                        at = up(at, field.align) + field.size;
                    }
                    end = end.max(at);
                }
                Model {
                    size: up(end, align),
                    align,
                    fields: Vec::new(),
                    payload: Some(payload),
                }
            }
        }
    }

    fn by_order(models: &[Model], order: &[usize]) -> Model {
        let mut fields = vec![0; models.len()];
        let (mut at, mut align) = (0, 1);
        for &i in order {
            at = up(at, models[i].align);
            fields[i] = at;
            at += models[i].size;
            align = align.max(models[i].align);
        }
        Model {
            size: up(at, align),
            align,
            fields,
            payload: None,
        }
    }

    fn class(&self, class: &ClassNode) -> Model {
        let (mut at, mut align, mut fields) = match &class.base {
            Some(base) => {
                let base = self.class(base);
                (base.size, base.align, base.fields)
            }
            None if !class.final_ => (self.p, self.p, Vec::new()),
            None => (0, 1, Vec::new()),
        };
        for field in &class.fields {
            let m = self.model(field);
            if !class.packed {
                at = up(at, m.align);
                align = align.max(m.align);
            }
            fields.push(at);
            at += m.size;
        }
        if let Some(n) = class.align {
            align = align.max(u64::from(n));
        }
        Model {
            size: up(at, align),
            align,
            fields,
            payload: None,
        }
    }
}

/// Builds a node into a world.
fn build(w: &mut World, node: &Node, count: &mut usize) -> Ty {
    match node {
        Node::Prim(s) | Node::Word(s) => w.ty(s),
        Node::Fixed(inner, n) => {
            let inner = build(w, inner, count);
            w.tcx.mk_fixed(inner, *n)
        }
        Node::Nullable(inner) => {
            let inner = build(w, inner, count);
            w.tcx.mk_nullable(inner)
        }
        Node::Tuple(parts) => {
            let parts: Vec<Ty> = parts.iter().map(|n| build(w, n, count)).collect();
            w.tcx.mk_tuple(&parts)
        }
        Node::Object(fields) => {
            let fields = fields
                .iter()
                .map(|(name, n)| (intern(name), build(w, n, count)))
                .collect();
            w.tcx.mk_object(fields)
        }
        Node::Class(class) => build_class(w, class, count),
        Node::Enum { repr, cases } => {
            let built: Vec<Vec<Ty>> = cases
                .iter()
                .map(|case| case.iter().map(|n| build(w, n, count)).collect())
                .collect();
            let names: Vec<String> = (0..built.len()).map(|i| format!("V{i}")).collect();
            let fields: Vec<Vec<String>> = built
                .iter()
                .map(|case| (0..case.len()).map(|i| format!("f{i}")).collect())
                .collect();
            let cases: Vec<Case<'_>> = built
                .iter()
                .enumerate()
                .map(|(i, case)| {
                    (
                        names[i].as_str(),
                        case.iter()
                            .enumerate()
                            .map(|(j, &t)| (fields[i][j].as_str(), t))
                            .collect(),
                        None,
                    )
                })
                .collect();
            *count += 1;
            let (adt, _) = w.enumeration(&format!("E{count}"), &[], *repr, &cases);
            w.tcx.mk_adt(adt, &[])
        }
    }
}

fn build_class(w: &mut World, class: &ClassNode, count: &mut usize) -> Ty {
    let base = class.base.as_ref().map(|b| build_class(w, b, count));
    let fields: Vec<Ty> = class.fields.iter().map(|n| build(w, n, count)).collect();
    *count += 1;
    let modifier = if class.final_ {
        ClassModifier::Final
    } else {
        ClassModifier::Plain
    };
    let attrs = Attrs {
        packed: class.packed,
        align: class.align,
        ..Attrs::default()
    };
    let (adt, _) = w.class(&format!("C{count}"), modifier, attrs, &[]);
    if let Some(base) = base {
        w.extends(adt, base);
    }
    for (i, ty) in fields.into_iter().enumerate() {
        w.field(adt, &format!("f{i}"), ty);
    }
    w.tcx.mk_adt(adt, &[])
}

fn world(target: &str) -> World {
    let mut w = World::new(target);
    w.declare("public interface Speaker { }");
    w
}

/// Every node of a tree, the tree first.
fn nodes(node: &Node) -> Vec<&Node> {
    let mut out = vec![node];
    match node {
        Node::Prim(_) | Node::Word(_) => {}
        Node::Fixed(inner, _) | Node::Nullable(inner) => out.extend(nodes(inner)),
        Node::Tuple(parts) => parts.iter().for_each(|n| out.extend(nodes(n))),
        Node::Object(fields) => fields.iter().for_each(|(_, n)| out.extend(nodes(n))),
        Node::Class(class) => out.extend(class_nodes(class)),
        Node::Enum { cases, .. } => cases.iter().flatten().for_each(|n| out.extend(nodes(n))),
    }
    out
}

fn class_nodes(class: &ClassNode) -> Vec<&Node> {
    let mut out = Vec::new();
    if let Some(base) = &class.base {
        out.extend(class_nodes(base));
    }
    class.fields.iter().for_each(|n| out.extend(nodes(n)));
    out
}

/// The fields of a class, its base's first.
fn class_fields(class: &ClassNode) -> Vec<&Node> {
    let mut out = class
        .base
        .as_ref()
        .map(|base| class_fields(base))
        .unwrap_or_default();
    out.extend(class.fields.iter());
    out
}

/// What a property is given: a built node, its layout, the model's view, and the
/// layouts of its fields and cases.
struct Checked<'a> {
    node: &'a Node,
    layout: &'a Layout,
    model: &'a Model,
    /// `(size, align)` of each field, in `Layout::fields` order.
    fields: Vec<(u64, u32)>,
    /// `(size, align)` of each case's fields.
    cases: Vec<Vec<(u64, u32)>>,
    p: u64,
    /// The base's layout, for a class with one.
    base: Option<Layout>,
    /// The layout a context that laid out other types first gives the node.
    cached: Layout,
}

type Property = fn(&Checked<'_>) -> Result<(), String>;

/// Builds `root` in a fresh world on `target` and runs `property` on every node.
fn check_tree(target: &str, root: &Node, property: Property) -> Result<(), String> {
    let mut w = world(target);
    let spec = Spec11 {
        p: w.p(),
        i64_align: u64::from(w.tcx.target().layout.i64_align),
    };
    let mut count = 0;
    for node in nodes(root) {
        let ty = build(&mut w, node, &mut count);
        let layout = w.layout(ty).map_err(|e| format!("no layout: {e:?}"))?;
        let model = spec.model(node);
        let sizes = |w: &mut World, count: &mut usize, ns: &[&Node]| -> Vec<(u64, u32)> {
            ns.iter()
                .map(|n| {
                    let t = build(w, n, count);
                    let l = w.ok(t);
                    (l.size, l.align)
                })
                .collect()
        };
        let p = spec.p;
        let fields: Vec<(u64, u32)> = match node {
            Node::Word("string" | "u8[]") => vec![(p, p as u32); 3],
            Node::Word("Box<Speaker>" | "&Slice<u8>" | "&Speaker") => vec![(p, p as u32); 2],
            Node::Tuple(parts) => sizes(&mut w, &mut count, &parts.iter().collect::<Vec<_>>()),
            Node::Object(fields) => {
                let mut sorted: Vec<&(&str, Node)> = fields.iter().collect();
                sorted.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
                let ns: Vec<&Node> = sorted.iter().map(|(_, n)| n).collect();
                sizes(&mut w, &mut count, &ns)
            }
            Node::Class(class) => sizes(&mut w, &mut count, &class_fields(class)),
            _ => Vec::new(),
        };
        let cases: Vec<Vec<(u64, u32)>> = match node {
            Node::Enum { cases, .. } => cases
                .iter()
                .map(|case| sizes(&mut w, &mut count, &case.iter().collect::<Vec<_>>()))
                .collect(),
            Node::Nullable(inner) => {
                let t = build(&mut w, inner, &mut count);
                let l = w.ok(t);
                vec![Vec::new(), vec![(l.size, l.align)]]
            }
            _ => Vec::new(),
        };
        let base = match node {
            Node::Class(class) => class.base.as_ref().map(|b| {
                let t = build_class(&mut w, b, &mut count);
                (*w.ok(t)).clone()
            }),
            _ => None,
        };
        // A context that has laid out every other type first, its parts included.
        let mut warm = LayoutCx::new(&w.tcx);
        for other in (0..w.tcx.ty_count()).rev() {
            let _ = warm.layout_of(Ty(other as u32));
        }
        let cached = (*warm.layout_of(ty).map_err(|e| format!("{e:?}"))?).clone();
        property(&Checked {
            node,
            layout: &layout,
            model: &model,
            fields,
            cases,
            p,
            base,
            cached,
        })
        .map_err(|e| format!("{e}\n  at {node:?}\n  laid out as {layout:?}"))?;
    }
    Ok(())
}

fn agrees_with_model(c: &Checked<'_>) -> Result<(), String> {
    let l = c.layout;
    let m = c.model;
    if (l.size, u64::from(l.align)) != (m.size, m.align) {
        return Err(format!(
            "size and align {:?}, the model says {:?}",
            (l.size, l.align),
            (m.size, m.align)
        ));
    }
    if l.fields != m.fields {
        return Err(format!(
            "fields {:?}, the model says {:?}",
            l.fields, m.fields
        ));
    }
    if l.variants.as_ref().map(|v| v.payload) != m.payload {
        return Err(format!("payload, the model says {:?}", m.payload));
    }
    Ok(())
}

fn sizes_are_multiples(c: &Checked<'_>) -> Result<(), String> {
    let l = c.layout;
    if !l.align.is_power_of_two() {
        return Err(format!("alignment {} is no power of two", l.align));
    }
    if !l.size.is_multiple_of(u64::from(l.align)) {
        return Err(format!("size {} is no multiple of {}", l.size, l.align));
    }
    for v in l.variants.iter().flat_map(|v| v.variants.iter()) {
        if v.size > l.size {
            return Err(format!("a case of {} bytes in {}", v.size, l.size));
        }
    }
    Ok(())
}

fn packed(node: &Node) -> bool {
    matches!(node, Node::Class(class) if class.packed)
}

/// Each field of a list at its offset: aligned unless packed, inside `size`.
fn inside(offsets: &[u64], fields: &[(u64, u32)], size: u64, aligned: bool) -> Result<(), String> {
    if offsets.len() != fields.len() {
        return Err(format!(
            "{} offsets for {} fields",
            offsets.len(),
            fields.len()
        ));
    }
    for (&at, &(len, align)) in offsets.iter().zip(fields) {
        if aligned && at % u64::from(align) != 0 {
            return Err(format!("a field at {at} needs alignment {align}"));
        }
        if at + len > size {
            return Err(format!("a field at {at} of {len} bytes ends past {size}"));
        }
    }
    Ok(())
}

fn fields_aligned_inside(c: &Checked<'_>) -> Result<(), String> {
    let l = c.layout;
    inside(&l.fields, &c.fields, l.size, !packed(c.node))?;
    if let Some(sum) = &l.variants {
        for (case, fields) in sum.variants.iter().zip(&c.cases) {
            inside(&case.fields, fields, l.size, true)?;
            if case.fields.iter().any(|&at| at < sum.payload) {
                return Err("a case's field before the payload".into());
            }
        }
        let tag = match sum.tag {
            enrang_layout::TagLayout::Direct { size } => u64::from(size),
            enrang_layout::TagLayout::NullWord => 0,
        };
        if sum.payload < tag {
            return Err("the payload overlaps the tag".into());
        }
    }
    if let Node::Class(class) = c.node {
        let hidden = !class.final_ || class.base.is_some();
        if hidden && l.fields.iter().any(|&at| at < c.p) {
            return Err("a field over the hidden table pointer".into());
        }
    }
    Ok(())
}

fn disjoint(offsets: &[u64], fields: &[(u64, u32)]) -> Result<(), String> {
    for i in 0..offsets.len() {
        for j in i + 1..offsets.len() {
            let (a, b) = ((offsets[i], fields[i].0), (offsets[j], fields[j].0));
            if a.1 > 0 && b.1 > 0 && a.0 < b.0 + b.1 && b.0 < a.0 + a.1 {
                return Err(format!("fields {i} and {j} overlap: {a:?} and {b:?}"));
            }
        }
    }
    Ok(())
}

fn fields_disjoint(c: &Checked<'_>) -> Result<(), String> {
    disjoint(&c.layout.fields, &c.fields)?;
    for (case, fields) in c
        .layout
        .variants
        .iter()
        .flat_map(|v| v.variants.iter())
        .zip(&c.cases)
    {
        disjoint(&case.fields, fields)?;
    }
    Ok(())
}

fn subclass_prefix(c: &Checked<'_>) -> Result<(), String> {
    let Some(base) = &c.base else {
        return Ok(());
    };
    let l = c.layout;
    if l.fields[..base.fields.len()] != base.fields[..] {
        return Err(format!(
            "base offsets {:?} moved to {:?}",
            base.fields, l.fields
        ));
    }
    if l.fields[base.fields.len()..]
        .iter()
        .any(|&at| at < base.size)
    {
        return Err(format!(
            "an own field inside the base's {} bytes",
            base.size
        ));
    }
    if l.align < base.align {
        return Err("a subclass aligned below its base".into());
    }
    Ok(())
}

fn sorted_by_alignment(c: &Checked<'_>) -> Result<(), String> {
    if !matches!(c.node, Node::Tuple(_) | Node::Object(_)) {
        return Ok(());
    }
    let l = c.layout;
    for i in 0..c.fields.len() {
        for j in 0..c.fields.len() {
            if c.fields[i].1 > c.fields[j].1 && l.fields[i] > l.fields[j] {
                return Err(format!("field {i} aligns more than {j} but comes after it"));
            }
        }
    }
    Ok(())
}

fn cached_equals_fresh(c: &Checked<'_>) -> Result<(), String> {
    if c.cached != *c.layout {
        return Err(format!("cached {:?}", c.cached));
    }
    Ok(())
}

const PROPERTIES: [(&str, Property); 7] = [
    (
        "layouts agree with an independent model of SPEC 11",
        agrees_with_model,
    ),
    (
        "sizes are multiples of power-of-two alignments",
        sizes_are_multiples,
    ),
    (
        "fields are aligned and inside the value",
        fields_aligned_inside,
    ),
    ("fields do not overlap", fields_disjoint),
    ("a subclass keeps its base's offsets", subclass_prefix),
    (
        "objects and tuples place larger alignments first",
        sorted_by_alignment,
    ),
    ("a cached layout equals a fresh one", cached_equals_fresh),
];

/// The forms a generated tree reaches, by name.
fn forms(node: &Node, seen: &mut std::collections::BTreeSet<&'static str>) {
    for n in nodes(node) {
        seen.insert(match n {
            Node::Prim(_) => "primitive",
            Node::Word(w) if w.starts_with('&') => "reference",
            Node::Word(_) => "word",
            Node::Fixed(..) => "fixed array",
            Node::Nullable(inner) if matches!(**inner, Node::Word("&Speaker")) => "&I | null",
            Node::Nullable(_) => "nullable",
            Node::Tuple(_) => "tuple",
            Node::Object(_) => "object",
            Node::Class(class) if class.base.is_some() => "subclass",
            Node::Class(class) if class.packed => "packed class",
            Node::Class(class) if class.align.is_some() => "aligned class",
            Node::Class(class) if class.final_ => "final class",
            Node::Class(_) => "open class",
            Node::Enum { cases, repr } if cases.iter().all(Vec::is_empty) && repr.is_some() => {
                "enum with @repr"
            }
            Node::Enum { cases, .. } if cases.iter().all(Vec::is_empty) => "payload-free enum",
            Node::Enum { .. } => "payload enum",
        });
    }
}

pub fn register(h: &mut Harness) {
    h.case("props/the generator reaches every form", || {
        let mut seen = std::collections::BTreeSet::new();
        for target in TARGETS {
            let mut rng = rng_for(&format!("layout-props-{target}"));
            for _ in 0..scaled(250) {
                forms(&gen_node(&mut rng, 3, true), &mut seen);
            }
        }
        let all = [
            "primitive",
            "reference",
            "word",
            "fixed array",
            "&I | null",
            "nullable",
            "tuple",
            "object",
            "subclass",
            "packed class",
            "aligned class",
            "final class",
            "open class",
            "enum with @repr",
            "payload-free enum",
            "payload enum",
        ];
        let missing: Vec<&&str> = all.iter().filter(|f| !seen.contains(**f)).collect();
        assert!(missing.is_empty(), "never generated: {missing:?}");
    });
    for (name, property) in PROPERTIES {
        for target in TARGETS {
            h.case(format!("props/{name} on {target}"), move || {
                let label = format!("layout-props-{target}");
                let mut rng = rng_for(&label);
                for _ in 0..scaled(250) {
                    let root = gen_node(&mut rng, 3, true);
                    if check_tree(target, &root, property).is_err() {
                        let small = shrink(root, |n| check_tree(target, n, property).is_err());
                        let why = check_tree(target, &small, property).unwrap_err();
                        panic!(
                            "{name} fails on {target} (ENRANG_SEED={}, stream {label}):\n  {why}",
                            seed()
                        );
                    }
                }
            });
        }
    }
}
