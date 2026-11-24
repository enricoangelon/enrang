//! Types as diagnostics print them (SPEC 4.1's spellings, SPEC 13's messages), and
//! as an overload's stable path names its parameters (ARCHITECTURE 6.8).
//!
//! `i64`, `&i64[]` (`&(i64[])`), `(&i64)[]`, `Box<Animal>`, `i64 | null`,
//! `&i64 | null` (`(&i64) | null`), `(i64 | null) | null`, `[int, string]`,
//! `{ age: int, name: string }`, `{ nick?: string | null }`, `Slice<u8>`, `T`.
//! Choices where the documents are silent: `i32` prints `int`, the spelling every
//! SPEC message uses for it (S:600, S:688, S:728); `Result<T, Failure>` prints
//! `Result<T>` (S:591); a field written `x?: T` prints `x?:` before its collapsed
//! type, so the spelling reads back as the same type; a function pointer or closure
//! prints its parameters without names, `fn(&i64) => void` and `(let &i64) => void`,
//! because a type keeps no names (A:288), unless the declaration that wrote it kept
//! them ([`Tcx::fn_ty_string`], D14: `fn(let s: &string) => void`, as SPEC 4.5's
//! EN0615 prints it); an inference variable and `Error` print `_`, since sema
//! resolves a variable before it prints one.
//!
//! [`Tcx::ty_path_string`] is the spelling of an overload's parameter in its
//! [`ItemPath`](crate::ItemPath): a class, enum or interface is named by its own
//! path (`&src/b::Node`), and so is the interface or shape an implicit parameter
//! stands for, so overloads over two same-named classes of two modules get two
//! paths (A:1281).

use enrang_base::Symbol;

use crate::ids::{FnSigId, ParamId, TyList};
use crate::lang::LangItem;
use crate::sig::{Implicit, Mark};
use crate::tcx::Tcx;
use crate::ty::{IntTy, Ty, TyKind};

/// Where a type is printed, which decides whether it needs parentheses.
#[derive(Copy, Clone, PartialEq, Eq)]
enum Place {
    /// Anywhere a whole type stands: a top level, a type argument, a tuple part.
    Whole,
    /// Before `[]` or `[N]`.
    Element,
    /// After `&` or `*`.
    Pointee,
    /// Before `| null`.
    Nullable,
}

/// How a type is spelled.
#[derive(Copy, Clone)]
struct Style<'n> {
    /// Name definitions by their stable paths (an overload's `ItemPath`).
    qualified: bool,
    /// The parameter names of the function type at the top, under at most one
    /// `| null`, as its declaration wrote them.
    names: Option<&'n [Symbol]>,
}

impl Style<'_> {
    /// The style for a type inside this one: names belong to the top only.
    fn inner(self) -> Style<'static> {
        Style {
            qualified: self.qualified,
            names: None,
        }
    }
}

impl Tcx {
    /// `t` spelled as SPEC writes types.
    pub fn ty_string(&self, t: Ty) -> String {
        self.spell(
            t,
            Style {
                qualified: false,
                names: None,
            },
        )
    }

    /// `t` spelled as [`Tcx::ty_string`] does, a function type at its top (under at
    /// most one `| null`) with the parameter names its declaration wrote, kept
    /// outside the type (D14): `fn(let s: &string) => void`. A name list of the
    /// wrong length is ignored.
    pub fn fn_ty_string(&self, t: Ty, names: Option<&[Symbol]>) -> String {
        self.spell(
            t,
            Style {
                qualified: false,
                names,
            },
        )
    }

    /// `t` spelled for an overload's stable path (ARCHITECTURE 6.8): every class,
    /// enum and interface by its item path, `Result` with both arguments, and an
    /// implicit parameter by what it stands for, so the spelling never depends on
    /// load order and two same-named classes of two modules differ.
    pub fn ty_path_string(&self, t: Ty) -> String {
        self.spell(
            t,
            Style {
                qualified: true,
                names: None,
            },
        )
    }

    fn spell(&self, t: Ty, style: Style<'_>) -> String {
        let mut out = String::new();
        self.write_ty(t, Place::Whole, style, &mut out);
        out
    }

    fn write_ty(&self, t: Ty, place: Place, style: Style<'_>, out: &mut String) {
        let kind = self.kind(t);
        let wrap = match kind {
            // `(i64 | null) | null` (A:888's `Opt<i64 | null>`) stays two layers.
            TyKind::Nullable(_) => place != Place::Whole,
            TyKind::Ref(_) | TyKind::Raw(_) => place == Place::Element,
            TyKind::FnPtr(..) | TyKind::Closure(_) => place != Place::Whole,
            _ => false,
        };
        if wrap {
            out.push('(');
            self.write_ty(t, Place::Whole, style, out);
            out.push(')');
            return;
        }
        let inner = style.inner();
        match kind {
            TyKind::Bool => out.push_str("bool"),
            TyKind::Int(IntTy::I32) => out.push_str("int"),
            TyKind::Int(int) => out.push_str(int.name()),
            TyKind::Float(float) => out.push_str(float.name()),
            TyKind::Void => out.push_str("void"),
            TyKind::Never => out.push_str("never"),
            TyKind::Str => out.push_str("string"),
            TyKind::Array(elem) => {
                self.write_ty(elem, Place::Element, inner, out);
                out.push_str("[]");
            }
            TyKind::Fixed(elem, n) => {
                self.write_ty(elem, Place::Element, inner, out);
                out.push_str(&format!("[{n}]"));
            }
            TyKind::Slice(elem) => {
                out.push_str("Slice<");
                self.write_ty(elem, Place::Whole, inner, out);
                out.push('>');
            }
            TyKind::Boxed(boxed) => {
                out.push_str("Box<");
                self.write_ty(boxed, Place::Whole, inner, out);
                out.push('>');
            }
            TyKind::Tuple(parts) => {
                out.push('[');
                self.write_list(parts, inner, out);
                out.push(']');
            }
            TyKind::Nullable(present) => {
                // A nullable is wrapped anywhere but at the top, so the names reach
                // a function type under `| null` there.
                self.write_ty(present, Place::Nullable, style, out);
                out.push_str(" | null");
            }
            TyKind::Ref(pointee) => {
                out.push('&');
                self.write_ty(pointee, Place::Pointee, inner, out);
            }
            TyKind::Raw(pointee) => {
                out.push('*');
                self.write_ty(pointee, Place::Pointee, inner, out);
            }
            TyKind::FnPtr(abi, sig) => {
                if let Some(name) = abi.name() {
                    out.push_str(&format!("@abi(\"{name}\") "));
                }
                if self.fn_sig(sig).unsafety {
                    out.push_str("unsafe ");
                }
                out.push_str("fn");
                self.write_sig(sig, style, out);
            }
            TyKind::Closure(sig) => self.write_sig(sig, style, out),
            TyKind::Adt(adt, args) => {
                let def = self.adt(adt);
                if style.qualified {
                    out.push_str(&self.def(def.def).path.to_string());
                } else {
                    out.push_str(def.name.as_str());
                }
                let mut args: Vec<Ty> = self.list(args).to_vec();
                if !style.qualified && self.is_lang_adt(adt, LangItem::Result) && args.len() == 2 {
                    let failure = self.lang_adt(LangItem::Failure);
                    if let TyKind::Adt(err, _) = self.kind(args[1])
                        && Some(err) == failure
                    {
                        args.pop();
                    }
                }
                if !args.is_empty() {
                    let list = self.intern_list(&args);
                    out.push('<');
                    self.write_list(list, inner, out);
                    out.push('>');
                }
            }
            TyKind::Param(p) => self.write_param(p, inner, out),
            TyKind::Object(shape) => {
                let shape = self.shape(shape);
                if shape.fields.is_empty() {
                    out.push_str("{}");
                } else {
                    out.push_str("{ ");
                    for (i, (name, ty)) in shape.fields.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        out.push_str(name.as_str());
                        if shape.is_optional(*name) {
                            out.push('?');
                        }
                        out.push_str(": ");
                        self.write_ty(*ty, Place::Whole, inner, out);
                    }
                    out.push_str(" }");
                }
            }
            TyKind::Infer(_) | TyKind::Error => out.push('_'),
        }
    }

    /// A type parameter by its name; in a stable path, an implicit one (D5) by the
    /// interface or shape it stands for, an interface's own `Self` staying `Self`.
    fn write_param(&self, p: ParamId, style: Style<'_>, out: &mut String) {
        let param = self.param(p);
        if style.qualified {
            match param.implicit {
                Some(Implicit::Interface(adt))
                    if self.adt(adt).as_interface().map(|i| i.self_param) != Some(p) =>
                {
                    let bound = param
                        .bounds
                        .iter()
                        .map(|&b| self.bound(b))
                        .find(|b| b.adt() == adt);
                    let args = bound.map_or(self.empty_list(), |b| b.args());
                    let ty = self.intern_ty(TyKind::Adt(adt, args));
                    self.write_ty(ty, Place::Whole, style, out);
                    return;
                }
                Some(Implicit::Shape(shape)) => {
                    let ty = self.intern_ty(TyKind::Object(shape));
                    self.write_ty(ty, Place::Whole, style, out);
                    return;
                }
                _ => {}
            }
        }
        out.push_str(param.name.as_str());
    }

    fn write_list(&self, list: TyList, style: Style<'_>, out: &mut String) {
        for (i, &ty) in self.list(list).iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            self.write_ty(ty, Place::Whole, style, out);
        }
    }

    /// `(params) => ret`, the part after `fn` and the whole of a closure type, with
    /// the parameter names `style` carries when there is one per parameter.
    fn write_sig(&self, sig: FnSigId, style: Style<'_>, out: &mut String) {
        let sig = self.fn_sig(sig);
        let names = style.names.filter(|names| names.len() == sig.params.len());
        let inner = style.inner();
        out.push('(');
        for (i, (ty, mark)) in sig.params.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            match mark {
                Mark::None => {}
                Mark::Let => out.push_str("let "),
                Mark::Const => out.push_str("const "),
            }
            if let Some(names) = names {
                out.push_str(names[i].as_str());
                out.push_str(": ");
            }
            self.write_ty(*ty, Place::Whole, inner, out);
        }
        out.push_str(") => ");
        if sig.ret_readonly {
            out.push_str("readonly ");
        }
        self.write_ty(sig.ret, Place::Whole, inner, out);
    }
}
