//! `Tcx`: every definition, signature and ADT of a program, and the type interner
//! (ARCHITECTURE 2.4, 3; A:749-763).
//!
//! Definitions live in `IdVec`s and every map is a `BTreeMap`; ids order nothing
//! that reaches output (ARCHITECTURE 1). Types are interned behind a `RefCell`, so a
//! shared `&Tcx` can make new types while bodies are typed (`intern_ty(&self)`),
//! and `kind` returns a `TyKind` by value (departure D2). Lists, signatures, shapes
//! and literal texts are interned the same way and handed out behind `Arc`, which
//! keeps a `Tcx` `Send`.
//!
//! The on-demand queries ARCHITECTURE 3 runs over a shared `&Tcx` and calls
//! memoised (`borrowck::contract`, `class_contract`, `layout_of`; A:772, A:816-817,
//! A:762) keep their results in memo tables here, behind `RefCell`s like the
//! interner: a query computes outside any borrow, so it may ask other queries, and
//! the first result stored for a key wins. The layout table is opaque, since this
//! crate cannot name `enrang-layout`'s types.
//!
//! `define_adt` and `define_fn` are the public way to build a program without a
//! front end, as MIR fixtures do (ARCHITECTURE 1 "Parallel work rules"); sema uses
//! them too, with the finer `define_*` and `*_mut` calls to fill a declaration in
//! steps (a class's fields name the class itself).

use std::any::Any;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::sync::Arc;

use enrang_base::{IdVec, Idx, SourceMap, Symbol};
use enrang_target::TargetSpec;

use crate::adt::{AdtDecl, AdtDef, AdtKind, FieldDef};
use crate::consts::{ConstTree, StringTable};
use crate::contract::{ClassContract, Contract};
use crate::def::{AliasDef, DefData, DefKind, ModuleInfo};
use crate::ids::{
    AdtId, BoundId, DefId, FieldIdx, FnSigId, GenericsId, HostCallId, ModuleId, ParamId, ShapeId,
    StringId, TyList,
};
use crate::lang::LangItem;
use crate::sig::{Bound, FnDecl, FnSig, Generics, TyParamDef, TyParamFacts};
use crate::ty::{Abi, FloatTy, FnPtrSig, IntTy, Shape, Ty, TyKind};

/// An `extend` block (SPEC 3.1): the pattern type it extends, with its own type
/// parameters, and its members. `Tcx::member` reads the blocks whose module is in
/// the looking module's import closure (A:886).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExtendDef {
    pub def: DefId,
    pub module: ModuleId,
    pub generics: GenericsId,
    pub ty: Ty,
    pub members: Vec<DefId>,
}

/// The types every pass names, interned once by `Tcx::new`.
#[derive(Copy, Clone, Debug)]
pub struct CommonTypes {
    pub bool: Ty,
    pub void: Ty,
    pub never: Ty,
    pub str: Ty,
    pub error: Ty,
    pub i8: Ty,
    pub i16: Ty,
    pub i32: Ty,
    pub i64: Ty,
    pub u8: Ty,
    pub u16: Ty,
    pub u32: Ty,
    pub u64: Ty,
    pub isize: Ty,
    pub usize: Ty,
    pub f32: Ty,
    pub f64: Ty,
}

impl CommonTypes {
    pub fn int(&self, int: IntTy) -> Ty {
        match int {
            IntTy::I8 => self.i8,
            IntTy::I16 => self.i16,
            IntTy::I32 => self.i32,
            IntTy::I64 => self.i64,
            IntTy::U8 => self.u8,
            IntTy::U16 => self.u16,
            IntTy::U32 => self.u32,
            IntTy::U64 => self.u64,
            IntTy::Isize => self.isize,
            IntTy::Usize => self.usize,
        }
    }

    pub fn float(&self, float: FloatTy) -> Ty {
        match float {
            FloatTy::F32 => self.f32,
            FloatTy::F64 => self.f64,
        }
    }
}

#[derive(Default)]
struct Interner {
    kinds: Vec<TyKind>,
    ty_ids: BTreeMap<TyKind, Ty>,
    lists: Vec<Arc<[Ty]>>,
    list_ids: BTreeMap<Arc<[Ty]>, TyList>,
    sigs: Vec<Arc<FnPtrSig>>,
    sig_ids: BTreeMap<Arc<FnPtrSig>, FnSigId>,
    shapes: Vec<Arc<Shape>>,
    shape_ids: BTreeMap<Arc<Shape>, ShapeId>,
    strings: StringTable,
}

/// The type context of one program.
pub struct Tcx {
    target: Arc<TargetSpec>,
    map: Arc<SourceMap>,
    defs: IdVec<DefId, DefData>,
    adts: IdVec<AdtId, AdtDef>,
    modules: IdVec<ModuleId, ModuleInfo>,
    generics: IdVec<GenericsId, Generics>,
    params: IdVec<ParamId, TyParamDef>,
    bounds: IdVec<BoundId, Bound>,
    extends: Vec<ExtendDef>,
    sigs: BTreeMap<DefId, FnSig>,
    consts: BTreeMap<DefId, ConstTree>,
    item_tys: BTreeMap<DefId, Ty>,
    aliases: BTreeMap<DefId, AliasDef>,
    langs: BTreeMap<LangItem, DefId>,
    facts: BTreeMap<DefId, TyParamFacts>,
    host_calls: Vec<Symbol>,
    interner: RefCell<Interner>,
    memo: RefCell<Memo>,
    common: CommonTypes,
    empty_generics: GenericsId,
    empty_list: TyList,
}

/// A memoised layout, opaque here: `enrang-layout` stores and reads its own type.
pub type LayoutMemo = Arc<dyn Any + Send + Sync>;

/// The memo tables of the on-demand queries (A:772, A:816-817, A:762).
#[derive(Default)]
struct Memo {
    contracts: BTreeMap<DefId, Arc<Contract>>,
    class_contracts: BTreeMap<AdtId, ClassContract>,
    layouts: BTreeMap<Ty, LayoutMemo>,
}

impl Tcx {
    /// An empty context for `target`, whose spans point into `map`.
    pub fn new(target: Arc<TargetSpec>, map: Arc<SourceMap>) -> Tcx {
        let mut interner = Interner::default();
        let mut mk = |kind: TyKind| intern_kind(&mut interner, kind);
        let common = CommonTypes {
            bool: mk(TyKind::Bool),
            void: mk(TyKind::Void),
            never: mk(TyKind::Never),
            str: mk(TyKind::Str),
            error: mk(TyKind::Error),
            i8: mk(TyKind::Int(IntTy::I8)),
            i16: mk(TyKind::Int(IntTy::I16)),
            i32: mk(TyKind::Int(IntTy::I32)),
            i64: mk(TyKind::Int(IntTy::I64)),
            u8: mk(TyKind::Int(IntTy::U8)),
            u16: mk(TyKind::Int(IntTy::U16)),
            u32: mk(TyKind::Int(IntTy::U32)),
            u64: mk(TyKind::Int(IntTy::U64)),
            isize: mk(TyKind::Int(IntTy::Isize)),
            usize: mk(TyKind::Int(IntTy::Usize)),
            f32: mk(TyKind::Float(FloatTy::F32)),
            f64: mk(TyKind::Float(FloatTy::F64)),
        };
        let empty_list = intern_list(&mut interner, &[]);
        let mut generics = IdVec::new();
        let empty_generics = generics.push(Generics::new(None, Vec::new()));
        Tcx {
            target,
            map,
            defs: IdVec::new(),
            adts: IdVec::new(),
            modules: IdVec::new(),
            generics,
            params: IdVec::new(),
            bounds: IdVec::new(),
            extends: Vec::new(),
            sigs: BTreeMap::new(),
            consts: BTreeMap::new(),
            item_tys: BTreeMap::new(),
            aliases: BTreeMap::new(),
            langs: BTreeMap::new(),
            facts: BTreeMap::new(),
            host_calls: Vec::new(),
            interner: RefCell::new(interner),
            memo: RefCell::new(Memo::default()),
            common,
            empty_generics,
            empty_list,
        }
    }

    /// An empty context for the target preset or alias `name` with no options, or
    /// `None` when no target has that name. A crate that cannot name
    /// `enrang-target` makes its `Tcx` here, as `enrang-mir`'s `parse_module` does
    /// (ARCHITECTURE 1's graph: `mir -> base hir`).
    pub fn for_target(name: &str, map: Arc<SourceMap>) -> Option<Tcx> {
        let (spec, _) = enrang_target::resolve(name, &enrang_target::TargetOpts::default()).ok()?;
        Some(Tcx::new(Arc::new(spec), map))
    }

    pub fn target(&self) -> &TargetSpec {
        &self.target
    }

    pub fn target_arc(&self) -> Arc<TargetSpec> {
        Arc::clone(&self.target)
    }

    pub fn map(&self) -> &SourceMap {
        &self.map
    }

    /// Replaces the source map: a front end that adds files after the `Tcx` exists
    /// hands it the grown map.
    pub fn set_map(&mut self, map: Arc<SourceMap>) {
        self.map = map;
    }

    pub fn common(&self) -> &CommonTypes {
        &self.common
    }

    // -----------------------------------------------------------------------------
    // Defining.

    /// Defines a class, enum or interface with its definition (A:753). The
    /// definition's kind becomes `DefKind::Adt`, or `StrUnion` for an enum with
    /// `str_union`, whatever `d.data.kind` says.
    pub fn define_adt(&mut self, d: AdtDecl) -> AdtId {
        let adt = self.adts.next_index();
        let mut data = d.data;
        data.kind = match &d.kind {
            AdtKind::Enum(e) if e.str_union => DefKind::StrUnion(adt),
            _ => DefKind::Adt(adt),
        };
        let def = self.defs.push(data);
        self.adts.push(AdtDef {
            def,
            name: d.name,
            generics: d.generics,
            kind: d.kind,
        })
    }

    /// Defines a function, method, constructor or destructor with its signature
    /// (A:754).
    pub fn define_fn(&mut self, d: FnDecl) -> DefId {
        let def = self.defs.push(d.data());
        self.sigs.insert(def, d.sig);
        def
    }

    /// Defines anything else, or a function whose signature comes later
    /// (`set_sig`).
    pub fn define_def(&mut self, d: DefData) -> DefId {
        self.defs.push(d)
    }

    pub fn define_module(&mut self, m: ModuleInfo) -> ModuleId {
        self.modules.push(m)
    }

    pub fn define_generics(&mut self, g: Generics) -> GenericsId {
        self.generics.push(g)
    }

    pub fn define_param(&mut self, p: TyParamDef) -> ParamId {
        self.params.push(p)
    }

    pub fn define_bound(&mut self, b: Bound) -> BoundId {
        self.bounds.push(b)
    }

    pub fn define_extend(&mut self, e: ExtendDef) {
        self.extends.push(e);
    }

    pub fn set_sig(&mut self, d: DefId, s: FnSig) {
        self.sigs.insert(d, s);
    }

    pub fn set_const(&mut self, d: DefId, v: ConstTree) {
        self.consts.insert(d, v);
    }

    /// The declared or inferred type of a constant or `unsafe let`.
    pub fn set_item_ty(&mut self, d: DefId, t: Ty) {
        self.item_tys.insert(d, t);
    }

    pub fn set_alias(&mut self, d: DefId, a: AliasDef) {
        self.aliases.insert(d, a);
    }

    pub fn set_lang(&mut self, item: LangItem, d: DefId) {
        self.langs.insert(item, d);
    }

    pub fn set_facts(&mut self, d: DefId, f: TyParamFacts) {
        self.facts.insert(d, f);
    }

    /// The id of a `@hostCall("name")` name, interning it on first use.
    pub fn intern_host_call(&mut self, name: Symbol) -> HostCallId {
        if let Some(i) = self.host_calls.iter().position(|&n| n == name) {
            return HostCallId::new(i);
        }
        self.host_calls.push(name);
        HostCallId::new(self.host_calls.len() - 1)
    }

    pub fn host_call_name(&self, id: HostCallId) -> Symbol {
        self.host_calls[id.index()]
    }

    pub fn def_mut(&mut self, d: DefId) -> &mut DefData {
        &mut self.defs[d]
    }

    pub fn adt_mut(&mut self, a: AdtId) -> &mut AdtDef {
        &mut self.adts[a]
    }

    pub fn module_mut(&mut self, m: ModuleId) -> &mut ModuleInfo {
        &mut self.modules[m]
    }

    pub fn generics_mut(&mut self, g: GenericsId) -> &mut Generics {
        &mut self.generics[g]
    }

    pub fn param_mut(&mut self, p: ParamId) -> &mut TyParamDef {
        &mut self.params[p]
    }

    pub fn sig_mut(&mut self, d: DefId) -> Option<&mut FnSig> {
        self.sigs.get_mut(&d)
    }

    pub fn extend_mut(&mut self, i: usize) -> &mut ExtendDef {
        &mut self.extends[i]
    }

    // -----------------------------------------------------------------------------
    // Interning.

    pub fn intern_ty(&self, k: TyKind) -> Ty {
        intern_kind(&mut self.interner.borrow_mut(), k)
    }

    pub fn kind(&self, t: Ty) -> TyKind {
        self.interner.borrow().kinds[t.0 as usize]
    }

    pub fn intern_list(&self, ts: &[Ty]) -> TyList {
        intern_list(&mut self.interner.borrow_mut(), ts)
    }

    pub fn list(&self, l: TyList) -> Arc<[Ty]> {
        Arc::clone(&self.interner.borrow().lists[l.index()])
    }

    pub fn empty_list(&self) -> TyList {
        self.empty_list
    }

    pub fn intern_fn_sig(&self, s: FnPtrSig) -> FnSigId {
        let mut interner = self.interner.borrow_mut();
        if let Some(&id) = interner.sig_ids.get(&s) {
            return id;
        }
        let id = FnSigId::new(interner.sigs.len());
        let s = Arc::new(s);
        interner.sigs.push(Arc::clone(&s));
        interner.sig_ids.insert(s, id);
        id
    }

    pub fn fn_sig(&self, s: FnSigId) -> Arc<FnPtrSig> {
        Arc::clone(&self.interner.borrow().sigs[s.index()])
    }

    /// Interns a shape; its fields are sorted by name first, so one field set is
    /// one shape whatever order they were written in (SPEC 4.3).
    pub fn intern_shape(&self, s: Shape) -> ShapeId {
        let s = Shape::with_optional(s.fields, s.optional);
        let mut interner = self.interner.borrow_mut();
        if let Some(&id) = interner.shape_ids.get(&s) {
            return id;
        }
        let id = ShapeId::new(interner.shapes.len());
        let s = Arc::new(s);
        interner.shapes.push(Arc::clone(&s));
        interner.shape_ids.insert(s, id);
        id
    }

    pub fn shape(&self, s: ShapeId) -> Arc<Shape> {
        Arc::clone(&self.interner.borrow().shapes[s.index()])
    }

    pub fn intern_str(&self, s: &str) -> StringId {
        self.interner.borrow_mut().strings.intern(s)
    }

    pub fn str(&self, s: StringId) -> Arc<str> {
        self.interner.borrow().strings.get(s)
    }

    /// Every interned literal text, in interning order.
    pub fn strings(&self) -> StringTable {
        self.interner.borrow().strings.clone()
    }

    /// How many types are interned.
    pub fn ty_count(&self) -> usize {
        self.interner.borrow().kinds.len()
    }

    // Constructors of common shapes.

    pub fn mk_ref(&self, t: Ty) -> Ty {
        self.intern_ty(TyKind::Ref(t))
    }

    pub fn mk_raw(&self, t: Ty) -> Ty {
        self.intern_ty(TyKind::Raw(t))
    }

    pub fn mk_nullable(&self, t: Ty) -> Ty {
        self.intern_ty(TyKind::Nullable(t))
    }

    pub fn mk_array(&self, t: Ty) -> Ty {
        self.intern_ty(TyKind::Array(t))
    }

    pub fn mk_fixed(&self, t: Ty, n: u64) -> Ty {
        self.intern_ty(TyKind::Fixed(t, n))
    }

    pub fn mk_slice(&self, t: Ty) -> Ty {
        self.intern_ty(TyKind::Slice(t))
    }

    pub fn mk_box(&self, t: Ty) -> Ty {
        self.intern_ty(TyKind::Boxed(t))
    }

    pub fn mk_tuple(&self, ts: &[Ty]) -> Ty {
        let list = self.intern_list(ts);
        self.intern_ty(TyKind::Tuple(list))
    }

    pub fn mk_adt(&self, adt: AdtId, args: &[Ty]) -> Ty {
        let list = self.intern_list(args);
        self.intern_ty(TyKind::Adt(adt, list))
    }

    pub fn mk_param(&self, p: ParamId) -> Ty {
        self.intern_ty(TyKind::Param(p))
    }

    pub fn mk_fn_ptr(&self, abi: Abi, sig: FnPtrSig) -> Ty {
        let sig = self.intern_fn_sig(sig);
        self.intern_ty(TyKind::FnPtr(abi, sig))
    }

    pub fn mk_closure(&self, sig: FnPtrSig) -> Ty {
        let sig = self.intern_fn_sig(sig);
        self.intern_ty(TyKind::Closure(sig))
    }

    /// An object type whose fields are all required.
    pub fn mk_object(&self, fields: Vec<(Symbol, Ty)>) -> Ty {
        self.mk_object_shape(Shape::new(fields))
    }

    /// An object type of any shape, optional fields included (D13).
    pub fn mk_object_shape(&self, shape: Shape) -> Ty {
        let shape = self.intern_shape(shape);
        self.intern_ty(TyKind::Object(shape))
    }

    /// `Result<ok, err>`; `None` before the library declares `@lang("result")`.
    pub fn mk_result(&self, ok: Ty, err: Ty) -> Option<Ty> {
        let adt = self.lang_adt(LangItem::Result)?;
        Some(self.mk_adt(adt, &[ok, err]))
    }

    // -----------------------------------------------------------------------------
    // Memo tables of the on-demand queries.

    /// The memoised contract of `d`, if one was stored.
    pub fn contract_memo(&self, d: DefId) -> Option<Arc<Contract>> {
        self.memo.borrow().contracts.get(&d).cloned()
    }

    /// The contract of `d`: the memoised one, or `compute`'s, stored. `compute` runs
    /// with no table borrowed, so it may ask for other contracts; if it stores one
    /// for `d` itself, that one wins.
    pub fn contract_or_insert_with(
        &self,
        d: DefId,
        compute: impl FnOnce() -> Contract,
    ) -> Arc<Contract> {
        if let Some(done) = self.contract_memo(d) {
            return done;
        }
        let computed = Arc::new(compute());
        let mut memo = self.memo.borrow_mut();
        Arc::clone(memo.contracts.entry(d).or_insert(computed))
    }

    /// The memoised flag of the borrowing class or tuple type `a`, if one was stored.
    pub fn class_contract_memo(&self, a: AdtId) -> Option<ClassContract> {
        self.memo.borrow().class_contracts.get(&a).copied()
    }

    /// The flag of `a`: the memoised one, or `compute`'s, stored (as
    /// [`Tcx::contract_or_insert_with`]).
    pub fn class_contract_or_insert_with(
        &self,
        a: AdtId,
        compute: impl FnOnce() -> ClassContract,
    ) -> ClassContract {
        if let Some(done) = self.class_contract_memo(a) {
            return done;
        }
        let computed = compute();
        *self
            .memo
            .borrow_mut()
            .class_contracts
            .entry(a)
            .or_insert(computed)
    }

    /// The memoised layout of `t`, if `enrang-layout` stored one.
    pub fn layout_memo(&self, t: Ty) -> Option<LayoutMemo> {
        self.memo.borrow().layouts.get(&t).cloned()
    }

    /// Stores the layout of `t` unless one is stored, and returns the stored one.
    pub fn memo_layout(&self, t: Ty, layout: LayoutMemo) -> LayoutMemo {
        let mut memo = self.memo.borrow_mut();
        Arc::clone(memo.layouts.entry(t).or_insert(layout))
    }

    // -----------------------------------------------------------------------------
    // Lookups.

    pub fn def(&self, d: DefId) -> &DefData {
        &self.defs[d]
    }

    /// Every definition, in definition order (never an output order).
    pub fn defs(&self) -> impl Iterator<Item = (DefId, &DefData)> {
        self.defs.iter_enumerated()
    }

    pub fn def_count(&self) -> usize {
        self.defs.len()
    }

    /// A function's signature. Panics on a definition with none (`sig_opt`).
    pub fn sig(&self, d: DefId) -> &FnSig {
        self.sigs
            .get(&d)
            .unwrap_or_else(|| panic!("{} has no signature", self.defs[d].path))
    }

    pub fn sig_opt(&self, d: DefId) -> Option<&FnSig> {
        self.sigs.get(&d)
    }

    /// Whether `d` takes `this` as its first argument, parameter 0 of its contract
    /// (ARCHITECTURE 6.7: a constructor "stores `(1, 0)`"): a method or destructor
    /// with a `&` or `move` receiver, and every constructor, whose signature has no
    /// receiver but which runs on the object `new` or `super(...)` hands it.
    pub fn takes_this(&self, d: DefId) -> bool {
        self.defs[d].kind == DefKind::Ctor
            || self.sigs.get(&d).is_some_and(|s| {
                matches!(
                    s.receiver,
                    Some(crate::sig::Receiver::Ref(_) | crate::sig::Receiver::Move)
                )
            })
    }

    pub fn adt(&self, a: AdtId) -> &AdtDef {
        &self.adts[a]
    }

    pub fn adts(&self) -> impl Iterator<Item = (AdtId, &AdtDef)> {
        self.adts.iter_enumerated()
    }

    /// The ADT a definition is (`DefKind::Adt` or `StrUnion`).
    pub fn adt_of(&self, d: DefId) -> Option<AdtId> {
        match self.defs[d].kind {
            DefKind::Adt(adt) | DefKind::StrUnion(adt) => Some(adt),
            _ => None,
        }
    }

    pub fn generics(&self, g: GenericsId) -> &Generics {
        &self.generics[g]
    }

    /// The generics list with no parameter.
    pub fn empty_generics(&self) -> GenericsId {
        self.empty_generics
    }

    /// Every parameter in scope of `g`: its parent's first, then its own.
    pub fn all_params(&self, g: GenericsId) -> Vec<ParamId> {
        let generics = &self.generics[g];
        let mut params = match generics.parent {
            Some(parent) => self.all_params(parent),
            None => Vec::new(),
        };
        params.extend(generics.params.iter().copied());
        params
    }

    /// `g`'s own parameters as types: an item's identity arguments.
    pub fn identity_args(&self, g: GenericsId) -> TyList {
        let tys: Vec<Ty> = self.generics[g]
            .params
            .iter()
            .map(|&p| self.mk_param(p))
            .collect();
        self.intern_list(&tys)
    }

    /// An ADT's own type, with its parameters as arguments (`Stack<T>`).
    pub fn adt_identity(&self, a: AdtId) -> Ty {
        let args = self.identity_args(self.adts[a].generics);
        self.intern_ty(TyKind::Adt(a, args))
    }

    pub fn param(&self, p: ParamId) -> &TyParamDef {
        &self.params[p]
    }

    pub fn bound(&self, b: BoundId) -> &Bound {
        &self.bounds[b]
    }

    pub fn module(&self, m: ModuleId) -> &ModuleInfo {
        &self.modules[m]
    }

    pub fn modules(&self) -> impl Iterator<Item = (ModuleId, &ModuleInfo)> {
        self.modules.iter_enumerated()
    }

    pub fn module_count(&self) -> usize {
        self.modules.len()
    }

    pub fn extends(&self) -> &[ExtendDef] {
        &self.extends
    }

    pub fn const_value(&self, d: DefId) -> Option<&ConstTree> {
        self.consts.get(&d)
    }

    pub fn item_ty(&self, d: DefId) -> Option<Ty> {
        self.item_tys.get(&d).copied()
    }

    pub fn alias(&self, d: DefId) -> Option<&AliasDef> {
        self.aliases.get(&d)
    }

    pub fn facts(&self, d: DefId) -> Option<&TyParamFacts> {
        self.facts.get(&d)
    }

    /// The definition of a lang item. Panics when the library does not declare it
    /// (`lang_opt`). `TyKind::{Array, Slice, Str, Boxed}` map to their `@lang`
    /// classes through this (A:758).
    pub fn lang(&self, item: LangItem) -> DefId {
        self.lang_opt(item)
            .unwrap_or_else(|| panic!("the library declares no `@lang(\"{item}\")`"))
    }

    pub fn lang_opt(&self, item: LangItem) -> Option<DefId> {
        self.langs.get(&item).copied()
    }

    /// The ADT of a lang item that is a class, enum or interface.
    pub fn lang_adt(&self, item: LangItem) -> Option<AdtId> {
        self.lang_opt(item).and_then(|d| self.adt_of(d))
    }

    /// Whether `adt` is the lang item `item`.
    pub fn is_lang_adt(&self, adt: AdtId, item: LangItem) -> bool {
        self.lang_adt(item) == Some(adt)
    }

    /// The lang item a definition is, if any.
    pub fn lang_item_of(&self, d: DefId) -> Option<LangItem> {
        self.langs
            .iter()
            .find(|(_, def)| **def == d)
            .map(|(item, _)| *item)
    }

    /// A field's declaration in an ADT: a class's flattened field, or, with
    /// `variant`, an enum case's.
    pub fn field_def(
        &self,
        adt: AdtId,
        variant: Option<crate::ids::VariantIdx>,
        field: FieldIdx,
    ) -> &FieldDef {
        match (&self.adts[adt].kind, variant) {
            (AdtKind::Class(class), None) => &class.fields[field.index()],
            (AdtKind::Enum(e), Some(v)) => &e.variants[v.index()].fields[field.index()],
            _ => panic!("no field {field:?} in {}", self.adts[adt].name),
        }
    }

    /// A field's type at the ADT's arguments `args`.
    pub fn field_ty(
        &self,
        adt: AdtId,
        variant: Option<crate::ids::VariantIdx>,
        field: FieldIdx,
        args: TyList,
    ) -> Ty {
        let declared = self.field_def(adt, variant, field).ty;
        let params = self.generics[self.adts[adt].generics].params.clone();
        let args = self.list(args);
        self.subst(declared, &params, &args)
    }

    // -----------------------------------------------------------------------------
    // Structure.

    /// The types directly inside `t`, in order.
    pub fn children(&self, t: Ty) -> Vec<Ty> {
        match self.kind(t) {
            TyKind::Array(e)
            | TyKind::Fixed(e, _)
            | TyKind::Slice(e)
            | TyKind::Boxed(e)
            | TyKind::Nullable(e)
            | TyKind::Ref(e)
            | TyKind::Raw(e) => vec![e],
            TyKind::Tuple(list) | TyKind::Adt(_, list) => self.list(list).to_vec(),
            TyKind::FnPtr(_, sig) | TyKind::Closure(sig) => {
                let sig = self.fn_sig(sig);
                let mut tys: Vec<Ty> = sig.params.iter().map(|(t, _)| *t).collect();
                tys.push(sig.ret);
                tys
            }
            TyKind::Object(shape) => self.shape(shape).fields.iter().map(|(_, t)| *t).collect(),
            TyKind::Bool
            | TyKind::Int(_)
            | TyKind::Float(_)
            | TyKind::Void
            | TyKind::Never
            | TyKind::Str
            | TyKind::Param(_)
            | TyKind::Infer(_)
            | TyKind::Error => Vec::new(),
        }
    }

    /// Rebuilds `t` bottom-up: `f` may replace any type it is given, and a type it
    /// leaves (`None`) is rebuilt from its rebuilt children.
    pub fn map_ty(&self, t: Ty, f: &mut dyn FnMut(&Tcx, Ty) -> Option<Ty>) -> Ty {
        if let Some(replaced) = f(self, t) {
            return replaced;
        }
        let kind = match self.kind(t) {
            TyKind::Array(e) => TyKind::Array(self.map_ty(e, f)),
            TyKind::Fixed(e, n) => TyKind::Fixed(self.map_ty(e, f), n),
            TyKind::Slice(e) => TyKind::Slice(self.map_ty(e, f)),
            TyKind::Boxed(e) => TyKind::Boxed(self.map_ty(e, f)),
            TyKind::Nullable(e) => TyKind::Nullable(self.map_ty(e, f)),
            TyKind::Ref(e) => TyKind::Ref(self.map_ty(e, f)),
            TyKind::Raw(e) => TyKind::Raw(self.map_ty(e, f)),
            TyKind::Tuple(list) => TyKind::Tuple(self.map_list(list, f)),
            TyKind::Adt(adt, list) => TyKind::Adt(adt, self.map_list(list, f)),
            TyKind::FnPtr(abi, sig) => TyKind::FnPtr(abi, self.map_sig(sig, f)),
            TyKind::Closure(sig) => TyKind::Closure(self.map_sig(sig, f)),
            TyKind::Object(shape) => {
                let shape = self.shape(shape);
                let fields = shape
                    .fields
                    .iter()
                    .map(|&(name, t)| (name, self.map_ty(t, f)))
                    .collect();
                let optional = shape.optional.clone();
                TyKind::Object(self.intern_shape(Shape::with_optional(fields, optional)))
            }
            other => other,
        };
        self.intern_ty(kind)
    }

    fn map_list(&self, list: TyList, f: &mut dyn FnMut(&Tcx, Ty) -> Option<Ty>) -> TyList {
        let tys: Vec<Ty> = self.list(list).iter().map(|&t| self.map_ty(t, f)).collect();
        self.intern_list(&tys)
    }

    fn map_sig(&self, sig: FnSigId, f: &mut dyn FnMut(&Tcx, Ty) -> Option<Ty>) -> FnSigId {
        let sig = self.fn_sig(sig);
        let mapped = FnPtrSig {
            unsafety: sig.unsafety,
            params: sig
                .params
                .iter()
                .map(|&(t, mark)| (self.map_ty(t, f), mark))
                .collect(),
            ret: self.map_ty(sig.ret, f),
            ret_readonly: sig.ret_readonly,
        };
        self.intern_fn_sig(mapped)
    }

    /// Whether `pred` holds of `t` or of any type inside it.
    pub fn any_ty(&self, t: Ty, pred: &mut dyn FnMut(&Tcx, Ty) -> bool) -> bool {
        if pred(self, t) {
            return true;
        }
        self.children(t).into_iter().any(|c| self.any_ty(c, pred))
    }

    /// `t` with each `params[i]` replaced by `args[i]`.
    pub fn subst(&self, t: Ty, params: &[ParamId], args: &[Ty]) -> Ty {
        if params.is_empty() {
            return t;
        }
        self.map_ty(t, &mut |tcx, inner| match tcx.kind(inner) {
            TyKind::Param(p) => params.iter().position(|&q| q == p).map(|i| args[i]),
            _ => None,
        })
    }

    /// Structural equality ignoring the rows of function pointer and closure
    /// signatures (their marks and `readonly`) and which fields of an object type
    /// were written `x?: T` (D13): typing's notion of one type (N1).
    pub fn same_ignoring_rows(&self, a: Ty, b: Ty) -> bool {
        if a == b {
            return true;
        }
        match (self.kind(a), self.kind(b)) {
            (TyKind::Array(x), TyKind::Array(y))
            | (TyKind::Slice(x), TyKind::Slice(y))
            | (TyKind::Boxed(x), TyKind::Boxed(y))
            | (TyKind::Nullable(x), TyKind::Nullable(y))
            | (TyKind::Ref(x), TyKind::Ref(y))
            | (TyKind::Raw(x), TyKind::Raw(y)) => self.same_ignoring_rows(x, y),
            (TyKind::Fixed(x, n), TyKind::Fixed(y, m)) => n == m && self.same_ignoring_rows(x, y),
            (TyKind::Tuple(x), TyKind::Tuple(y)) => self.same_lists(x, y),
            (TyKind::Adt(p, x), TyKind::Adt(q, y)) => p == q && self.same_lists(x, y),
            (TyKind::FnPtr(abi1, x), TyKind::FnPtr(abi2, y)) => {
                abi1 == abi2 && self.same_sigs(x, y)
            }
            (TyKind::Closure(x), TyKind::Closure(y)) => self.same_sigs(x, y),
            (TyKind::Object(x), TyKind::Object(y)) => {
                let (x, y) = (self.shape(x), self.shape(y));
                x.fields.len() == y.fields.len()
                    && x.fields
                        .iter()
                        .zip(y.fields.iter())
                        .all(|((n, s), (m, t))| n == m && self.same_ignoring_rows(*s, *t))
            }
            _ => false,
        }
    }

    fn same_lists(&self, x: TyList, y: TyList) -> bool {
        let (x, y) = (self.list(x), self.list(y));
        x.len() == y.len()
            && x.iter()
                .zip(y.iter())
                .all(|(&a, &b)| self.same_ignoring_rows(a, b))
    }

    fn same_sigs(&self, x: FnSigId, y: FnSigId) -> bool {
        let (x, y) = (self.fn_sig(x), self.fn_sig(y));
        x.unsafety == y.unsafety
            && x.params.len() == y.params.len()
            && x.params
                .iter()
                .zip(y.params.iter())
                .all(|((a, _), (b, _))| self.same_ignoring_rows(*a, *b))
            && self.same_ignoring_rows(x.ret, y.ret)
    }

    /// Whether `t` mentions a type parameter.
    pub fn has_params(&self, t: Ty) -> bool {
        self.any_ty(t, &mut |tcx, inner| {
            matches!(tcx.kind(inner), TyKind::Param(_))
        })
    }

    /// Whether `t` mentions an inference variable.
    pub fn has_infer(&self, t: Ty) -> bool {
        self.any_ty(t, &mut |tcx, inner| {
            matches!(tcx.kind(inner), TyKind::Infer(_))
        })
    }

    /// Whether `t` is or contains `Error`.
    pub fn references_error(&self, t: Ty) -> bool {
        self.any_ty(t, &mut |tcx, inner| {
            matches!(tcx.kind(inner), TyKind::Error)
        })
    }
}

fn intern_kind(interner: &mut Interner, kind: TyKind) -> Ty {
    if let Some(&ty) = interner.ty_ids.get(&kind) {
        return ty;
    }
    let ty = Ty(u32::try_from(interner.kinds.len()).expect("types exceed u32"));
    interner.kinds.push(kind);
    interner.ty_ids.insert(kind, ty);
    ty
}

fn intern_list(interner: &mut Interner, ts: &[Ty]) -> TyList {
    if let Some(&id) = interner.list_ids.get(ts) {
        return id;
    }
    let id = TyList::new(interner.lists.len());
    let list: Arc<[Ty]> = Arc::from(ts);
    interner.lists.push(Arc::clone(&list));
    interner.list_ids.insert(list, id);
    id
}
