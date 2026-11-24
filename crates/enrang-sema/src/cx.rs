//! The per-run context of phase 2: the `Tcx` being filled, the diagnostics, the
//! loaded program, and one state struct per area, each defined in its area's file
//! (plan h.2).

use std::collections::BTreeMap;
use std::sync::Arc;

use enrang_base::Span;
use enrang_diag::{Code, DiagCtx, Diagnostic};
use enrang_hir::{
    AdtId, Body, BodyOwner, CheckedProgram, DefId, Entry, FieldInits, LocalKind, ModuleId,
    SatisfactionRecord, Tcx, TestItem, TopVar, TopVarInfo, Ty,
};

use crate::classes::ClassTables;
use crate::consteval::ConstState;
use crate::load::LoadedProgram;
use crate::lower::DeclTables;
use crate::passes::views::ViewUses;
use crate::resolve::ResolveTables;

/// The run context. `program` and the AST inside it outlive the run, so the
/// declaration tables keep references into it for the bodies typed later.
pub(crate) struct Sema<'a> {
    pub tcx: &'a mut Tcx,
    pub dcx: &'a mut DiagCtx,
    pub program: &'a LoadedProgram,
    pub res: ResolveTables,
    pub decls: DeclTables<'a>,
    // The state of const eval (2E, 4F) and the view facts (4E), unread until those
    // stages fill them, and the errors the class checks already reported (4D).
    #[allow(dead_code)]
    pub consts: ConstState,
    pub classes: ClassTables,
    #[allow(dead_code)]
    pub views: ViewUses,
    pub bodies: BTreeMap<DefId, Arc<Body>>,
    pub statements: Option<Arc<Body>>,
    pub field_inits: BTreeMap<AdtId, FieldInits>,
    /// The whole typed body of each class's field initialisers, arrows included,
    /// for the passes over every body (the view facts read it).
    pub field_init_bodies: BTreeMap<AdtId, Arc<Body>>,
    pub tests: Vec<TestItem>,
    /// Set by `entry::check`.
    pub entry: Entry,
    /// Unannotated constants typed on demand, from a use typed before their own
    /// turn, waiting for that turn's passes (`typeck::const_ty`).
    pub early_consts: BTreeMap<DefId, Body>,
    /// The unannotated constants being typed on demand, outermost first, which a
    /// cycle among their initialisers is read from (EN0412).
    pub typing_consts: Vec<DefId>,
}

impl<'a> Sema<'a> {
    /// The context of one run; defines every loaded module in `tcx`, in load order.
    pub fn new(tcx: &'a mut Tcx, dcx: &'a mut DiagCtx, program: &'a LoadedProgram) -> Sema<'a> {
        let mut res = ResolveTables::default();
        crate::resolve::define_modules(tcx, program, &mut res);
        Sema {
            tcx,
            dcx,
            program,
            res,
            decls: DeclTables::default(),
            consts: ConstState::default(),
            classes: ClassTables::default(),
            views: ViewUses::default(),
            bodies: BTreeMap::new(),
            statements: None,
            field_inits: BTreeMap::new(),
            field_init_bodies: BTreeMap::new(),
            tests: Vec::new(),
            entry: Entry::None,
            early_consts: BTreeMap::new(),
            typing_consts: Vec::new(),
        }
    }

    /// Reports what loading recorded for phase 2 (EN0305).
    pub fn emit_pending(&mut self) {
        for diag in &self.program.pending {
            self.dcx.emit(diag.clone());
        }
    }

    /// Emits an error with its primary label.
    pub fn err(
        &mut self,
        code: Code,
        msg: impl Into<String>,
        span: Span,
        label: impl Into<String>,
    ) {
        self.dcx.emit(Diagnostic::new(code, msg, span, label));
    }

    /// Emits a built diagnostic.
    pub fn emit(&mut self, diag: Diagnostic) {
        self.dcx.emit(diag);
    }

    /// `t` as messages spell it (`Tcx::ty_string`).
    #[allow(dead_code)] // For the typing stages' messages.
    pub fn ty_str(&self, t: Ty) -> String {
        self.tcx.ty_string(t)
    }

    /// The module of a loaded module index.
    pub fn module_id(&self, index: usize) -> ModuleId {
        self.res.modules[index]
    }

    /// Keeps a finished body.
    pub fn store_body(&mut self, owner: BodyOwner, body: Body) {
        let body = Arc::new(body);
        match owner {
            BodyOwner::Statements(_) => self.statements = Some(body),
            BodyOwner::Fn(def) | BodyOwner::Const(def) | BodyOwner::Test(def) => {
                self.bodies.insert(def, body);
            }
        }
    }

    /// The checked program, modules in `order`, with what phase 3 reads beside the
    /// bodies (M3 plan K6, K7): the recorded satisfactions, one per member found and
    /// interface member, the first by site, sorted by the paths of both; each local
    /// function's hidden arguments; and the top-level variables with the types and
    /// mutability their locals in the statements have.
    pub fn finish(self, order: Vec<ModuleId>) -> CheckedProgram {
        let mut firsts: BTreeMap<(DefId, DefId), &crate::classes::satisfy::Satisfaction> =
            BTreeMap::new();
        for s in &self.classes.satisfactions {
            let kept = firsts.entry((s.found, s.member)).or_insert(s);
            if s.site < kept.site {
                *kept = s;
            }
        }
        let mut satisfactions: Vec<SatisfactionRecord> = firsts
            .into_values()
            .map(|s| SatisfactionRecord {
                ty: s.ty,
                iface: s.iface,
                member: s.member,
                found: s.found,
                site: s.site,
            })
            .collect();
        let tcx = &*self.tcx;
        satisfactions.sort_by(|a, b| {
            let key = |r: &SatisfactionRecord| (&tcx.def(r.found).path, &tcx.def(r.member).path);
            key(a).cmp(&key(b))
        });
        let top = &self.res.toplevel;
        let error = tcx.common().error;
        let top_vars = top
            .vars
            .iter()
            .enumerate()
            .map(|(i, var)| {
                let local = self.statements.as_ref().and_then(|body| {
                    body.locals
                        .iter()
                        .find(|l| matches!(l.kind, LocalKind::TopVar(v) if v == TopVar(i as u32)))
                });
                TopVarInfo {
                    name: var.name,
                    ty: local.map_or(error, |l| l.ty),
                    mutable: local.is_some_and(|l| l.mutable),
                    span: var.span,
                }
            })
            .collect();
        let hidden_args = top.hidden.clone();
        CheckedProgram {
            modules: order,
            entry: self.entry,
            bodies: self.bodies,
            statements: self.statements,
            field_inits: self.field_inits,
            tests: self.tests,
            satisfactions,
            hidden_args,
            top_vars,
        }
    }
}
