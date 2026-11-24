//! Running `load` and `analyze` on in-memory programs, with a small fake library or
//! the embedded one, and reading the result: diagnostics, rendered as the command
//! line renders them, and the `Tcx` the declarations were lowered into.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::Arc;

use enrang_base::SourceMap;
use enrang_diag::{DiagCtx, Diagnostic, RenderOpts, render_text};
use enrang_hir::{CheckedProgram, DefId, Mark, Receiver, Tcx};
use enrang_sema::{LibSource, LoadError, ProgramInput, analyze, load};
use enrang_syntax::{NodeIdGen, ParseMode};
use enrang_target::{TargetOpts, resolve};

/// A minimal library with the lang items the cases name: `string`, `Slice<T>`,
/// `Copy`, `Clone`, `Error`, `Failure`, `Result<T, E>` and `Ok` in `core`, `T[]`'s class and
/// `Box<T>` in `alloc`, and an `extend` on nullables.
pub const MINI_LIB: &[(&str, &str)] = &[
    (
        "core/prelude",
        "// A fake core prelude for the sema suite.
public import { Option } from \"./option\";
@lang(\"string\") public final class string {
  private ptr: usize;
  public length(): isize;
}
@lang(\"slice\") public final class Slice<T> {
  private ptr: usize;
  public length(): isize;
}
@lang(\"copy\") public interface Copy {}
@lang(\"clone\") public interface Clone {
  clone(): Self;
}
@lang(\"error\") public interface Error {}
@lang(\"failure\") public final class Failure {
  private text: string;
}
@lang(\"result\") public enum Result<T, E> { Ok { value: T }, Err { error: E } }
@lang(\"ok\") public function Ok<T, E>(value: T): Result<T, E> { unreachable(); }
",
    ),
    (
        "core/option",
        "// Members of nullables.
public interface Option {}
extend<T> T | null {
  public unwrapOr(d: T): T;
}
",
    ),
    (
        "alloc/prelude",
        "// A fake alloc prelude.
@lang(\"array\") public final class Array<T> {
  private ptr: usize;
  public let push(x: T): void;
}
@lang(\"box\") public final class Box<T> {
  private ptr: usize;
}
",
    ),
    ("os/linux_x64/prelude", "// Empty.\n"),
];

/// The fake library of `modules`.
pub fn fake_lib(modules: &[(&str, &str)]) -> LibSource {
    LibSource::Fake(
        modules
            .iter()
            .map(|(key, text)| ((*key).to_owned(), Arc::from(*text)))
            .collect::<BTreeMap<String, Arc<str>>>(),
    )
}

/// What a run produced.
pub struct Run {
    pub map: Arc<SourceMap>,
    pub tcx: Tcx,
    /// `None` when phase 1 or phase 2 stopped.
    pub program: Option<CheckedProgram>,
    pub diags: Vec<Diagnostic>,
}

impl Run {
    /// The diagnostics as `enrang check` prints them, without colour.
    pub fn rendered(&self) -> String {
        render_text(&self.diags, &self.map, &RenderOpts { color: false })
    }

    /// The codes reported, in order.
    pub fn codes(&self) -> Vec<String> {
        self.diags
            .iter()
            .map(|d| d.code.name().to_owned())
            .collect()
    }

    /// The messages reported, in order.
    pub fn messages(&self) -> Vec<String> {
        self.diags.iter().map(|d| d.message.clone()).collect()
    }

    /// Asserts nothing was reported.
    pub fn clean(&self) -> &Run {
        assert!(self.diags.is_empty(), "{}", self.rendered());
        assert!(self.program.is_some());
        self
    }

    /// The definition whose path prints as `path` (`src/main::Stack::push`).
    pub fn def(&self, path: &str) -> DefId {
        self.tcx
            .defs()
            .find(|(_, d)| d.path.to_string() == path)
            .map(|(def, _)| def)
            .unwrap_or_else(|| {
                let known: Vec<String> = self
                    .tcx
                    .defs()
                    .filter(|(_, d)| d.path.module.as_str().starts_with("src"))
                    .map(|(_, d)| d.path.to_string())
                    .collect();
                panic!("no definition `{path}` among {known:?}")
            })
    }

    /// A signature as `(this, a: i64, b?: int | null) => void`.
    pub fn sig(&self, path: &str) -> String {
        let def = self.def(path);
        let sig = self.tcx.sig(def);
        let mut parts = Vec::new();
        match sig.receiver {
            Some(Receiver::Ref(Mark::None)) => parts.push("this".to_owned()),
            Some(Receiver::Ref(Mark::Let)) => parts.push("let this".to_owned()),
            Some(Receiver::Ref(Mark::Const)) => parts.push("const this".to_owned()),
            Some(Receiver::Move) => parts.push("move this".to_owned()),
            Some(Receiver::Static) => parts.push("static".to_owned()),
            None => {}
        }
        for p in &sig.params {
            let mark = match p.mark {
                Mark::None => "",
                Mark::Let => "let ",
                Mark::Const => "const ",
            };
            let default = if p.has_default { "?" } else { "" };
            parts.push(format!(
                "{mark}{}{default}: {}",
                p.name,
                self.tcx.ty_string(p.ty)
            ));
        }
        let readonly = if sig.ret_readonly { "readonly " } else { "" };
        format!(
            "({}) => {readonly}{}",
            parts.join(", "),
            self.tcx.ty_string(sig.ret)
        )
    }
}

/// Checks the program of `sources`, the first being the entry, with the fake
/// library, in `ParseMode::Test`.
pub fn run(sources: &[(&str, &str)]) -> Run {
    run_with(sources, fake_lib(MINI_LIB), "x86_64-linux")
}

/// Checks `sources` with `lib` for `target`.
pub fn run_with(sources: &[(&str, &str)], lib: LibSource, target: &str) -> Run {
    run_entry(sources, lib, target, false)
}

/// [`run_with`], with the entry loaded as a library module when `library_entry`
/// (a compile fixture's `//! library`, G50).
pub fn run_entry(
    sources: &[(&str, &str)],
    lib: LibSource,
    target: &str,
    library_entry: bool,
) -> Run {
    let input = ProgramInput {
        entry: PathBuf::from(sources[0].0),
        mode: ParseMode::Test,
        overrides: sources
            .iter()
            .map(|(path, text)| (PathBuf::from(path), Arc::from(*text)))
            .collect(),
        dir: PathBuf::from("/nonexistent/enrang-sema-suite"),
        lib,
        library_entry,
    };
    run_input(input, target)
}

/// Checks the file `entry` of the directory `dir` on disk, with the embedded
/// library, for `x86_64-linux`.
pub fn run_in(dir: &std::path::Path, entry: &str) -> Run {
    let input = ProgramInput {
        entry: PathBuf::from(entry),
        mode: ParseMode::Test,
        overrides: BTreeMap::new(),
        dir: dir.to_path_buf(),
        lib: LibSource::Embedded,
        library_entry: false,
    };
    run_input(input, "x86_64-linux")
}

/// Loads and analyzes `input` for `target`.
fn run_input(input: ProgramInput, target: &str) -> Run {
    let (spec, _) = resolve(target, &TargetOpts::default()).expect("a target");
    let mut map = SourceMap::new();
    let mut ids = NodeIdGen::new();
    let mut dcx = DiagCtx::new();
    let loaded = match load(&input, &spec, &mut map, &mut ids, &mut dcx) {
        Ok(program) => Some(program),
        Err(LoadError::Aborted(_)) => None,
        Err(LoadError::Unreadable { path, error }) => panic!("{}: {error}", path.display()),
    };
    let map = Arc::new(map);
    let mut tcx = Tcx::new(Arc::new(spec), Arc::clone(&map));
    let program = loaded.and_then(|p| analyze(&p, &mut tcx, &mut dcx).ok());
    let diags = dcx.take();
    Run {
        map,
        tcx,
        program,
        diags,
    }
}
