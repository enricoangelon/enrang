//! `enrang check --emit=mir` and `--emit=summary` (M3 plan b.11, departure D23):
//! the text a checked program prints on stdout.
//!
//! `mir` is the elaborated MIR of every user body, each verified again after
//! elaboration, printed through `print_module` one user module at a time in
//! topological order, each module's bodies in owner order (plan choice: elaborated
//! MIR shows drop order, flags and ladders; interface files store the built MIR).
//! `summary` is `borrowck::summary::render` of every user module in the same
//! order: each function, method and constructor with its contract, each borrowing
//! class with its flag, and their witnesses.

use enrang_hir::Tcx;
use enrang_mir::{Body, print_module, verify};

use crate::Checked;
use crate::phase3::{Internal, owner_name};

/// What `--emit=` prints.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Emit {
    Mir,
    Summary,
}

impl Emit {
    /// The values `check --emit=` takes, as written.
    pub const VALUES: [&'static str; 2] = ["mir", "summary"];

    /// The value named `name`, if `check` takes it.
    pub fn from_name(name: &str) -> Option<Emit> {
        match name {
            "mir" => Some(Emit::Mir),
            "summary" => Some(Emit::Summary),
            _ => None,
        }
    }
}

/// The text `--emit=what` prints for a program that passed `check`.
pub fn emit(checked: &Checked, what: Emit) -> Result<String, Internal> {
    match what {
        Emit::Mir => mir(checked),
        Emit::Summary => Ok(summary(checked)),
    }
}

/// Every user body elaborated (A:595-605) and verified again, module by module.
fn mir(checked: &Checked) -> Result<String, Internal> {
    let tcx = &checked.tcx;
    let mut out = String::new();
    for (_, owners) in &checked.modules {
        let bodies: Vec<Body> = (owners.iter())
            .map(|owner| {
                let facts = &checked.facts[owner];
                enrang_borrowck::elaborate_drops(tcx, checked.mir[owner].clone(), facts)
            })
            .collect();
        if bodies.is_empty() {
            continue;
        }
        if !out.is_empty() {
            out.push('\n');
        }
        out.push_str(&print_elaborated(tcx, &bodies)?);
    }
    Ok(out)
}

/// One module's elaborated `bodies`, each verified again, printed: elaborated MIR
/// that fails the verifier is a bug in the compiler, [`Internal`], and is never
/// printed.
pub fn print_elaborated(tcx: &Tcx, bodies: &[Body]) -> Result<String, Internal> {
    for b in bodies {
        if let Err(errors) = verify(tcx, b) {
            let shown: Vec<String> = errors.iter().map(|e| e.to_string()).collect();
            return Err(Internal(format!(
                "the elaborated MIR of `{}` fails the verifier: {}",
                owner_name(tcx, b.owner),
                shown.join("; ")
            )));
        }
    }
    Ok(print_module(tcx, bodies))
}

/// Every user module's contracts, flags and witnesses.
fn summary(checked: &Checked) -> String {
    let mut out = String::new();
    for (module, _) in &checked.modules {
        if !out.is_empty() {
            out.push('\n');
        }
        out.push_str(&enrang_borrowck::summary::render(
            &checked.tcx,
            &checked.contracts,
            *module,
        ));
    }
    out
}
