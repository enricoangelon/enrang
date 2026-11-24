//! `enrang targets --evidence`: the table of ARCHITECTURE 8.6 and TESTING 21.
//!
//! A class is printed only once a test result has reached it. Nothing has, because
//! no compiler exists, so there is nothing to read and every cell is one constant.

use enrang_diag::CURRENT_MILESTONE;

use crate::table::table;

/// A CPU family and the `--cpu` rung that covers it.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Family {
    pub name: &'static str,
    pub rung: &'static str,
    /// What its C4 cell reads. Most families have no chip anyone can test on.
    pub c4: &'static str,
}

const fn family(name: &'static str, rung: &'static str) -> Family {
    Family {
        name,
        rung,
        c4: NO_HARDWARE,
    }
}

/// A family with real hardware available to test on: the owner's Q8400, and the
/// development machine for `Newer` (SPEC 10.6).
const fn testable(name: &'static str, rung: &'static str) -> Family {
    Family {
        name,
        rung,
        c4: PLANNED,
    }
}

/// Every family, in the order of ARCHITECTURE 8.6.
pub const FAMILIES: &[Family] = &[
    family("i386, Am386", "i386"),
    family("i486, Am486, Am5x86", "i486"),
    family("Pentium, Pentium MMX", "i586"),
    family("K5", "i586"),
    family("K6, K6-2, K6-III", "i586"),
    family("Pentium Pro, II, III", "i686"),
    family("K7", "i686"),
    family("NetBurst", "sse2"),
    family("Intel mobile: Pentium M, Core Solo/Duo", "sse2"),
    family("Atom", "sse2; x86-64 on 64-bit parts"),
    testable("Core 2 Duo, Core 2 Quad, Q8400", "sse2, x86-64"),
    testable("Newer", "sse2, x86-64"),
];

/// The four classes of SPEC 10.6.
pub const CLASSES: [&str; 4] = ["C1", "C2", "C3", "C4"];

/// What a class reads while nothing has reached it.
const PLANNED: &str = "planned";

/// What C4 reads for a family with no chip to test on.
pub const NO_HARDWARE: &str = "no hardware";

pub(crate) fn text() -> String {
    let mut rows = vec![vec!["family".to_owned(), "rung".to_owned()]];
    rows[0].extend(CLASSES.map(str::to_owned));
    for family in FAMILIES {
        let mut row = vec![family.name.to_owned(), family.rung.to_owned()];
        row.extend(["C1", "C2", "C3"].map(|_| PLANNED.to_owned()));
        row.push(family.c4.to_owned());
        rows.push(row);
    }
    format!(
        "Support evidence per CPU family. A class is printed only once it is reached.

{table}
Nothing has been achieved: this is milestone {CURRENT_MILESTONE}, which generates no code, and no
chip has run any Enrang output. `{NO_HARDWARE}` means no such chip is available to test on.

C1  level-proven: encoder tags, assembler oracle, disassembly audit, single-step
    classification
C2  run at that level on the development host, which proves the code, not the chip
C3  emulated, naming the model
C4  real hardware, only from the owner's report
",
        table = table(&rows),
    )
}
