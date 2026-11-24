//! Spellings the reader accepts but the printer never writes (`int`, `user`,
//! `phase built`, numeric field and case names, hex numbers, `Result<T>`, `//~`
//! anchors, `instantiate`), and the reader's errors with their positions, each
//! pinned in `spellings.txt` as `==== name`, the text, then `---- outcome` and the
//! module printed back or `ERR line:col message`. Fixtures that other stages write
//! by hand may use any of them.

use enrang_mir::{parse_module, print_module};
use enrang_testkit::Harness;

use crate::support::dir;

/// What reading `text` gives: the module printed back, or the error.
fn outcome(text: &str) -> String {
    match parse_module(text) {
        Ok((tcx, bodies)) => print_module(&tcx, &bodies),
        Err(e) => format!("ERR {}:{} {}", e.line, e.col, e.message),
    }
}

pub fn register(h: &mut Harness) {
    let text = std::fs::read_to_string(dir("spellings.txt")).expect("the pins");
    for case in text.split("==== ").skip(1) {
        let (name, rest) = case.split_once('\n').expect("a name line");
        let (input, want) = rest.split_once("---- outcome\n").expect("an outcome");
        let (name, input, want) = (name.to_owned(), input.to_owned(), want.to_owned());
        h.case(format!("spellings/{name}: reads as pinned"), move || {
            assert_eq!(format!("{}\n", outcome(&input)), want, "{input}");
        });
    }
}
