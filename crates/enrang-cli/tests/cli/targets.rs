//! `enrang targets` against the tables of `enrang-target` and SPEC 10.1.

use enrang_diag::Code;
use enrang_target::{CPU_ALIASES, CodeMode, TargetOpts, all_targets, resolve};
use enrang_testkit::Harness;

use crate::support::{inproc, table_rows};

const TARGETS: &str = "Targets:";
const LEVELS: &str = "CPU levels, the values --cpu will take:";
const ALIASES: &str = "CPU aliases, which --cpu will accept in place of a level:";

fn listing() -> String {
    let outcome = inproc(&["targets"]);
    assert_eq!(outcome.code, 0);
    assert_eq!(outcome.stderr, "");
    outcome.stdout
}

fn opts_with_cpu(cpu: &str) -> TargetOpts {
    TargetOpts {
        cpu: Some(cpu.to_owned()),
        ..TargetOpts::default()
    }
}

pub fn register(h: &mut Harness) {
    h.case("targets/lists every target once, in table order", || {
        let rows = table_rows(&listing(), TARGETS);
        let names: Vec<&str> = rows[1..].iter().map(|row| row[0].as_str()).collect();
        assert_eq!(names, all_targets());
    });
    for &name in all_targets() {
        h.case(
            format!("targets/row of {name} matches its spec"),
            move || {
                let rows = table_rows(&listing(), TARGETS);
                let row = rows
                    .iter()
                    .find(|row| row[0] == name)
                    .expect("the target has a row");
                let (spec, notes) = resolve(name, &TargetOpts::default()).expect("it resolves");
                assert!(notes.is_empty());
                assert_eq!(row.len(), 7, "{row:?}");
                let is_vm = name.starts_with("vm");
                let code = match (is_vm, spec.code_mode) {
                    (true, _) => "vm",
                    (false, CodeMode::M32) => "i386",
                    (false, CodeMode::M64) => "x86-64",
                };
                assert_eq!(row[1], code);
                assert_eq!(row[2], format!("{} bytes", spec.layout.ptr_bytes));
                let level = if is_vm { "none" } else { spec.cpu.name() };
                assert_eq!(row[3], level);
                assert_eq!(row[4], spec.float.name());
            },
        );
    }
    h.case("targets/each target's output and os, by hand", || {
        let rows = table_rows(&listing(), TARGETS);
        let expected: &[(&str, &str, &str)] = &[
            ("x86_64-linux", "elf64", "linux"),
            ("x86_64-windows", "pe32+", "windows"),
            ("i386-linux", "elf32", "linux, int 0x80"),
            ("i386-none", "flat", "none"),
            ("x86_64-none", "flat", "none"),
            ("vm64", "none", "vm"),
            ("vm32", "none", "vm"),
        ];
        assert_eq!(rows.len() - 1, expected.len());
        for ((name, output, os), row) in expected.iter().zip(&rows[1..]) {
            assert_eq!(row[0], *name);
            assert_eq!(row[5], *output, "{name}");
            assert_eq!(row[6], *os, "{name}");
        }
    });
    h.case("targets/the levels are those of SPEC 10.1, by hand", || {
        let rows = table_rows(&listing(), LEVELS);
        let baseline = "fpu cpuid bswap cmpxchg xadd cmpxchg8b rdtsc msr cr4 cmov fcomi sse sse2 fxsave nopl pae lm invlpg";
        let expected: &[(&str, &str, &str)] = &[
            ("i386", "i386-*", "80386 integer only"),
            ("i486", "i386-*", "+ bswap cmpxchg xadd invlpg"),
            ("i586", "i386-*", "+ cpuid cmpxchg8b rdtsc msr cr4"),
            ("i686", "i386-*", "+ cmov fcomi"),
            ("sse2", "i386-*", "+ sse sse2 fxsave"),
            ("x86-64", "x86_64-*", baseline),
        ];
        assert_eq!(rows.len() - 1, expected.len());
        for ((level, targets, assume), row) in expected.iter().zip(&rows[1..]) {
            assert_eq!(row[0], *level);
            assert_eq!(row[1], *targets, "{level}");
            assert_eq!(row[2], *assume, "{level}");
        }
    });
    h.case(
        "targets/no level names a feature the x86-64 baseline bans",
        || {
            let rows = table_rows(&listing(), LEVELS);
            let x86_64 = rows.last().expect("a row");
            assert_eq!(x86_64[0], "x86-64");
            for banned in ["cmpxchg16b", "lahf", "sahf", "popcnt", "sse3"] {
                assert!(!x86_64[2].contains(banned), "{banned}");
            }
        },
    );
    h.case("targets/lists every alias once, in SPEC order", || {
        let rows = table_rows(&listing(), ALIASES);
        let names: Vec<&str> = rows[1..].iter().map(|row| row[0].as_str()).collect();
        let expected: Vec<&str> = CPU_ALIASES.iter().map(|alias| alias.name).collect();
        assert_eq!(names, expected);
        assert_eq!(names.len(), 21);
    });
    for alias in CPU_ALIASES {
        let name = alias.name;
        h.case(
            format!("targets/alias {name} agrees with the resolver"),
            move || {
                let rows = table_rows(&listing(), ALIASES);
                let row = rows
                    .iter()
                    .find(|row| row[0] == name)
                    .expect("the alias has a row");
                let (on_32, _) = resolve("i386-linux", &opts_with_cpu(name)).expect("it resolves");
                assert_eq!(row[1], on_32.cpu.name());
                match resolve("x86_64-linux", &opts_with_cpu(name)) {
                    Ok((on_64, notes)) => {
                        assert!(row[2].starts_with(on_64.cpu.name()), "{row:?}");
                        let some_models = row[2].ends_with(", 64-bit models only");
                        let says_so = notes
                            .iter()
                            .any(|note| note.message.contains("64-bit models"));
                        assert_eq!(some_models, says_so, "{row:?} {notes:?}");
                    }
                    Err(diag) => {
                        assert_eq!(diag.code, Code::EN0912);
                        assert_eq!(row[2], "EN0912, no long mode");
                    }
                }
            },
        );
    }
    h.case("targets/the aliases of SPEC 10.1, by hand", || {
        let expected: &[(&str, &str, &str)] = &[
            ("386", "i386", "EN0912, no long mode"),
            ("am386", "i386", "EN0912, no long mode"),
            ("486", "i486", "EN0912, no long mode"),
            ("am486", "i486", "EN0912, no long mode"),
            ("am5x86", "i486", "EN0912, no long mode"),
            ("pentium", "i586", "EN0912, no long mode"),
            ("k5", "i586", "EN0912, no long mode"),
            ("k6", "i586", "EN0912, no long mode"),
            ("k6-2", "i586", "EN0912, no long mode"),
            ("k6-3", "i586", "EN0912, no long mode"),
            ("pentiumpro", "i686", "EN0912, no long mode"),
            ("p2", "i686", "EN0912, no long mode"),
            ("p3", "i686", "EN0912, no long mode"),
            ("k7", "i686", "EN0912, no long mode"),
            ("athlon-xp", "i686", "EN0912, no long mode"),
            ("p4", "sse2", "x86-64, 64-bit models only"),
            ("pentium-m", "sse2", "EN0912, no long mode"),
            ("core-duo", "sse2", "EN0912, no long mode"),
            ("atom", "sse2", "x86-64, 64-bit models only"),
            ("core2", "sse2", "x86-64"),
            ("q8400", "sse2", "x86-64"),
        ];
        let rows = table_rows(&listing(), ALIASES);
        assert_eq!(rows.len() - 1, expected.len());
        for ((alias, on_32, on_64), row) in expected.iter().zip(&rows[1..]) {
            assert_eq!(row[0], *alias);
            assert_eq!(row[1], *on_32, "{alias}");
            assert_eq!(row[2], *on_64, "{alias}");
        }
    });
    h.case("targets/the listing says nothing can be built", || {
        let text = listing();
        assert!(
            text.ends_with(
                "These are design tables. This is milestone M0, which has no compiler, so nothing\ncan be built for any target yet.\n"
            ),
            "{text}"
        );
    });
    h.case("targets/no line ends in white space", || {
        for args in [&["targets"][..], &["targets", "--evidence"][..]] {
            for line in inproc(args).stdout.lines() {
                assert_eq!(line, line.trim_end(), "{args:?}");
            }
        }
    });
}
