//! Contract inference over a large SCC (A:1349, A:1354): stages 2 and 3 only grow
//! and stage 4 only falls, so both loops run to their fixed point, however many
//! rounds the visit order costs. Each program is an 80-function cycle in which
//! the fact that matters starts at the last function in ItemPath order and moves
//! back one function per round; a round cap below that (64 before this fix)
//! stopped early and left `f00` writable or storing nothing, a hole each case
//! pins.

use enrang_testkit::Harness;

const N: usize = 80;

/// Stage 4: `f79` returns a `readonly` result and each `fI` returns `fI+1`'s,
/// so `f00`'s result is read-only and writing through it is EN0614 at line 3.
fn read_only_chain() -> String {
    let mut s =
        String::from("let a: i64[] = [1];\nconst r = f00(&a);\nr.push(2);\nconsole.log(a);\n\n");
    for i in 0..N - 1 {
        s += &format!(
            "private function f{i:02}(x: &i64[]): &i64[] {{ return f{:02}(x); }}\n",
            i + 1
        );
    }
    s += &format!(
        "private function f{:02}(x: &i64[]): readonly &i64[] {{ if (x.length() > 100) {{ f00(x); }} return x; }}\n",
        N - 1
    );
    s
}

/// Stage 2: `f79` stores `s` into `c` and each `fI` passes both on, so `f00`
/// stores `(2, 1)`, and the block's `t` dropped while `h` holds it is EN0711
/// at line 6.
fn store_chain() -> String {
    let mut s = String::from(
        "let base = \"b\".toString();\nlet h = new Holder(&base);\n{\n  const t = \"x\".toString();\n  f00(&h, &t);\n}\nconsole.log(h.get());\n\n",
    );
    for i in 0..N - 1 {
        s += &format!(
            "private function f{i:02}(c: &Holder, s: &string): void {{ f{:02}(c, s); }}\n",
            i + 1
        );
    }
    s += &format!(
        "private function f{:02}(c: &Holder, s: &string): void {{ if (s.length() > 100) {{ f00(c, s); }} c.setSrc(s); }}\n",
        N - 1
    );
    s += "\nprivate class Holder {\n  private src: &string;\n  public constructor(s: &string) { this.src = s; }\n  public setSrc(s: &string): void { this.src = s; }\n  public get(): readonly &string { return this.src; }\n}\n";
    s
}

pub fn register(h: &mut Harness) {
    h.case(
        "scc/stage 4 runs to its fixed point over an 80-function cycle",
        || {
            assert_eq!(
                crate::support::phase3(&read_only_chain()),
                [("EN0614".to_owned(), 3)]
            );
        },
    );
    h.case(
        "scc/stage 2 runs to its fixed point over an 80-function cycle",
        || {
            assert_eq!(
                crate::support::phase3(&store_chain()),
                [("EN0711".to_owned(), 6)]
            );
        },
    );
    h.case(
        "scc/the near misses compile: no write, and `t` outlives `h`",
        || {
            let ro = read_only_chain().replace("r.push(2);", "console.log(r);");
            assert_eq!(crate::support::phase3(&ro), []);
            let st = store_chain().replace(
                "{\n  const t = \"x\".toString();\n  f00(&h, &t);\n}\n",
                "const t = \"x\".toString();\nf00(&h, &t);\n",
            );
            assert_eq!(crate::support::phase3(&st), []);
        },
    );
}
