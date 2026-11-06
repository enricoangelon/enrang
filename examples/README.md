# Examples

> [!IMPORTANT]
> **None of these can run yet, because there is no compiler.** They are written against [the language reference](../docs/SPEC.md) and reviewed by reading them against it. The expected output of `hello`, `ownership`, `rpn` and `leaderboard` was worked out by hand and cross-checked with throwaway Rust programs, not with Enrang. The first compiler to read them will be their first real test, and any disagreement will be a bug in them or in it.

`name.stdout` and `name.stderr` hold the exact bytes a program must print. `enrang run` arrives with M4 for the VM (`--vm`) and with M5 natively. The [milestones](../docs/ARCHITECTURE.md#12-milestones) say what each one delivers.

| Example | What it shows | Can run from |
|---|---|---|
| [`hello.en`](hello.en) | The smallest program | M4 |
| [`ownership.en`](ownership.en) | Handing over, lending, and when a value ends | M4 |
| [`rpn.en`](rpn.en) | Enums, `match`, `Result` and `?`, in a small calculator | M4 |
| [`leaderboard.en`](leaderboard.en) | Classes, interfaces, generics and closures | M4 |
| [`testing/`](testing) | Tests in the language, including tests that code must not compile | M4 |
| [`mistakes/`](mistakes) | Programs that must not compile, and what the compiler says | M1 to M3 |
| [`hot-reload/`](hot-reload) | Changing a program while it runs | M6 |
| [`kernel/`](kernel) | A kernel that boots on a PC | M9 |

## Mistakes

These are the spec's own golden diagnostics, with only the file name changed. M0's renderer already prints them from hand-built errors. The milestone below is when the compiler finds each mistake by itself, with `enrang check <file>`.

| Program | The mistake | Code | From |
|---|---|---|---|
| [`typescript-habits.en`](mistakes/typescript-habits.en) | `any`, `var` and `undefined`, which don't exist here | [EN0205, EN0202, EN0206](mistakes/typescript-habits.stderr) | M1 |
| [`missing-case.en`](mistakes/missing-case.en) | A `match` that forgets one variant | [EN0501](mistakes/missing-case.stderr) | M2 |
| [`use-after-move.en`](mistakes/use-after-move.en) | Using a value after handing it over | [EN0601](mistakes/use-after-move.stderr) | M3 |
| [`changed-in-a-loop.en`](mistakes/changed-in-a-loop.en) | Growing an array while still holding one of its items | [EN0706](mistakes/changed-in-a-loop.stderr) | M3 |
| [`dangling-reference.en`](mistakes/dangling-reference.en) | Returning a reference to a local | [EN0710](mistakes/dangling-reference.stderr) | M3 |

## Tests

[`testing/inventory.test.en`](testing/inventory.test.en) tests [`testing/inventory.en`](testing/inventory.en). Run it with `enrang test --ci inventory.test.en` from that directory, and the output must equal [`inventory.test.stdout`](testing/inventory.test.stdout). `--ci` removes timings. The last test is a `compileFails`: it passes only if the snippet is rejected with exactly the code on its `//~` line.

## Hot reload

[`hot-reload/server.en`](hot-reload/server.en) is the worked scenario of [DEV_RUNTIME.md section 11](../docs/DEV_RUNTIME.md#11-worked-scenario), which has the full transcript. That transcript is a design target, because nothing there has run. Start it with `enrang dev server.en`, then make these edits while it runs:

1. **Change the data.** Add `level: i32 = 1;` to `Player`. After the score line, add `if (g.players[who].score % 30 == 0) { g.players[who].level += 1; }`, and print `L${g.players[who].level}` in the log line. The two live players gain the field, and the game keeps its state.
2. **Break it.** Before the `+= 10` line, add `const rival = who + 1;` and `g.players[rival].score -= 1;`. Soon the index runs off the end. The program pauses with its state intact instead of dying.
3. **Fix it.** Change the first of those lines to `const rival = (who + 1) % g.players.length;`, and save. The failed call is undone and retried with the new code, and nothing else is lost.

## Kernel

[`kernel/family-pc.en`](kernel/family-pc.en) boots, prints the CPU vendor, the CPU level and the usable memory to the screen and to COM1, and halts. Build it with:

```sh
enrang build --target=i386-none --image=hdd family-pc.en
```

`--image=floppy` makes a 1,474,560-byte floppy image instead. [TESTING.md section 19](../docs/TESTING.md#19-how-windows-i386-and-boot-tests-run-here) has the checklist for writing the image to a USB stick and booting it on a Core 2 board. This program has no `.stdout` file because its output depends on the machine, and it has never booted anywhere. The target arrives with M9, and `enrang targets --evidence` will say what has really been run on which chip.
