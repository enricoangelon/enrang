//! Scenarios run in a child process, one per value of `ENRANG_TESTKIT_CHILD`.

use std::env;
use std::io;
use std::panic;
use std::process::ExitCode;
use std::sync::Arc;
use std::thread;
use std::time::Duration;

use enrang_testkit::{
    BlessMode, GoldenStore, Harness, Rng, RunOptions, TempDir, catch_panic, golden, golden_in,
    rng_for, scale, scaled, seed, skip, skip_oracle, tool,
};

pub fn run(scenario: &str) -> ExitCode {
    match scenario {
        "all_pass" => all_pass(),
        "mixed" => mixed(),
        "empty" => Harness::new("empty").run(),
        "seed_scale" => seed_scale(),
        "seed_direct" => seed_direct(),
        "scale_direct" => scale_direct(),
        "skip_demo" => skip_demo(),
        "golden_env" => golden_env(),
        "speed" => speed(),
        "tool_probe" => tool_probe(),
        "default_store_orphans" => default_store_orphans(),
        "default_store_mismatch" => default_store_mismatch(),
        "golden_in_env" => golden_in_env(),
        "one_skip" => one_skip(),
        "run_options" => run_options(),
        "other_thread_panic" => other_thread_panic(),
        "foreign_hook" => foreign_hook(),
        "temp_dir" => temp_dir(),
        other => panic!("unknown child scenario `{other}`"),
    }
}

fn all_pass() -> ExitCode {
    let mut h = Harness::new("children");
    for name in ["alpha", "beta", "gamma"] {
        h.case(name, || println!("ran {}", 1 + 1));
    }
    h.run()
}

fn mixed() -> ExitCode {
    let mut h = Harness::new("children");
    h.case("passes", || ());
    h.case("asserts", || assert_eq!(1 + 1, 3, "arithmetic moved"));
    h.case("panics", || -> () { panic!("boom from a case") });
    h.case("returns_err", || Err::<(), _>("declined"));
    h.case("after_the_failures", || ());
    h.run()
}

fn seed_scale() -> ExitCode {
    let mut h = Harness::new("children");
    h.case("print", || {
        println!(
            "seed={} scale={} scaled={} rng={}",
            seed(),
            scale(),
            scaled(7),
            rng_for("label").next_u64()
        );
    });
    h.run()
}

/// Without a harness to refuse the value first.
fn seed_direct() -> ExitCode {
    println!("{:?}", catch_panic(seed));
    ExitCode::SUCCESS
}

fn scale_direct() -> ExitCode {
    println!("{:?}", catch_panic(scale));
    ExitCode::SUCCESS
}

fn skip_demo() -> ExitCode {
    let mut h = Harness::new("children");
    h.case("notes_skips", || {
        skip("qemu-system-i386", 212, "not found");
        skip("OVMF", 40, "not found");
        skip_oracle("as", 2400, "not found");
    });
    h.run()
}

fn golden_env() -> ExitCode {
    let root = env::var("ENRANG_TESTKIT_ROOT").expect("the scenario gets its golden root");
    let store = Arc::new(GoldenStore::new(root, BlessMode::from_env()));
    let mut h = Harness::new("children");
    h.goldens_in(Arc::clone(&store), "s");
    h.case("compares", move || store.check("s", "out.txt", "new\n"));
    h.run()
}

fn speed() -> ExitCode {
    let mut options = RunOptions::from_env().expect("the scenario gets valid options");
    options.budget = Some(Duration::ZERO);
    let mut h = Harness::new("children");
    h.case("takes_some_time", || {
        std::thread::sleep(Duration::from_millis(2));
    });
    h.run_with(&options, &mut io::stdout()).exit_code()
}

/// Owns the real `testkit` goldens and uses none of them.
fn default_store_orphans() -> ExitCode {
    let mut h = Harness::new("children");
    h.goldens("testkit");
    h.case("uses_no_golden", || ());
    h.run()
}

fn default_store_mismatch() -> ExitCode {
    let mut h = Harness::new("children");
    h.case("mismatch", || {
        golden("testkit", "skip_summary.txt", "not its contents\n")
    });
    h.run()
}

/// Compares through `golden_in`, whose report goes to the process's stderr.
fn golden_in_env() -> ExitCode {
    let root = env::var("ENRANG_TESTKIT_ROOT").expect("the scenario gets its golden root");
    let store = GoldenStore::new(root, BlessMode::from_env());
    println!("{:?}", golden_in(&store, "s", "out.txt", "new\n").is_ok());
    ExitCode::SUCCESS
}

fn one_skip() -> ExitCode {
    let mut h = Harness::new("children");
    h.case("notes_a_skip", || skip("gcc", 1, "not found"));
    h.run()
}

/// What this process's arguments and environment come to.
fn run_options() -> ExitCode {
    let options = RunOptions::from_env().expect("the scenario gets valid options");
    println!(
        "threads={} budget={:?}",
        options.threads,
        options.budget.map(|budget| budget.as_secs())
    );
    ExitCode::SUCCESS
}

/// A panic on a thread a case spawned is nobody's capture, so it prints as usual.
fn other_thread_panic() -> ExitCode {
    let mut h = Harness::new("children");
    h.case("spawns", || {
        let joined = thread::spawn(|| -> () { panic!("boom on another thread") }).join();
        assert!(joined.is_err());
    });
    h.run()
}

/// Our hook is replaced, so the panic reaches no slot and its report is empty.
fn foreign_hook() -> ExitCode {
    assert_eq!(catch_panic(|| ()), None);
    panic::set_hook(Box::new(|_| {}));
    println!("{:?}", catch_panic(|| -> () { panic!("unseen") }));
    ExitCode::SUCCESS
}

fn temp_dir() -> ExitCode {
    println!("{}", TempDir::new("probe").path().display());
    ExitCode::SUCCESS
}

fn tool_probe() -> ExitCode {
    let found = tool("sh").is_some();
    println!("sh={}", if found { "found" } else { "absent" });
    ExitCode::SUCCESS
}
