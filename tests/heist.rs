//! Heist's tests, one each, for `cargo nextest run`: every test of the
//! shell runners, run by that runner alone, so a test passes exactly when
//! its runner exits 0 and the runners stay what one runs by hand.
//!   editor::NAME       editor/tests/run.sh NAME-test.fx
//!   ui::NAME           editor/tests/ui.sh NAME
//!   s7st::NAME         s7st/tests/run.sh NAME
//!   s7st::prelude      s7st/gen-prelude.py --check
//!   conformance::LIB   s7st/conformance/run.sh LIB (its summary all passed);
//!                      the libraries s7st does not have yet, ignored
//! Each needs Fixpt built (`cd fixpt && cargo build --release -p fixpt-cli`).

use libtest_mimic::{Arguments, Failed, Trial};
use std::path::{Path, PathBuf};
use std::process::Command;

/// R7RS-small's libraries, as conformance/run.sh names them.
const LIBRARIES: &[&str] = &[
    "base", "case-lambda", "char", "complex", "cxr", "eval", "file", "inexact", "lazy", "load",
    "process-context", "read", "repl", "time", "write",
];
/// Those s7st lacks: complex numbers, and inexact's of them.
const NOT_YET: &[&str] = &["complex", "inexact"];

fn heist() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().to_path_buf()
}

/// The names of the files in `dir` ending in `suffix`, without it, sorted.
fn names(dir: &Path, suffix: &str) -> Vec<String> {
    let mut v: Vec<String> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .filter_map(|e| e.ok()?.file_name().into_string().ok()?.strip_suffix(suffix).map(String::from))
        .collect();
    v.sort();
    v
}

/// Run `cmd`; a failure is its exit status and all it printed.
fn run(mut cmd: Command) -> Result<String, Failed> {
    let out = cmd.output().map_err(|e| format!("{cmd:?}: {e}"))?;
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    if out.status.success() { Ok(text) } else { Err(format!("{cmd:?}: {}\n{text}", out.status).into()) }
}

fn script(path: &Path, args: &[&str]) -> Command {
    let mut c = Command::new("sh");
    c.arg(path).args(args);
    c
}

fn main() {
    let args = Arguments::from_args();
    let h = heist();
    let mut trials = Vec::new();

    let editor = h.join("editor/tests");
    for n in names(&editor, "-test.fx") {
        let sh = editor.join("run.sh");
        trials.push(Trial::test(format!("editor::{n}"), move || {
            run(script(&sh, &[&format!("{n}-test.fx")])).map(drop)
        }));
    }
    for n in names(&editor.join("ui"), ".keys") {
        let sh = editor.join("ui.sh");
        trials.push(Trial::test(format!("ui::{n}"), move || run(script(&sh, &[&n])).map(drop)));
    }

    let s7st = h.join("s7st/tests");
    let mut tests: Vec<String> = names(&s7st, ".scm").into_iter().chain(names(&s7st, ".serve")).collect();
    tests.sort();
    for n in tests {
        let sh = s7st.join("run.sh");
        trials.push(Trial::test(format!("s7st::{n}"), move || run(script(&sh, &[&n])).map(drop)));
    }
    let gen = h.join("s7st/gen-prelude.py");
    trials.push(Trial::test("s7st::prelude", move || {
        let mut c = Command::new("python3");
        c.arg(&gen).arg("--check");
        run(c).map(drop)
    }));

    for &lib in LIBRARIES {
        let sh = h.join("s7st/conformance/run.sh");
        let trial = Trial::test(format!("conformance::{lib}"), move || run(script(&sh, &[lib])).map(drop));
        trials.push(trial.with_ignored_flag(NOT_YET.contains(&lib)));
    }

    libtest_mimic::run(&args, trials).exit();
}
