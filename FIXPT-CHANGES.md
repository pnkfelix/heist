# Changes Heist made to Fixpt

`fixpt/` is a squashed git subtree of Fixpt (`git@github.com:pnkfelix/fixpt.git`).
Heist edits it in place when the editor port needs something FX-26 lacks.
This file records each change: what was needed, why a library could not
do it, and what it cost. Kayak will need the same changes later
(see `docs/fx26-for-yank.md`, "Who does what").

## Base

- Fixpt `main` at 21f4b60e (2026-10-29), pulled from GitHub by Heist's
  a3658e7d (squash 2b4f03ea): Heist's load-time request in part
  (`docs/requests/fixpt-load-time.md`) -- an executable's image found by
  its trailer alone, images this executable wrote loaded without a CRC or
  `Heap::verify`, mapped and spliced in place, made for a fixed base;
  the CRC eight bytes a step where it is kept; subtyping's trail looked
  up by pair, module types proven below one another remembered; and an
  inferred list printed alike by both checkers
  (`docs/requests/fixpt-checkers-print-list-arguments.md`, Heist's).
  Still open: `parse::takes_modules_at` reads a whole file for its first
  form. `.fasl`s an older Fixpt made are stale; after `bin/heist-compile
  all` all 131 tests pass. Heist has no edits of its own on it. From
  clean: the editor 2.9 s, s7st 5.3 s, the CFA 7.7 s, combo 1.7 s; 23 MB
  in all. Start-up from `.fasl`s, against ec7a02b0: an empty program
  0.05 s (0.18 s); the editor through main.fx 0.55 s (0.79 s); s7st 0.90 s
  (1.07 s); the CFA's server 1.38 s (1.56 s); combo's server 0.29 s
  (0.48 s).
- Before: Fixpt `main` at ec7a02b0 (2026-10-28), pulled from GitHub by Heist's
  d2879d07 (squash f47238d0): the checkers print an imported list type
  alike (`docs/requests/fixpt-checkers-print-lists.md`, Heist's request),
  so `fixpt check editor.fx` no longer says they disagree; built-in module
  files get `.fasl`s; a `.fasl` keeps native code. The `.fasl`s an older
  Fixpt made are said stale and their sources run, but s7st's and the
  CFA's tests compare that warning, so they failed until
  `bin/heist-compile all` (8.5 s). Then all 99 tests pass (5 UI tests on a
  retry). Heist has no edits of its own on it. From clean, compiled
  (`bin/heist-compile all`, which now has a `cfa` target): the editor's 20
  files in 3.0 s (`frame.fx` 0.8 s, the rest 0.01-0.3 s each); s7st's 13
  in 5.5 s (`expand.fx` 1.5 s, `prims.fx` 1.0 s, `machine.fx` 0.6 s); the
  CFA's, after s7st's (the same `.fasl`s, byte for byte), 7.7 s
  (`scheme.fx` 1.0 s, `engine.fx` 0.5 s); 16 MB in all. Start-up, from
  source against from `.fasl`s: the editor loaded through main.fx 3.0 s
  against 0.79 s; s7st to its prompt and out at end of input 3.9 s
  against 1.07 s; the CFA's server likewise 5.1 s against 1.56 s.
- Before: Fixpt `main` at fff9f9e4 (2026-10-28), pulled from GitHub by Heist's
  3922431e (squash 2c45243c): the recursive types a substitution makes
  interned, and a maker's `.fasl` naming its parameters' types again. The
  editor through main.fx starts in 1.96 s from `.fasl`s (2.56 s before),
  5.30 s from source (5.86 s). `.fasl`s an older Fixpt made need no
  cleaning: each is said stale ("another fixpt made it") and its source
  loaded. Still: `fixpt check editor.fx` says the checkers disagree, in
  how they print a list type (TODO.md). Heist has no edits of its own on
  it.
- Before: Fixpt fc9e56fe (2026-10-28), pulled by Heist's
  598ccfe7 (squash 5b0960cc): a program's `.fasl` names types by the
  earlier files' abbreviations, and recursive types print as their minimal
  graph (`docs/requests/fixpt-program-fasl-types.md`, Heist's request).
  `bin/heist-compile all` in 13.3 s (s7st's alone was 444 s); s7st's
  `.fasl`s 4.0 MB, and it starts in 1.08 s against 3.90 s from source.
  Heist has no edits of its own on it.
- Before: Fixpt b26b2efc (2026-10-28), pulled by Heist's
  90390000 (squash 33105471): a module file's `.fasl` names the standard
  types and the closed types it repeats. The editor from `.fasl`s
  (`bin/heist-compile`) starts in 2.56 s against 5.86 s from source, and
  its tests pass with them. A program's `.fasl` still writes its types in
  full, so s7st's are unusable (`docs/requests/fixpt-program-fasl-types.md`).
- Before: Fixpt 8ff01fe3 (2026-10-28), pulled by Heist's
  556d8e43 (squash f1c8eabb): `.fasl` files of module files and programs
  (`fixpt compile-file`; Fixpt `docs/research/fasl.md`, `DONE.md`
  §156-§157), a maker's kept with its parameters as written. Heist's tests
  pass on it. Tried in a copy, not adopted: the editor starts in 5.0 s
  from `.fasl`s against 5.9 s from source; through eldoc.fx 2.65 s against
  4.75 s, as Fixpt measured, but making main.fx from modules read from
  `.fasl`s costs 2 s against 0.5 s from source, with or without main's
  own `.fasl`.
- Before: Fixpt 0c2e4dd5 (2026-10-28), pulled by Heist's
  ea918aa7 (squash 36335552): native code on arm64 only -- a module's
  maker with frames past 4080 bytes, `new`/`make-array` and their region
  forms in line, and compiled code's names, lines and values in `lldb`.
- Before: Fixpt 35bf4c4f (2026-10-28), pulled by Heist's
  48ec00d0 (squash 8beaa5b8): `(module-parameters ())`, a maker of no
  arguments that `load-module` and `load-moduleof` take (Heist's ask,
  given the user in conversation).
- Before: Fixpt 62261413 (2026-10-28), pulled by Heist's
  2dde955f (squash 52e491a8): a module's `define*` used as a value
  (`docs/requests/fixpt-define-star-in-modules.md`, Heist's request; Fixpt
  `DONE.md` §148), `(m T qualified)` module parameters, not included, and
  include made cheaper in the FX-26 checker by interning types and keeping
  the cyclic walk by type (`docs/requests/fixpt-include-cost.md`, Heist's
  request; §149, §151); frozen regions covariant in lifetimes (Kayak's,
  §150).
- Before: Fixpt 6447f9b0 (2026-10-28), pulled by Heist's
  30d080c6 (squash f6f8274a): `module-parameters` of modules and
  expressions as module items (`docs/requests/fixpt-module-file-parameters.md`,
  Heist's request), and strings at a region, `(stringof r)`.
- Before: Fixpt 2d706414 (2026-10-28), pulled by Heist's c8eacb3c
  (squash 2b137803): a module's maker in native code, however many its
  items (`docs/requests/fixpt-native-module-makers.md`, Heist's request;
  Fixpt `DONE.md` §145).
- Before: Fixpt 5731f52e (2026-10-27), pulled by Heist's
  a9d57d8b (squash 358e4450): region and heap `new`/`make-array` in line
  in x86_64 native code (`docs/requests/fixpt-region-alloc-inline.md`,
  Heist's request; branch s7st had pulled it, b7b60d98, by 82b06f73,
  merged since), `load-moduleof` and
  `restrict`, compiled code named to `gdb` and `lldb` with source lines,
  and a syscall's effect with no `(io sys)` required.
- Before: Fixpt 8793b0cb (2026-10-27), pulled by Heist's 550e2fcb
  (squash c2cfe8cf): queries by type and effect and `consumes T`.
- Before that: Fixpt 991ec476 (2026-10-26), pulled by Heist's cea14dba
  (squash 83dbcee8), with F1–F4 upstream.
- Earlier: Fixpt 1e4d4ed6 (2026-10-25), added by Heist's 86eff712.

## Upstream

F1–F4 below are all on Fixpt's `main`, as Fixpt `DONE.md` §129–§132
(Heist's requests), rebased onto Fixpt's syscalls (8c7111da). The
entries below stay as the record of what Heist asked for and why; Fixpt's
`DONE.md` and `docs/fx26.md` are now the definition. Where upstream
differs from what Heist had:

- F1: `attempt1` is in `check-env.fx`'s `k-built-in-only-table`, which
  replaced the `symbol=?` chain, so the leading-`%` test is gone.
- F3: `%fx26-type-at` is primitive 509, after the syscall primitives
  (506–508).
- F4: `(io process)` is the twelfth I/O kind, code 11, after `(io sys)`.

Still open in Fixpt's `TODO.md`:

- §131: whether `type-at` stays a primitive or becomes a syscall that a
  module built into Fixpt declares (`define-optional-syscall type-at
  "fx26:type-at/1"`), so that the editor needs no `--syscalls`. A module
  file cannot hold a declaration yet (`fixpt/docs/research/syscalls.md`,
  "What Fixpt does", 4).
- §132: a `pselect` arm for a process (F4, "What it does not do").

## Reading and moving the base

- Our changes: `git diff 550e2fcb HEAD -- fixpt/`. After a pull, use the
  pull's merge commit instead. (Not the `Squashed 'fixpt/' …` commit
  itself: its tree is Fixpt's, not under `fixpt/`.)
- Taking upstream: `git subtree pull --prefix=fixpt ~/Dev/LangPlay/fixpt main --squash`,
  or `git@github.com:pnkfelix/fixpt.git` in place of the local path.
  Upstream rebases its `main` at times; a squashed pull does not care.
- Offering a change upstream: `git subtree split --prefix=fixpt` gives a
  branch of Fixpt's tree with our commits on it.

## Changes

### F1. `attempt`: a failure caught in place, at a cancellable body (language)

- **Needed for:** the editor's turns. A command that does `(car nil)`
  must end with a message in the echo area and leave the editor running.
  This is R2 in `docs/fx26-for-yank.md`, done differently from what R2
  proposed there.
- **What changed:**
  - A new form, `(attempt e on-failure)`, documented in
    `fixpt/docs/fx26.md` under "`attempt`".
  - Runtime: `attempt1` in `processes.fx`. It is `race2` with one
    branch, whose failure handler gives the "lost" outcome to
    `on-failure` instead of failing.
  - Typing: `synth_attempt` (Rust) and `k-attempt-te` (FX-26). These
    share `race`'s cancellability check, now factored out as
    `cancellable` and `k-cancellable`.
  - Parsing: `processes.rs` and `parser-forms.fx`. The head lists in
    `parse.rs`, `syn.rs` and `parser-exps.fx` gained `attempt`, and
    `check-env.fx`'s `k-built-in-only?` gained `attempt1`.
  - The type `%processes:attempt1` in `standard.rs`.
- **Why not a library:** a library can't catch a trap. The machines
  already turn a failure in a monitored group into an abort to the
  scheduler's prompt (`sched::task_failed`), and `attempt` reuses that.
  What needed a typing rule was the body's restriction.
- **Why this shape:** Fixpt's §86/§89 keep `error` as a panic, "caught
  only at a task's boundary … never in place". The checker shows that
  an `attempt`'s body can leave nothing half done (race's rule), so the
  body *is* a task's boundary, and §86 stands. R2's original proposal,
  catching any fault in any dynamic extent, would have reversed it.
- **What it asks of programs:** the code that may fail must not write
  shared state. In the editor, a turn returns its new state, and the
  sends and spawns it wants, as values, and the scheduler commits them
  outside the `attempt`. States are persistent (a rope).
- **Machines covered:** all twelve; both checkers agree. Tests are in
  `programs/attempt` (four ways, ten schedules) and `preempt.rs` (each
  machine).
- **A cost found on the way:** the FX-26 checker's `k-lookup` runs
  `k-built-in-only?` on every name it looks up, and that is a chain of
  `symbol=?` tests. One more name in the chain pushed a test that runs the
  front end under the 20M-step limit (`direct.rs`,
  `native_session_adapters_aborts_and_stack_maps`) over the limit. The
  chain now tests for a leading `%` first, which makes it cheaper than it
  was before F1. (Upstream has since made it a table: see "Upstream".)
- **Found a bug on `fx-ast-eval`**, fixed as F2.
- **Found a hazard in the test harness**, older than F1: the
  scheduler's prompt tag is kept once in the runtime's state (`%sched`
  12 and 13). One test session runs the evaluator written in FX-26 and
  the compilers in turn, and a tag one of them made is no use to the
  other. So `(race 1 2)` compiled and then evaluated in one session fails
  with "a prompt tag is expected", and after a longer program it fails
  with "the wrong number of arguments". The existing directories happen
  to order their programs so that this never shows. `programs/attempt`
  did not, so its evaluator way now has a session of its own
  (`common::with_own_eval`). A real run uses one way, so it is not
  affected.
- **Not done:**
  - A richer failure value (kind, span) than the message string.
  - Heap exhaustion is still a Rust panic.
  - Cancelling a running `attempt` from outside, which would serve C-g.
- **Kayak will need:** the form, the cancellability rule it shares with
  `race`, and a failure in a group aborting to the scheduler's prompt on
  each of its tiers.

### F2. The evaluator's failed task is quiet until the scheduler takes it (bug fix)

- **Needed for:** F1's tests. The bug is older than F1: `race`
  branches and monitored processes fail by the same path.
- **The bug:** on `fx-ast-eval` only, when a monitored task fails,
  `efail` asks the runtime (`TASK_FAILED`, op 38) and aborts to the
  scheduler's prompt. The current task is still the failed one until
  `run-task` takes the failure (op 37), and the evaluator polls before
  every application. If its tick, every 4096 applications, fell in that
  window, `PREEMPT_WANTED` said yes. `preempt` then `suspend`ed to a
  prompt that had just been left, giving "call-with-composable-continuation:
  no prompt for this tag". The native machines check that the prompt is
  on the stack (their `reachable`); the evaluator's ops cannot.
- **What changed:** `fixpt-runtime/src/sched.rs`, `op::TASK_FAILED`:
  the failed task enters `quiet` when a tag is returned, so it is not
  preempted again before the failure is taken. Quiet is per task, and a
  new task starts without it.
- **Found by:** a subagent, from a trace of the `%sched` ops. The
  reproduction is `programs/attempt/evaluator-after-failure.fx`; where
  the ticks fall is why it needed an earlier top-level form and more
  than about 600 failures.
- **Kayak will need:** nothing, unless it grows an evaluator that runs
  a program's scheduler as its own values.

### F3. `type-at`: the checker's type at a place in a program text (primitive)

- **Needed for:** the editor's C-c t, the type of the expression at
  point. This is the first piece of R10's "the elaborated program as
  data", and of the "reader and checker as libraries" asked for in
  `fx26-for-yank.md`.
- **What changed:**
  - **The primitive:** `type-at : (subr (io fs-read) (string int) string)`.
    It checks a program text with the checker written in Rust, keeping
    each expression's type (`record_types`, as the verifier does), up to
    the form the place is in. It gives the innermost expression's span (in
    characters) and type as `"START END TYPE"`, or `"error START END
    MESSAGE"`. Its effect is reading the files the text loads.
  - **The checking:** `crates/fixpt-fx26/src/typeat.rs`.
  - **The runtime:** a hook, `Runtime::type_at`, which `Fx26Session`
    installs, since the checker is above `fixpt-runtime`, and
    `%fx26-type-at` in `prim.rs`.
  - **Its names elsewhere:** `standard.rs` (its type), `lower.rs`,
    `debts.rs` (it cannot fail), and `eval-prims.fx` (the evaluator
    written in FX-26 calls the host's).
  - **Regenerated** (`FIXPT_BLESS=1 cargo test -p fixpt-fx26 --test
    layout`): `standard.fx` and `native-direct-x64-layout.fx`. I first
    edited `standard.fx` by hand. It is generated from `lower.rs`, its
    header says so, and `tests/layout.rs` checks it. The test caught it.
- **Why a primitive:** the checker kept types by node already; what a
  program lacked was a way to ask. Loading the checker written in FX-26
  into a program would compile about 24,000 lines on every start. The
  primitive uses the one the session has.
- **Machines covered:** all twelve, with the same answers
  (`programs/typeat/basic.fx`).
- **Measured:** on the editor's own program (220 KB, seven files), 21 ms
  near its start and 0.44 s near its end.
- **Not done:**
  - **Text past an error.** It stops at the first refusal before the
    place.
  - **Instantiations at a place** (`facts.insts`) and effects. These are
    for R10's flow analysis.
- **Names in what it prints** (added after): the checker keeps a
  `define-type`'s name only for data that mentions no variable
  (`closed_named`), so a `subr`, or a product holding one, printed
  expanded, and the editor's types ran to thousands of characters.
  `type-at` now prints a type, and each named type, with no names at all,
  then puts each named type back where its text appears, longest first.
  - **Printing.** That needed a printing mode with no names,
    `Checker::print_expanded`. In it, closed data keeps its name, and a
    cycle prints by its distance up (`%^2`), so that a recursive type
    reads the same wherever it is printed.
  - **Modules.** A module's types and effects read as `(select m t)` are
    resolved first: the effects through `selected_effect`, the types
    through `select_map`, which then applies a family it finds applied.
  - **Families.** One-parameter families (a module's `(actor s)`) are
    named when applied to a named type that is in the result:
    `(actor frame)`.
  - **Result:** `in-buffer` prints as `(subr pure ((actor frame) command)
    (msg buffer))`, as written.
  - **Cost:** 69 ms near the start of the editor's program and 0.5 s
    near its end. Families applied to every named type, before limiting
    them to those in the result, took 0.4 s more a query.
  - **What it is:** a printing, not a judgement. Two names of one type
    print as the first in order.
- **Kayak will need:** the same primitive, over its own checker.

### F4. Programs run beside this one: `(io process)` and `process-*` (primitive)

- **Needed for:** the editor's M-x compile, M-x grep, M-! and M-x shell:
  running the editor's own tests from inside it and visiting the places
  their output names. This is R7's "the world outside", for programs, in
  `fx26-for-yank.md`.
- **What changed:**
  - **A new I/O kind, `(io process)`**, the eleventh (upstream, the twelfth): `IoKind::Process`
    (`ast.rs`), and in the checker written in FX-26 `k-io-kind-name` and
    `k-io-kind-code` (`check-types.fx`) and `io-any` (`eval-types.fx`).
  - **Six primitives:**
    - `process-start : (subr (maxeff (io process) (read r)) ((listof string r) string) (sumof (started int) (failed io-error)))`,
      a program and its arguments, and a directory (`""` means this one's);
    - `process-output : (subr (io process) (int) string)`, what it wrote since last asked;
    - `process-status : (subr (io process) (int) (sumof (running unit) (exited int) (signalled int) (unknown unit)))`;
    - `process-write : (subr (io process) (int string) (sumof (done unit) (failed io-error)))`;
    - `process-close-input : (subr (io process) (int) unit)`;
    - `process-signal : (subr (io process) (int int) unit)`, a signal to its group.
  - **The runtime:** a table of processes in `World` (`world.rs`). Each
    process's standard output and error are one pipe, which a thread of
    its own reads into a buffer, so that asking never waits. Its output
    is decoded as UTF-8: a character cut by a read waits for its rest,
    and a byte that is not UTF-8 becomes U+FFFD.
  - **Status:** a process is `running` until it has exited and its
    output has all been read, so one more `process-output` after
    `exited` gives the rest.
  - **Sessions:** each process starts in a session of its own (`setsid`,
    `tty::new_session`). With no controlling terminal, a shell cannot
    take the editor's terminal for job control. At first I used only a
    process group of its own, and `sh -i` was stopped trying (SIGTTOU).
    The session's group is what `process-signal` signals, so C-c C-c
    reaches what a shell runs.
  - **The unsafe code** (`setsid` between fork and exec, `kill`) is in
    `tty.rs`, which was already the crate's one place that calls the
    system.
  - **Names elsewhere:** `docs/fx26.md`, `prim.rs`, `standard.rs`, `lower.rs`, `debts.rs`
    (they cannot fail), and `eval-prims.fx`.
  - **Regenerated:** `standard.fx` and `native-direct-x64-layout.fx`.
- **Why a primitive:** nothing in FX-26 could start a program.
- **What it does not do:** a program cannot wait for a process. There is
  no `pselect` arm for one, as there is for `(read-byte)`. The editor
  polls every 50 ms while a process runs, and every 500 ms otherwise.
  An arm would need:
  - a waker list per process in the scheduler (`sched.rs`), as there is
    for the standard input;
  - the reader threads to wake `wait_stdin`'s `poll` (a pipe it also
    polls);
  - the arm's syntax in both parsers.
  - **Also not done:** a pseudo-terminal for the program, so programs
    see no terminal (`sh -i` says so, and runs without job control);
    environment variables; separate standard output and error.
- **Machines covered:** all twelve, and both checkers agree.
  `programs/process/basic.fx` writes to a shell's input, reads its
  output and status, and starts a program that does not exist.
- **Also fixed: column limits.** The tidy test (`fixpt-tidy`,
  `fx_size.rs`) found lines over 100 columns that F1 and F3 had added,
  in `check-processes.fx`, `parser-forms.fx` and their tests. I had run
  only `fixpt-fx26`'s tests after them, not the whole workspace. They
  are now wrapped, and the whole workspace's tests pass.
- **Kayak will need:** the I/O kind, and the same six primitives over
  its own runtime.

Each entry takes this form:

### Fn. Title (library | primitive | language)

- **Needed for:** the editor feature, and the `fx26-for-yank.md` requirement.
- **What changed:** files, forms, primitives, types.
- **Why not a library:**
- **Machines covered:** which of Fixpt's machines and checkers have it.
- **Kayak will need:**
