# Changes Heist made to Fixpt

`fixpt/` is a squashed git subtree of Fixpt (`git@github.com:pnkfelix/fixpt.git`).
Heist edits it in place when the editor port needs something FX-26 lacks.
This file records each change: what was needed, why a library could not
do it, and what it cost. Kayak will need the same changes later
(see `docs/fx26-for-yank.md`, "Who does what").

## Base

- Fixpt `main` at 70382694 (2026-10-30), pulled from GitHub by Heist's
  02fa619d (squash 3c34eead). Fifteen commits, none Heist's request:
  a program's and a module's `.fasl` spliced into the heap once, not
  read and copied as a graph, and a definition's stamp digesting its
  type by structure; the native front end's entries called as native
  code, its syntax cached with it, and an FX-26 session's checker made
  once; arenas and reaps holding large objects, and a place's limit
  (TODO §180, §181). Heist needed no change. After `fixpt prewarm` and
  `bin/heist-compile all` (18.6 s), all 135 tests pass; ratfink matches
  shakedown as before (corpus 123 of 124, playback 12 of 12, its FX-26
  test reports unchanged).
  Start-up from `.fasl`s, median of 20 (before: the same measure on
  e4af8997 with kit adopted, 2026-10-29): the editor 0.42 s (0.43 s);
  s7st 0.74 s (0.87 s); the CFA's server 1.15 s (1.35 s); combo's server
  0.11 s (0.14 s); ratfink on a one-proof FX-26 file 0.22 s (0.26 s).
- Before: Fixpt `main` at e4af8997 (2026-10-29), pulled from GitHub by Heist's
  c7837be9 (squash d4be8147). Three of Heist's requests, done:
  a maker's file is known by its first form, the rest not read
  (8202075e; `fixpt-module-type-per-dependent.md` cost 1,
  `fixpt-load-time.md` item 1); substitution leaves alone a type it
  cannot change, so a module type given to a dependent is not copied
  for it (80f8b222, cost 2); and a region binder a call leaves unsolved,
  used only as a pair's region and only allocated and read, is
  `acyclic` (e4af8997, `fixpt-region-default-acyclic.md`, as Heist
  prototyped it). After `fixpt prewarm` and `bin/heist-compile all`
  (19.1 s), all 135 tests pass. Heist has no edits of its own on it.
  ratfink matches shakedown as before (corpus 123 of 124, playback 12
  of 12, its FX-26 test reports unchanged), and the region request's
  repros run.
  Start-up from `.fasl`s, best of 5: an empty program 0.03 s (0.03 s);
  the editor 0.44 s (0.53 s); s7st 0.85 s (0.86 s); the CFA's server
  1.34 s (1.34 s); combo's server 0.13 s (0.28 s); ratfink on a
  one-proof FX-26 file 0.25 s (0.75 s).
- Before: Fixpt `main` at 61a2e792 (2026-10-29), pulled from GitHub by Heist's
  8ce93dbe (squash 79849167): masking keeps `read` and `write` on a region
  only the result's type mentions (Heist's request,
  `docs/requests/fixpt-mask-hides-acyclic-writes.md`), so a procedure that
  writes what it returns says so, and is refused where instantiated at
  `acyclic`; the front end native on every machine that runs native code,
  and its caches mapped, not copied. Heist had to say two reads it made:
  `s7-parse-number` (`s7st/read.fx`) and its caller `s7-bar-symbol?`
  (`s7st/print.fx`) now declare `(read @sc)`, the region of the value
  they build and look at (s7st and the CFA, which shares the files, were
  refused without them). After `fixpt prewarm` and `bin/heist-compile all`
  (14.5 s), all 131 tests pass, and the request's repro is refused, both
  checkers agreeing. Heist has no edits of its own on it. Start-up from
  `.fasl`s, best of 5: an empty program 0.03 s (0.05 s); the editor
  0.53 s (0.56 s); s7st 0.86 s (0.90 s); the CFA's server 1.34 s
  (1.40 s); combo's server 0.28 s (0.30 s); ratfink on a one-proof FX-26
  file 0.75 s (0.73 s). The same within noise, but for the empty program.
- Before: Fixpt `main` at 6505d8bb (2026-10-29), pulled from GitHub by Heist's
  cc42544a (squash 8488d79f): images as tables of sections, a static
  area in the heap that the front end's image is read into first, and a
  write barrier by generation. After `fixpt prewarm` and
  `bin/heist-compile all` (20.9 s, the .fasls an older Fixpt made
  stale), all 131 tests pass. Heist has no edits of its own on it.
  Start-up from `.fasl`s, best of 5, against b2609b6a measured the same
  hour: an empty program 0.05 s (0.05 s); the editor 0.56 s (0.53 s);
  s7st 0.90 s (0.88 s); the CFA's server 1.40 s (1.37 s); combo's server
  0.30 s (0.29 s); ratfink on a one-proof FX-26 file 0.73 s (0.71 s).
  The same, within noise, or a little slower: these commits are for
  collections, and their own measure of start-up (an empty program,
  50.6 ms to 49.1 ms) is below what these runs resolve.
- Before: Fixpt `main` at b2609b6a (2026-10-29), pulled from GitHub by Heist's
  c2d66a71 (squash 769f4412): `fixpt prewarm`, which makes an
  executable's front-end caches before they are wanted (2.6 s and 3.1 s
  cold, after a build); a call-out's field is the call-out itself; a
  foreign call roots its caller's code. `.fasl`s an older Fixpt made are
  stale; after `fixpt prewarm` and `bin/heist-compile all` all 131 tests
  pass. Heist has no edits of its own on it. From clean: the editor
  3.0 s, s7st 5.2 s, the CFA 7.5 s, combo 1.7 s. Start-up from `.fasl`s
  as on 21f4b60e, within noise: an empty program 0.05 s, the editor
  0.53 s, s7st 0.87 s, the CFA's server 1.35 s, combo's server 0.29 s.
- Before: Fixpt `main` at 21f4b60e (2026-10-29), pulled from GitHub by Heist's
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

### F5. What a path is: `file-info` and `read-symlink` (primitive)

- **Needed for:** the editor's dired listings, which told a directory
  from a file by trying to list each name, and could show no size, time
  or permissions; and s7st's `file-exists?`, which read the whole file,
  and was false for a directory.
- **What changed:** two primitives, as SRFI 170 names them:
  - `file-info : (subr (io fs-read) (string) (sumof (info (productof (kind (sumof (file unit) (directory unit) (symlink unit) (other unit))) (size int) (modified int) (mode int))) (failed io-error)))`,
    what the path itself is (`lstat`: a link not followed), its size in
    bytes, when last modified (seconds since the epoch), its permission
    bits;
  - `read-symlink : (subr (io fs-read) (string) (sumof (target string) (failed io-error)))`.
  - **The runtime:** `prim.rs` (at the end of its table: 522 and 523),
    `world.rs` (`file_info`, `read_symlink`); Rust's `std::fs`.
  - **Names elsewhere:** `standard.rs`, `lower.rs`, `debts.rs`,
    `eval-prims.fx`, `docs/fx26.md`'s table. **Regenerated:**
    `standard.fx`, `native-direct-x64-layout.fx`.
- **Cut, 2026-10-30:** F5 first had five more, which changed files:
  `delete-file`, `delete-directory`, `rename-file`, `create-directory`,
  `copy-file`. The user pointed out that running the system's programs
  could do those, as Yank's dired does (`rm -r`, `mv`, `cp -R`, `mkdir
  -p`); what was missing was a way to wait for one without stopping the
  other tasks, which F6 added. So they went, and the editor and s7st run
  the programs. What a path *is* stayed a primitive: it is asked often (a
  listing asks it of every name), and its answer is data, not text to
  parse.
- **Why a primitive:** nothing in FX-26 could ask what a path is but by
  running `ls` and parsing what it writes, which differs between systems
  and cannot hold every name. A syscall (`docs/fx26.md`, "Syscalls")
  would not do: its types are plain (no product or sum to give the
  answer or an `io-error`), and only a runtime's own code may declare one.
- **Machines covered:** one of each kind: `fixpt-cli/tests/io.rs`'s
  `files_inspected`, of `tests/programs/io/fs.fx` (a file, a directory, a
  link and its target, a missing path); both checkers agree on it.
- **Kayak will need:** the two primitives over its own runtime.

### F6. A task waits for a process: `pselect` arms for its output, its end, and any process's news (language, primitive)

- **Needed for:** the editor's processes (M-x compile, grep, shell, s7st
  and the CFA's servers), which it polled every 50 ms while one ran; and
  running a command and waiting for it without stopping the other tasks.
  Fixpt's `TODO.md` §132, Heist's own request after F4.
- **What changed:**
  - **Two `pselect` arms:** `((process-output p) text body …)`, ready
    once process `p` has output to take, `text` what `process-output`
    gives; `((process-exit p) how body …)`, ready once it has ended and
    all its output has been taken, so that an arm for the output sees all
    of it before the end, `how` what `process-exit` gives;
    `((process-news) p body …)`, ready once any process has output to
    take or has ended unseen, `p` its number: for a set of processes
    known only as the program runs, which no arm of a fixed `pselect`
    can name (and a `race` of arms cannot: its branches may do no I/O).
    An end is seen once `process-status` says it or `process-exit`
    gives it, and is then no news. Both parsers
    (`processes.rs`, `parser-forms.fx`), and both checkers' types for the
    events, `(event (io process))` (`standard.rs`, `check-env.fx`).
  - **A primitive:** `process-exit : (subr (io process) (int) (sumof
    (exited int) (signalled int) (unknown unit)))`, how a process ended,
    waiting until it has (as `read-byte` waits, no task running
    meanwhile); its output need not have been taken. In an arm, at once.
  - **Primitives too:** `process-news : (subr (io process) () int)`,
    the first process with news, -1 if none.
  - **Used by:** the editor's main loop, which waits for a key or a
    process's news, not polling every 50 ms; its listings' `rm`, `mv`,
    `cp` and `mkdir` (`run-command!`); s7st's `delete-file`.
  - **The scheduler** (`sched.rs`): events 46–48 (output ready, a waker
    given, taken back), 49–51 (ended) and 52–54 (any news); three lists
    of wakers in its state; `timers_wait` sleeps on the processes too, and runs the
    wakers of those that are ready.
  - **The runtime** (`world.rs`, `tty.rs`): a wake pipe, made with the
    first process, neither end blocking; each process's reader thread
    writes a byte to it after each read and at the end, and a thread of
    its own waits for its exit without reaping it (`waitid`, `WNOWAIT`)
    and writes one too. The scheduler `poll`s the pipe beside the
    standard input, with the earliest deadline, then empties it; who is
    ready it asks the processes, not the pipe.
  - **The library** (`processes.fx`): `process-output-event`,
    `process-exit-event`.
  - **Names elsewhere:** `lower.rs`, `debts.rs`, `eval-prims.fx`,
    `docs/fx26.md` (`pselect`, the table), `TODO.md` §132.
  - **Regenerated:** `standard.fx`, `native-direct-x64-layout.fx`
    (`process-news` is primitive 524, `process-exit` 525, after F5's).
- **Why not a library:** a task can wait only for what the scheduler can
  be woken by; nothing woke it for a process.
- **Machines covered:** one of each kind, `fixpt-cli/tests/io.rs`:
  `a_process_waited_for` (`process-wait.fx`: output, then the end, a
  deadline beside; `process-exit` alone) and
  `a_task_waits_for_a_process_while_another_runs` (`process-tasks.fx`),
  `news_of_any_process` (`process-news.fx`).
  Both checkers agree on both. A second's wait for a process costs 0.01 s
  of CPU: it sleeps. Also run: `fixpt-runtime`, `fixpt-tidy`, all of
  `fixpt-cli`, and `fixpt-fx26`'s `processes`, `checker`, `evaluator`,
  `compiler` and `layout`. Not Fixpt's whole suite.
- **Found, not ours:** `fixpt-fx26`'s `processes` tests fail on this
  128-core machine with "no native slots left" (`fixpt-native`,
  `NATIVE_SLOTS`), with or without F6: run with the default 128 test
  threads, their sessions together take more slots than there are. With
  `--test-threads=1` all 34 pass.
- **Not done:** a process's standard error apart from its output; an arm
  for its input being writable.
- **Kayak will need:** the two arms, and an event for each in its
  scheduler.

Each entry takes this form:

### Fn. Title (library | primitive | language)

- **Needed for:** the editor feature, and the `fx26-for-yank.md` requirement.
- **What changed:** files, forms, primitives, types.
- **Why not a library:**
- **Machines covered:** which of Fixpt's machines and checkers have it.
- **Kayak will need:**
