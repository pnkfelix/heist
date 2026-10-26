# Changes Heist made to Fixpt

`fixpt/` is a squashed git subtree of Fixpt (`git@github.com:pnkfelix/fixpt.git`).
Heist edits it in place when the editor port needs something FX-26 lacks.
This file records each change: what was needed, why a library could not
do it, and what it cost. Kayak will need the same changes later
(see `docs/fx26-for-yank.md`, "Who does what").

## Base

- Fixpt `main` at 1e4d4ed6 (2026-10-25), added by Heist's 86eff712.

## Reading and moving the base

- Our changes: `git diff 86eff712 HEAD -- fixpt/`. After a pull, use the
  newest `Squashed 'fixpt/' content from commit …` commit instead.
- Taking upstream: `git subtree pull --prefix=fixpt ~/Dev/LangPlay/fixpt main --squash`.
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
  was before F1.
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
  - **Names in types.** Types are printed fully expanded, not by their
    `define-type` names, so a command's type is several hundred
    characters long.
  - **Text past an error.** It stops at the first refusal before the
    place.
  - **Instantiations at a place** (`facts.insts`) and effects. These are
    for R10's flow analysis.
- **Kayak will need:** the same primitive, over its own checker.

Each entry takes this form:

### Fn. Title (library | primitive | language)

- **Needed for:** the editor feature, and the `fx26-for-yank.md` requirement.
- **What changed:** files, forms, primitives, types.
- **Why not a library:**
- **Machines covered:** which of Fixpt's machines and checkers have it.
- **Kayak will need:**
