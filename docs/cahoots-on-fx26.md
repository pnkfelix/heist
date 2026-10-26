# Porting cahoots to FX-26

Heist's first application is a port of cahoots, the actor-based
rewrite of yank, to FX-26 on Fixpt. This note says how cahoots' parts
map onto what FX-26 offers, what has to be added to Fixpt, and what
gets built first. It updates `fx26-for-yank.md`, which read yank's
`main` (a single command loop) rather than cahoots.

Sources read:
- cahoots at c337e2a (`~/Dev/Emacs/cahoots`): `DESIGN.md`, `ACTORS.md`,
  `src/yank/actor/core.sld`, `main.sld`, `src/yank/engine.sld`;
- `fixpt/` at 86eff712 (Fixpt 1e4d4ed6): `docs/fx26.md`,
  `crates/fixpt-fx26/src/standard.rs`, `TODO.md`.

## What cahoots is

- Actors in one heap, on one OS thread. Each has a mailbox, a state and
  a behavior `(behavior state message) → state`. They are spawned as a
  tree.
- A **turn** handles one message, and it is a transaction:
  - Sends, spawns and outside effects (`after-turn!`) are queued, and
    committed only when the turn ends well.
  - A turn that raises leaves the actor's state as it was. States are
    values; a buffer's text is a persistent rope.
- **Code is the currency.** Commands are procedures sent to a buffer
  and run on its state in its turn. A view's layers are procedures of a
  snapshot.
- An **activity** is a message plus all the turns that follow from it.
  A command is an activity. The frame starts the next command when the
  last one is done, and C-g gives up the one that is running.
- **Scheduling classes:**
  - interactive: the frame, buffers, the kill ring;
  - display: views, run only when nothing interactive waits;
  - idle: analyses, in 2 ms slices.
- Turns run in **engines** that pause after 20 ms, so a long turn holds
  up only its own actor.
- **Analyses** (syntax, names, flow, the index) are parties outside the
  text. They read snapshots by revision, and send back functions,
  advice and anchored annotations, never edits.

## Where the actors live

FX-26's processes copy every message deeply, except procedures, I-cells
and addresses (`fixpt/docs/fx26.md:1497`). A process may also hold only
transmissible data: nothing writable.

**So the interactive core is one FX-26 process with its own actor
scheduler,** a library ported from `core.sld`. Its actors share the
heap, so:
- a snapshot sent to a view is a pointer, not a copy of the rope;
- a message may be any closure, including one over mutable state.

That is cahoots as it is. The frame, buffers, views, the kill ring and
the buffer list all live there.

**Parties outside the text are FX-26 processes.** Syntax, names, flow
and the index:
- read an immutable snapshot (a rope is products and sums, so it is
  transmissible);
- run preempted by Fixpt's fuel slices, which takes the place of the
  idle class's 2 ms engines;
- send back closures, which are shared rather than copied, provided
  they are pure over transmissible data. That is what DESIGN.md's
  "functions, not results" asks for anyway.

A snapshot copied to an analysis costs O(text) each time it is sent.
The idle class already keeps only the latest snapshot of a burst, so
this is paid once per pause in typing, not once per key. If it shows up
in measurements, the fix belongs in Fixpt: sharing frozen data across
processes instead of copying it.

## Typing the actor core

Cahoots' messages are any Scheme value. In FX-26:
- **Every message is code.** An actor of state `S` is an `(actor S)`,
  and its messages are `(subr e (S) S)`.
  - This is already cahoots' convention for most messages.
  - Data messages such as `(key k)` or `(resize r c)` become closures
    built by the sender, or the frame's state gets a sum type of its
    own.
- **Transactions come from purity where possible.** A turn's sends and
  spawns are recorded and committed at its end, as in `core.sld`.
  Because states are values, a turn that fails rolls back by keeping the
  old state.
- **Heterogeneous actors** are a `poly` over the state type, held behind
  an existential (an `(actor S)` closed over by a send procedure) where
  a table needs them all.

## What FX-26 lacks, for this design

Revised from `fx26-for-yank.md` (R-numbers as there).

| Need | cahoots uses | Fixpt today | What to do |
|---|---|---|---|
| A failing turn leaves the editor running (R2) | `with-exception-handler` around each behavior | `error` and traps (car of nil, index) end the run; only `spawn-monitored` sees them | **First Fixpt change.** A fault caught in a dynamic extent, as R2 asks. Without it, one bad command kills the editor. |
| Pausing a long turn (R3, engines) | Larceny timer interrupt + `call/cc` | Fuel preempts between processes only; nothing to pause within one | **Defer.** Interactive turns are short. Long work goes to processes. Revisit if a command needs it. |
| C-g during a command (R3) | Between batches of turns, not inside one long turn | No program-visible interrupt; raw mode gives ^C as a byte | Same limit as cahoots: C-g is read between turns. Nothing is needed for now. |
| Cleanups (R1) | `dynamic-wind` for terminal mode; `at-stop!` | `fixpt` restores the terminal at exit even after a failure | Not needed for the slice. `at-stop!` is the scheduler's own. |
| Building a frame (R5) | String ports, one `write(2)` | Immutable strings; variadic `string-append`; `write-out` of a string | Build rows as strings and join them. Measure before asking for a builder. |
| Subprocesses (M-!, compile, shell, inferior) | `(yank process)`, FFI pipes | Absent (`fixpt/TODO.md` §84) | A Fixpt change when the port reaches them: spawn with pipes, read through `pselect`. |
| Files: exists?, stat, cwd, getenv (R7) | `(yank files)` | Absent (§84); `write-file` replaces atomically | A Fixpt change when visiting files needs them. |
| Tables: delete, iterate (R6) | R6RS hash tables | `table.fx` has neither; `eqtable` has delete | Library work in `table.fx`, or an association structure of our own at first. |
| Evaluating user code: `M-:`, init file (R4) | Larceny `eval` | None (§105) | Last. The editor is useful without it. |

## The first slice

The smallest thing that is still cahoots' shape, end to end:

1. **The actor core**, ported from `core.sld`: spawn, send, turns as
   transactions, activities, the three scheduling classes, timers, and
   the turn log. Turns run to completion; there are no engines.
2. **A rope** (`rope.sld`, an AVL tree of strings) as a datatype, with
   revisions.
3. **A buffer actor and a view actor:** insert, delete, point; a
   snapshot to the view; the view lays out lines.
4. **A frame actor:** keys bound to commands, the echo area, drawing
   the screen as one `write-out`.
5. **`main`:** raw terminal, then a loop that reads keys with
   `stdin-ready?`/`read-byte`, sends them to the frame, runs turns, and
   polls the terminal size.
6. **Commands:** self-insert, DEL, C-f/b/n/p/a/e, RET, C-x C-c.
   C-x C-f/C-x C-s for one file.

The first Fixpt change, R2, should land before or during step 1, so
that the actor core catches failing turns from the start.

## Status (2026-10-25)

The first slice runs: `fixpt/target/release/fixpt run editor/main.fx -- FILE`.
It has one buffer, one view and a frame, all actors. It has movement,
insertion, deletion, C-x C-s and C-x C-c. `C-c !` is a command that
fails on purpose: the echo area says why, and the buffer is left as it
was.

| File | From cahoots | What it is |
|---|---|---|
| `editor/core.fx` | `(yank actor core)` | Actors, turns under `attempt`, and commands run after a turn. No scheduling classes, activities or timers yet. |
| `editor/rope.fx` | `(yank actor rope)` | The persistent rope, as a `define-datatype`. |
| `editor/keys.fx` | `(yank keys)` | Keys as `(union char symbol)`, `kbd`, and decoding from a byte source. |
| `editor/screen.fx` | `(yank screen)` | Immutable rows with face spans; `screen-update` redraws the rows that changed. |
| `editor/main.fx` | `(yank actor main)`, a little of buffer, view, frame and commands | The slice. |

`editor/tests/run.sh` runs the modules' tests. The slice itself was
tried under `script(1)` with keys piped in.

**How a turn is typed.** A message to an actor of state `S` is a
`(subr turn-eff (S) (reply S))`. `turn-eff` is cancellable: it may
read, allocate and loop. A reply is the next state, plus commands
(thunks of `cmd-eff`) that the scheduler runs after the turn. The
checker accepts `attempt` around a polymorphic `run-one`, so rollback
is a property of the types, not a convention as it was in cahoots.

**What writing FX-26 at this scale taught:**
- A `cons` in one arm of an `if` gets a region of its own. Where the
  other arm is an acyclic list, the `cons` needs `(the (listof T
  acyclic) …)`, or a helper of that result type (`push` in
  `screen.fx`).
- `typecase` arms bind a name, `(char c …)`, and it must end with
  `else`.
- A type imported from a module file has no shape known at run time, so
  it can't be a member of a union outside that module. `screen.fx` uses
  `no-screen` instead of `(union false screen)`.
- `spawn` and `send` are FX-26's process forms, so the core's are
  named `spawn-actor` and `tell`.
- A definition sees only those before it. The actors are wired up after
  they are spawned (`subscribe`), and a buffer's subscribers are closures,
  so its type never names the view's.
- Types from a parameterized module are printed fully expanded, so one
  message about an actor is pages long. Naming them in messages would
  help.
- `fixpt check editor/main.fx` reports that "the checkers disagree" on
  `draw`. They agree on the type: one prints `cmd` by its name and the
  other expands it.

**Measured:** an empty program starts in 0.15 s, and checking and
compiling the actor core adds 0.05 s. An `attempt` costs about 1.7 µs.

**Next:**
- Scheduling classes, so that a burst of keys is drawn once.
- Activities, so that commands follow one another, and C-g.
- Windows and the minibuffer, then C-x C-f.
- Tabs laid out as columns (`(yank actor columns)`).
- Then the parties outside: a syntax actor that reads FX-26 with
  Fixpt's own reader, as a process sent snapshots.
