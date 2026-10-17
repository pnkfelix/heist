# What FX-26 must offer to implement Yank

Heist's editor is a port of Yank, an Emacs-lineage editor written in R7RS
Scheme for Larceny (`~/Dev/Emacs/yank`). This document lists what FX-26,
the language, and its implementations must provide before the port can
begin. Each requirement is traced to what Yank does today.

## Who does what

**Kayak is meant to be FX-26's reference implementation.** Its compiler
and runtime are written once, in KFX. That ends the duplication Fixpt
has: every feature of Fixpt is written twice, once in Rust and once in
the FX-26 bootstrap.

Kayak is not there yet. Meanwhile the gaps below should close in Fixpt,
which is where FX-26 can grow today. Kayak follows under its rule K1.
Fixpt's process for this already exists: kayak's requests are numbered
`TODO.md` sections marked "(kayak's request, DATE)", and they move to
`DONE.md` under the same number. Heist's requests should go the same way.

Each request is marked with its **cost** in duplicated work:

- **library**: written once, in FX-26, as a module like
  `fx26:conditions.fx`. It runs on every machine and on kayak's engine,
  and no checker changes.
- **primitive**: a runtime entry and its type in the standard
  environment. It is cheap to duplicate: Fixpt's runtime, then
  kayak-rt and the engine's primitive table.
- **language**: a new form, a new typing rule, or a change to what
  every machine does at an existing operation. It must be built in
  both of Fixpt's checkers or in each machine, then in kayak. Keep
  these few, and say for each why a library or a primitive cannot do
  the job.

Every addition should be expressible in KFX, or be a primitive kayak-rt
can mirror, so that it does not make kayak's catching up harder.

## The snapshot this reads

- Fixpt `main` at bb3f5709 (2026-10-16), as last fetched to this
  machine. Note that `~/Dev/LangPlay/fixpt` has `x86_64-native` checked
  out, which is 130 commits behind.
- kayak `main` at 40abf64 (2026-10-16).
- Yank `main` (2026-10-16): 49 libraries and 13,012 lines. The analysis
  libraries (k-CFA and its support) are about 55% of it.

Fixpt's `main` already has much of what Yank needs, built at kayak's
requests:
- the `io` effects: stdout and stderr, stdin by byte and by line,
  `stdin-ready?`, whole files, `list-dir`, `args`, `exit`, `main`
  (§84, §95);
- `clock` and `sleep-until`;
- terminal raw mode and size (§95);
- processes, `par`, `pselect` with a key arm and a deadline arm, `race`
  and monitors (§92, §94), with preemption by fuel slices;
- conditions as a library (`fx26:conditions.fx`, §89);
- escape-only prompt tags and one-shot continuations;
- `bytevectorof`, `u8` and UTF-8 conversions;
- variadic `string-append` and `append`.

None of those are requested again here.

## Requirements

They are in priority order. The first four decide the editor's
architecture, so they are needed first even where the rest could wait.

### R1. Cleanup when frames are dropped (language)

**Yank:** 18 uses of `dynamic-wind`. They restore:
- the terminal mode;
- the current buffer;
- a buffer's read-only flag;
- the minibuffer's state;
- keyboard-macro state;
- interrupt masking.

They must run on a normal return, on an error, and on C-g's escape.

**Fixpt:**
- "a failure in FX-26 unwinds nothing" (fx26.md, the `io` section).
- Aborts run nothing for the frames they drop. Fixpt makes one
  exception, the regions that end.
- Fixpt restores the terminal mode itself, at the end of a run.

**kayak:**
- No such mechanism.
- Marks are popped on unwind by a Rust `Drop`, but nothing a program
  writes is run.

**Request:** a form, or a primitive taking thunks, that runs a cleanup
whenever control leaves its body for good. That covers:
- a normal return;
- an escape or abort to a prompt *of any tag*, including one outside
  the body;
- a raised condition that a handler escapes from;
- the interrupt of R3;
- the cancelling of the process it runs in (a `race`'s loser, or a
  monitored group's members).

**Not when suspending.** `call-with-oneshot-continuation`, or capturing
a composable continuation, then aborting to the scheduler, keeps the
frames. Running cleanups there would undo state on every task switch.
(This is the trouble with Scheme's `dynamic-wind`: a continuation jump
cannot tell leaving from suspending. See Design notes.) A captured
continuation that is never resumed gets no cleanup. Racket does not
give it one either.

**No "before" half.** Dynamic state belongs in continuation marks,
which a resumed continuation carries with it. FX-26 has marks on every
machine.

**Cost:**
- Every machine's abort, and process cancellation, must run the
  cleanups for the frames they drop.
- If the cleanup is a mark that abort looks for, the typing needs no
  new rule: a `subr` with a `poly` type, as `with-handler` has.

**Done when:** tests of all five exits run the cleanup exactly once, on
every machine. A `yield` inside the body does not run it.

### R2. Faults caught where they happen (language)

**Yank:**
- Every command, hook and idle task runs inside `guard`. A command
  doing `(car '())` reports "car: …" and the editor goes on.
- Errors in the init file, and in evaluated user code, are caught the
  same way.

**Fixpt:**
- "`error` stays the panic (§86): `pure`, never dropped, ending the
  run; caught only at a task's boundary … never in place" (TODO §89).
- Runtime faults (a field of the wrong variant, an index out of range,
  division by zero, a stack overflow) end the run, or the process under
  `spawn-monitored`. Heap exhaustion is a Rust panic.

**kayak:** the same.
- On kayak-rt a fault is a Rust panic, caught only by a monitored
  process.
- On the engine, a fault is a value internally, but no program can
  catch it.

**Why the process boundary is not enough:**
- Processes share only transmissible (immutable) data.
- An editor's commands mutate the buffer, the windows and the kill
  ring. A command run in a monitored worker could not touch them, short
  of making every piece of editor state a process of its own, with
  every edit a message.
- That is a real architecture, but it is a large price for "a bug in
  one command must not kill the editor".

**Request:** revisit §86 for one narrow case.
- `error` stays `pure`, and nothing changes for code that does not ask.
- A new primitive observes a fault in a dynamic extent, and the effect
  goes on the observer, not on `error`. For instance:

  ```
  call-with-fault-handler :
    (poly ((a type) (e effect))
      (subr (maxeff e (io fault)) ((subr e () a) (subr e (fault) a)) a))
  ```

  - `fault` carries the message and, where known, a source position.
  - The handler runs after the body's frames are dropped, so R1's
    cleanups run.
  - The `io` effect says that the result depends on the
    implementation's fault order: it is not pure, never speculative,
    never reordered. That is the same bargain as Haskell's `catch` of
    `error` in `IO`.
- Stack overflow should be a fault. Heap exhaustion should at least end
  the run with a message rather than a Rust panic.

**Cost:**
- One primitive with a `poly` type.
- In each machine, a fault must unwind to the nearest handler instead of
  ending the run.

**Done when:** `(call-with-fault-handler (lambda () (car nil)) (lambda (f) 0))`
gives 0 on every machine, and the cleanups of R1 inside it run.

### R3. Interrupting a running command: C-g (language)

**Yank:**
- A timer interrupt every ~0.1 s asks the terminal whether byte 7 has
  arrived. If it has, the handler escapes to the command loop.
- `guard` cannot swallow the escape, so `(let loop () (guard (e (#t #f))
  (car '())) (loop))` is still stopped.
- Buffer insertion and deletion hold interrupts off (`without-interrupts`).

**Fixpt:**
- Preemption at fuel slices, between processes only. A program cannot
  see an interrupt or hold one off.
- Under `terminal-raw`, ^C is a byte, and otherwise SIGINT's default.

**kayak:**
- The engine's REPL stops a form on ^C, using fuel slices (C94, C99),
  but no program can.
- On kayak-rt, preemption is the OS's, between threads.

**Request:** an interrupt a program installs, delivered at polls.
- `(with-interrupt-check check body)` runs the pure-ish `check` at
  polls, every N ms or every N units of fuel. When `check` says so, the
  interrupt escapes to an escape tag the program gave, running R1's
  cleanups on the way out.
- `(without-interrupts body)` holds it off. An interrupt that arrives
  during the body is delivered when the body ends.
- The check must be cheap and allocate nothing. `stdin-ready?` plus a
  peek at the next byte would do.
- Alternatively: a way to deliver an escape into a *running process*
  from another, if R2's answer moves commands into processes after all.

**Cost:** language, since every machine's poll must call the check.
The machines already poll at the same places for preemption.

**Done when:** the loop above, which catches everything, is stopped by
a byte on stdin, on every machine. An interrupt is never delivered
inside a `without-interrupts` body.

### R4. Evaluating FX-26 inside the running editor (library, plus a bridge)

**Yank:** this is the extension language, and the reason it is an Emacs.
- `~/.yank.scm`, `M-:`, `C-x C-e` and `C-j` call `eval`, in one
  persistent environment. Forty-four libraries are imported into it,
  macros included.
- User code defines commands, keymaps, modes, hooks and variables. It
  calls editor internals, and stores closures the editor calls later.
- Its stdin, stdout and stderr are editor buffers.
- Evaluation is cut into 100 ms slices, then moved to the background.

**Fixpt:**
- No `eval` for programs. The pieces exist as FX-26 modules: the
  reader, `syn.fx`, the checker in FX-26, and the evaluator (`val` is
  its own union).
- Since §96 the evaluator keeps state between REPL forms, but that is
  in the driver.

**kayak:**
- No API. The engine and checker can be included in a unit, and that
  is how the REPL is built.
- The engine's state is global, so there is one instance per process.
- The checker's refusals are panics.

**Request:** a design note first, then an `fx26:` library. These
questions need answers:
1. **A persistent environment.** Definitions made in one evaluation are
   seen by the next, and a name can be redefined. That has to agree with
   the out-of-date tracking that the REPL already does (fx26.md).
2. **The host's modules, imported with their types.** Evaluated code
   calls the editor's procedures, and the editor calls closures the
   evaluated code made. The evaluator's values (`val`) differ from
   compiled values, so a typed bridge is needed. It is the hard part.
   Evaluated code may have to be compiled by the same machine, not
   interpreted.
3. **Every failure as a value:** a read error, a checker refusal, or a
   fault (R2). Each has a kind, a message and a span, and nothing is
   printed on the side.
4. **Its `io`** redirected to procedures the host supplies, for one
   evaluation at a time.
5. **Time slices:** run for N ms, then give back a remainder the host
   can resume or drop. A process with `race` against a deadline may be
   enough if the evaluation can run in a process; see R2 on what a
   process may share.
6. **Macros.** Yank exports `define-command`, `define-key`,
   `define-major-mode` and `define-variable` to user code. FX-26 has no
   macros (fx26.md leaves "Syntax" open). Either procedures over tables
   do the job, which the port should try first, or this becomes a
   request of its own.

**Done when:** a program evaluates
`(define (f x) (host-insert! x))` and then `(f "hi")`, both on the same
environment. The second call reaches the host's `host-insert!`, the
host keeps `f` and calls it later, and a refusal and a fault both come
back as values.

### R5. Text a program can edit (primitives)

**Yank:**
- The buffer is a gap buffer over one mutable string: `string-ref` in
  O(1), and `string-copy!` within the string, whose ranges may overlap.
- Screen rows are mutable strings, and a frame is built in a string
  port.

**Fixpt:**
- Strings are immutable UTF-32, with `string-ref` in O(1).
- `(arrayof char r)` is mutable and O(1), so a gap buffer can be built
  on it. But there is no block copy, and no way to make a string from
  part of an array.
- There is no string builder or port.

**Requests** (all primitive or library):
- `array-copy!`, whose ranges may overlap, for arrays of any element
  type, and `array->string` taking a start and an end.
- A string builder: append a string or a char, then take the result.
  It could be a library over `arrayof char`, if `array->string` exists.
- `string->int` and `string->number` (TODO §75), and `string-upcase`.
- Writing bytes to stdout: `write-out-bytes` of a `bytevectorof`. A
  frame is UTF-8, and today it must go through `utf8->string`, then
  `write-out`.

**Done when:** a gap buffer of 10 million chars inserts at a random
point in amortized O(1), and a 200×60 frame goes out in one write.

### R6. Hash tables (library, plus one primitive)

**Yank:** R6RS hash tables of four kinds:
- by identity: symbols, chars and records;
- by string;
- by `equal?`;
- by a hash and an equality the program supplies.

`hashtable-keys` and `hashtable-entries` are used for completion and
listings, and deletion for keymaps and caches.

**Fixpt:**
- `fx26:table.fx` takes the program's hash and equality, but has no
  delete and no iteration.
- `eqtable` takes as keys only pairs, refs, arrays and i-cells. Records
  (bloblets) are excluded, and the evaluator lacks `eqtable`.

**kayak:** none. Only the hash functions exist.

**Requests:**
- Delete and iteration (a fold over the entries) in `table.fx`.
- Bloblets as `eqtable` keys, or a stable identity hash for mutable
  objects, which would let `table.fx` hash them itself.
- `eqtable` in the evaluator.

### R7. The operating system (primitives)

**Yank:**
- `HOME` expands `~`.
- File modification times invalidate a cache of definitions.
- `file-exists?` and directory tests.
- The current directory, for relative file names.
- Saving writes over the file in place, keeping its permissions and
  its links.

**Fixpt:**
- None of the above.
- `write-file` writes beside the file and renames over it. That drops
  the file's permissions and replaces a symbolic link with a plain file.

**kayak:** the same, and it adds a stance: "FX-26 reads no environment"
(`world.rs`).

**Requests:**
- `file-info`: kind, size, and modification time in nanoseconds, with
  `not-found` as a value.
- `current-directory`.
- `environment-variable` under a new `(io env)` effect, or a documented
  convention by which `main` receives the environment.
- `write-file` keeps the old file's permissions and writes through a
  symbolic link to its target. This is a choice to make in the
  semantics, not a new primitive.
- Later: delete, rename and mkdir.
- Not needed: signals, since terminal size polled at each redisplay
  will do, and subprocesses.

### R8. Scale (implementation)

Yank is 13,000 lines in 49 modules. It must start in well under a
second, and it stays resident for hours.

**Requests:**
- **FX-26 heap images, or separate compilation** (Fixpt PLAN Q9), so
  the editor is not checked and compiled whole at every start.
- **A collector that does not re-copy the loaded program at every
  major collection:** a static area or a large-object space (TODO §27).
  The k-CFA analysis keeps hundreds of MB live, and Yank on Larceny saw
  pauses of 80–720 ms.
- **Later:** weak tables or ephemerons (TODO §59). Yank abandoned a memo
  for lack of them.

### R9. Smaller conveniences (library)

- `map`, `for-each`, `fold` and `filter` in a standard prelude (TODO
  §22). Yank uses them on nearly every page.
- Optional arguments: Yank passes them as rest lists, which `vlambda`
  can already express. Not requested.
- Multiple values: products serve. Not requested.

### R10. Flow analysis, shared by the editor and the compiler (library, on the checker's output)

**Yank:** Yank's largest research investment was flow analysis.
- It runs k-CFA and m-CFA over Scheme desugared to a core language,
  idly and time-sliced (`analysis/cfa.sld` and its support, about 55%
  of the source).
- It shows the values reaching the variable at point, the callees at a
  call, inferred signatures in eldoc, find-uses (`M-?`), and calls that
  cannot work.
- Measured (Yank `DONE.md` and `TODO.md`, 2026-10-12 to -15):
  - All of Yank analyzes in 5.4 s from nothing at m-CFA depth 2, and
    1.9 s after an edit, by a warm run that matches definitions across
    the edit.
  - m-CFA gave k-CFA's precision at a half to a seventh of the cost.
    Depth beyond 1 bought no precision in k-CFA.
  - Splitting on records only where they hold procedures (CPA-style)
    took depth 2 from 220 s to 11 s, with the same precision.
  - The cost was in data structures: interning, hash-consed intsets,
    `eq?`-compared value ids. A memo table was abandoned for lack of
    weak tables. Heaps reached 0.3–1.9 GB.
  - Precision died wherever "unknown" entered: `eval`, `guard`
    handlers, foreign procedures, vector contents.

**A statically typed FX-26 still needs flow analysis.** Polymorphic
and structural types say what *may* flow, not what *does*. Flow
analysis answers:
- which closures reach a call made through a variable or a
  structurally typed field (for `M-.`, find-uses, and direct calls);
- which variants reach a `tagcase` (dead arms);
- which instantiations reach a polymorphic parameter at a site;
- which effects happen, against the declared `maxeff`.

The compiler wants the same answers: kayak's roadmap has Twobit's
optimizations in KFX and a uniform `Value` beside unboxed generics
(its TODO §24). **Build it once, as a library, and use it for both.**

**Requests to FX-26 (Fixpt first):**
- **The elaborated program as data:** a type at every node, every
  instantiation (`proj`, and those that inference fills in), resolved
  names, and effects, each with a span. Fixpt keeps effect summaries by
  span but not types (its TODO §25). The editor needs the same thing
  for type-at-point and eldoc: the reader and the checker as libraries,
  with diagnostics as data.
- **R4's bridge stays typed.** If evaluated code enters as `datum`,
  the analysis meets Scheme's "unknown" again. Under `(eval-at T src)`
  it meets only "any value of T".
- **R6 and R8's runtime pieces are what the analysis runs on:**
  records as `eqtable` keys, stable identity hashes, weak tables for
  memos, and a collector that copes with hundreds of MB live.

**Requests to kayak:**
- **The analysis on the incremental query substrate** (`lib/query.kfx`,
  after Coopt's query-based compiler), with node identities that stay
  stable across edits, so that warm reanalysis is the design rather
  than a correspondence made after the fact.
- **One analysis run per region, in a cancellable process.**
  - The run's state is in a `letrena` or the process's reap, dropped
    whole when the next run starts; on kayak-rt this needs no collector.
  - Results go out as immutable summaries.
  - An edit cancels the run (`race`, and R1's cleanups).
- **Fixpt's corpus as the benchmark:** its 653 programs and its 41k-line
  front end. Measure precision by spurious callees and by warnings
  found in deliberately broken code, which Yank's `TODO.md` asks for.

**Staging:**
1. Closure flow, bounded by types: which lambdas reach which calls.
   That alone serves `M-.`, find-uses, and direct calls.
2. Then data flow over unions and sums.
3. Then effects.

**Done when (stage 1):** for all of Fixpt's front end, the callees at
every call through a variable are found, with no spurious ones where a
type rules them out. A one-definition edit is reanalyzed in under a
second, while typing stays responsive.

## Kayak: implementation, not language

These are kayak's own work, apart from following Fixpt on R1–R9.

- **Parity with Fixpt `main`:**
  - the processes on the engine (§27);
  - `read-byte` and the terminal on the engine;
  - variadics and `apply` on kayak-rt (refused since C71);
  - `eq?` and `set-car!` on kayak-rt.
- **Stage A** (its TODO §31.2), so that tiers 1–5 run FX-26 programs
  without Fixpt's word listings. Today the only standalone tier is the
  engine, about 200× slower than compiled Rust.
- **x86-64 in kayak-jit:** tiers 2, 4 and 5 are arm64 macOS only.
- **Memory on kayak-rt.** Its heap is never freed, and repeated
  `string-append` leaks every intermediate.
  - Regions first, as `docs/research/kayak-rt-gc.md` recommends.
  - The engine's Cheney collector leaks its old spaces and bignums.
- **`terminal-size` without running `stty`,** so it can be called at
  each redisplay.
- **`scripts/check.sh` on x86-64 Linux.** The `made-*` corpus goldens
  expect native results.
- **The records:**
  - DONE.md stops at C125, though C126–C131 are built.
  - Several TODO entries are stale: §7, §13, §16, §17 and §27.
  - PLAN §6 and §8 predate C49 and C101.

## Design notes

### Why not `dynamic-wind`

Scheme's `dynamic-wind` has two halves:
- **"before"** runs when a continuation re-enters the extent;
- **"after"** runs when one leaves it.

That is sound only if every jump means "leaving". Once continuations
also implement threads, generators or engines, every task switch runs
"after" and every resume runs "before". A generator yielding from
inside `with-input-file` closes the file at each yield (Pitman,
"UNWIND-PROTECT vs. Continuations"). Yank met this: `engine.sld` has
`call-with-engine-root` so that resuming a slice does not re-enter the
winds of whoever ran the first one.

Racket kept `dynamic-wind`, but took its other jobs away:
- `parameterize` is built on continuation marks, which need no
  rewinding.
- Threads are primitive, so a switch runs no winds. `racket/engine` is
  built on threads.
- Continuation barriers forbid re-entry where it would be unsafe.
- Custodians reclaim the resources of what is killed without unwinding.
- Will executors (Chez's guardians) are the safety net run by the
  collector.
- Breaks (^C) are delivered at safe points as `exn:break`. They unwind
  as any exception does, and an `exn:fail?` handler does not catch them.

That leaves "after", run only when frames are really dropped, and that
is R1.

FX-26 is in a good position to do the same:
- Its marks hold dynamic state.
- Its processes are threads, not continuation jumps.
- A process already owns its places, which end with it, so a process
  is FX-26's custodian. R1 asks only that cancelling a process also
  runs its cleanups.

### Interrupts are escapes, not conditions

Yank's C-g is an escape that `guard` cannot catch, so a loop that
catches everything is still stopped. Racket gets the same result by
making `exn:break` not an `exn:fail`. In FX-26, R3's interrupt should
escape to a tag the program installed. It must not `raise`, since a
handler installed by `with-handler` would run first and could
swallow it.

### Flow analysis with types: what changes

Yank's analysis was written for an untyped language. Four things
differ for FX-26:

- **"Unknown" is bounded.** In Scheme an unknown value poisoned every
  set it reached; Yank's fix (31916f0) was to make an unknown set hold
  no data at all. In FX-26 the worst case is "any value of type T", a
  much smaller hole. `datum` and unions are where the Scheme problem
  returns, which is why R4's bridge should stay typed.
- **Polymorphism supplies the context.** Yank found that the useful
  context was what kind of value came in, not which call chain came
  before: m-CFA at depth 2 matched k-CFA, and splitting on records
  that hold procedures paid. In FX-26 the type arguments at an
  instantiation are exactly that, and they are in the elaborated
  program. Type-argument polyvariance should be the default context,
  with call-site depth added only where measurements say it pays.
- **Effects and regions split the store.** Abstract garbage collection
  fit Yank poorly, because its analysis had one global store. FX-26
  says which regions a procedure reads and writes, and
  `letregion`/`letrena` say when a region dies. A pure procedure needs
  no store modeling at all, and a region's addresses can be dropped
  when it ends.
- **Uniqueness would allow strong updates.** If FX-26 gains
  substructural types, a unique reference can be updated strongly,
  which is a well-known gain in precision. This is one argument for
  ranking substructural types above GADTs.

### What Yank asks that this document does not

The port changes these instead of FX-26:
- **Larceny's FFI to libc:** termios, `ioctl`, `poll`, `read` and
  `write`. FX-26's `io` effects replace it.
- **Larceny's timer interrupts and `call/cc` for engines:** replaced by
  processes and preemption, plus R3.
- **Procedure reflection for eldoc** (`procedure-formals`): replaced by
  the checker's types, which tell more.
- **Its own Scheme reader and `syntax-rules` expander for analysis:**
  rewritten for FX-26 source. The checker in FX-26 can replace much of
  what Yank had to infer.
