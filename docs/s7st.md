# s7st: R7RS Scheme, interpreted in FX-26

s7st (branch `s7st`, 2026-10-27) is an interpreter of R7RS-small Scheme,
written in FX-26. It is all in `s7st/`, and runs from the command line
(`bin/s7st`). The editor runs it as a separate process, `bin/s7st
--serve`, through one file, `editor/scheme.fx`. That gives the editor a
REPL (`M-x run-s7st`) and runs forms from Scheme buffers.

    bin/s7st                 a REPL on the terminal
    bin/s7st FILE …          each file run, as `load` runs it
    bin/s7st --serve         a server: requests and answers, a line each
    s7st/tests/run.sh        its tests (UPDATE=1 writes their .out files)

## How it is built

The files are plain FX-26 programs, read in the order `s7st/program`
lists them. Each file sees the globals of the files before it. Every name
s7st defines begins `s7-`, so another program can include the files
alongside its own without names colliding. (The editor did so at first,
which cost it 1.9 s at every start; it now runs s7st as a process
instead.) s7st's state lives in
region `@sc`, and its effect is `s7-eff`. When Fixpt's `load-module` can
take a group of files as one module, s7st can become a module with
`(module-parameters ((sc region)))` and nothing else changes.

| file          | what it does                                                                                                                                 |
| ------------- | -------------------------------------------------------------------------------------------------------------------------------------------- |
| `value.fx`    | Scheme values, the core (`s7-node`), the machine's continuations and states, and the global table                                            |
| `read.fx`     | the reader: all of R7RS's lexical syntax; each list's span, keyed by its first pair (`s7-spans`)                                            |
| `print.fx`    | `write` and `display`                                                                                                                        |
| `expand.fx`   | data to core: special forms, derived forms rewritten, `syntax-rules`, bodies' internal definitions                                          |
| `prims.fx`    | about 220 procedures written in FX-26                                                                                                        |
| `table.fx`    | hash tables                                                                                                                                  |
| `library.fx`  | libraries: namespaces, import sets, finding a library's file                                                                                 |
| `analyze.fx`  | what a text is, for an editor, read and walked but never run: faces, definitions, each local variable's binder, the read's error           |
| `machine.fx`  | the compiler to closures, and the CEK machine that runs its code, one step at a time                                                         |
| `prelude.scm` | what is written in Scheme: `map`, `guard`, `parameterize`, promises, the I/O procedures over ports, a few of SRFI 1's. `prelude.fx` is generated from it by `gen-prelude.py` |
| `session.fx`  | the API clients call: `s7-init!`, `s7-start!`, `s7-continue!`, `s7-take-output!`, `s7-interrupt!`                                            |
| `main.fx`     | the command-line REPL, and the server (its protocol is described at the top of the file)                                                     |

**The machine is a CEK machine whose continuation is data.** A state is one
of four things:
- a node to evaluate, in an environment, with a continuation;
- a value returned to a continuation;
- a procedure applied to arguments;
- a condition raised.

This gives several properties for free:
- **Proper tail calls.** A loop of a million iterations runs in constant
  space.
- **`call/cc` is first-class and re-entrant.** A continuation is an
  immutable list of frames.
- **`dynamic-wind`** runs its `before` and `after` thunks on every jump into
  or out of its extent.
- **R7RS's exceptions:** `with-exception-handler`, `raise`,
  `raise-continuable`, and `guard` (written in the prelude as R7RS 7.3
  gives it).
- **Clients run it in slices** (`s7-continue! fuel`). The server runs
  20,000 steps (a few milliseconds) at a time and reads requests between
  slices, so an `interrupt` stops a loop that doesn't end, and the
  session's state survives it.

**Variables are resolved when expanded, not when run.** A local is a frame
slot, given by depth and index. A global is its cell. A `lambda`'s frame
holds its parameters and then its body's internal definitions; `letrec*`
and `let-syntax` get frames of their own (`n-scope`).

**Hygiene works by renaming.** `syntax-rules` renames each symbol a
template introduces: `tmp` becomes `tmp 17`, where 17 is that expansion's
number. The space in the name means no symbol a program reads can equal
it. So `swap!`'s `tmp` binds nothing the user wrote. A free renamed symbol
means whatever its plain name means where the macro is used. A quote in a
template strips the renaming. Special forms and the procedures that
rewritten forms call are bound twice, under `if` and also under ` if`.
Rewritten forms use the space-prefixed names, so a program that binds
`if` or `list` locally doesn't break them (`tests/syntax.scm`).

**Primitives don't fail in FX-26's sense.** Every primitive checks its
arguments and raises a Scheme condition rather than trapping, so that a
client running s7st in its own process never has the run fail under it.
(A failure in the server would end only the server: the editor says so,
and starts it again when next asked.) A
condition that nothing handles stops the run with `Error: …`. A syntax
error is reported with its file, line and column before its form runs.

## What it does of R7RS-small

Most of it:
- **Special forms:** `quote`, `quasiquote` (nested, vectors), `lambda`
  (rest parameters), `define` (curried too), `set!`, `if`, `begin`, `let`
  (named too), `let*`, `letrec`, `letrec*`, `cond` (`=>`), `case` (`=>`),
  `and`, `or`, `when`, `unless`, `do`, `case-lambda`, `define-values`,
  `define-record-type`.
- **Macros:** `define-syntax`, `let-syntax`, `letrec-syntax`, and
  `syntax-rules` with literals, a custom ellipsis, `(... ...)`, nested
  ellipses, patterns after an ellipsis, dotted and vector patterns.
- **Delayed evaluation and the rest:** `delay`, `delay-force` (constant
  space), `make-promise`, `parameterize`, `guard`, `let-values`,
  `let*-values`, `cond-expand`, `include`.
- **Libraries** (`library.fx`): `define-library` makes a namespace of its
  own. `import` binds names to the exporting library's own cells, with
  `only`, `except`, `prefix` and `rename`; `export` may rename too. A
  library imported but not yet defined is loaded from a file named after
  it: `(foo bar)` from `foo/bar.sld`, under the importing file's directory
  or another of `s7-library-path`. The standard libraries (`(scheme …)`,
  `(srfi …)`, `(rnrs …)`) are the built-ins, which every namespace sees.
  The built-ins, the top level and each library are separate namespaces,
  so a program's `(define (map …) …)` changes only its own `map`.
- **Numbers:** exact integers of any size, exact rationals (`1/3`,
  `#e1.1` is `11/10`), and floats.
- **Data types:** lists, symbols, characters (Unicode), mutable strings,
  vectors, bytevectors, records, and hash tables (`table.fx`: SRFI 69's
  and R6RS's procedures, by `eqv?`, `equal?`, `string=?` or
  `string-ci=?`).
- **Ports:** string ports, and files for input and output. An output
  file is written when its port is flushed or closed, and when a run
  ends.
- **Time:** `current-jiffy`, `jiffies-per-second`, and `current-second`.
  FX-26's clock is monotonic, so `current-second` counts from the start of
  the run, not from the epoch.
- **Evaluation:** `eval` in any environment (`environment`,
  `interaction-environment`), `load`, `exit`.

## What is not done

- **Complex numbers.**
- **Datum labels.** Neither `#0=` nor `write`'s cycle-safe output exists.
  `write` stops after 100,000 items with `...`, so it ends on a cycle.
- **Console input.** It is empty: `read-line` and the others read string
  ports and files.
- **Deleting files.** `delete-file` raises a file error, because FX-26 has
  no primitive for it.
- **Full hygiene.** A free symbol that a template introduces means what
  its name means in the macro's namespace (a library's macro can use what
  the library doesn't export). But if the user's code binds that name
  *locally* around the use, the macro sees the user's binding. Yank's
  `(yank analysis macro)` has the same limitation.
- **`let-values` and `let*-values` both bind sequentially.** Each `init`
  sees the bindings before it. R7RS requires that only of `let*-values`.
- **Library details.** Every library sees the built-ins whether it
  imports them or not, and an imported name can be assigned with `set!`
  (R7RS makes that an error).

Each could be added.

## Speed

**Each top-level form is compiled before it runs** (`machine.fx`'s
`s7-compile`). Every node of the core becomes two FX-26 closures, made
once:
- **Its code** takes the environment, continuation and dynamic state, and
  returns the machine's next state.
- **Its quick evaluation,** where the node allows one, gets the node's
  value with no machine step: constants, variables, lambdas, `if` and
  sequences of such, and calls of pure built-ins on such.

A call of a closure with one clause, given the right number of quick
arguments, fills the new frame's slots directly. A closure's body still
starts with a step of its own, so the machine still runs in slices and
can be interrupted. A quick evaluation that cannot finish (a variable not
yet defined, an operator that turns out not to be a built-in) has done
nothing another could see, since it calls only pure built-ins. The node's
code then runs it the slow way.

On this machine, measured in the program itself with `current-jiffy`,
before compiling and after:

| benchmark                     | evaluating nodes | compiled |
| ----------------------------- | ---------------- | -------- |
| `(fib 25)`                    | 242 ms           | 100 ms   |
| `(tak 18 12 6)`               | 69 ms            | 26 ms    |
| a named-`let` loop, 1,000,000 | 1209 ms          | 333 ms   |
| `map` over 200,000            | 731 ms           | 455 ms   |
| `do` over a vector, 500,000   | 729 ms           | 221 ms   |

`(fib 25)` is 250,000 calls, so about 2.5 million procedure calls a second.
The same `fib` written in FX-26, which Fixpt compiles to native code, is
still much faster. FX-26 has no way to make FX-26 code at run time
("Openings").

- **Start-up** is 2.6 s, nearly all of it Fixpt compiling s7st's 4,600
  lines. Making the interpreter ready (special forms, primitives, prelude)
  takes milliseconds. The editor starts the server the first time it's
  asked for Scheme, so only that first request waits.
- **The editor's latency:** the editor looks for the server's answers
  every 50 ms while one is awaited, as it does for `*compilation*`.

## Openings

### For a flow analysis like Yank's

Yank's `(yank analysis core)` reduces Scheme to a small core:
- constants;
- variable references, each binder distinct;
- `lambda`, `if`, `set!`, application, `letrec*`, sequencing;
- every node keeping its source span.

Its `(yank analysis cfa)` then runs k-CFA over that core. **s7st's core
(`s7-form` in `value.fx`) is that language**, and the expander already
produces it:

- **Every node has a number** (`id`) **and a span** (file, start, end) for
  an analysis to key its facts by.
- **Every binder has a distinct identity:** the number of its `lambda` or
  `n-scope`, plus its slot index. Each lambda lists its slots' names
  (`names`).
- **References are resolved:** a reference names its binder's slot, or a
  global's cell.
- **Macros are expanded by the same expander that runs code**, so the
  analysis sees exactly what runs. Yank had to write a second expander for
  analysis.
- **The machine is the concrete counterpart of the analysis.** It is
  written as Van Horn and Might's "Abstracting Abstract Machines"
  prescribe: a CEK machine with continuations as data. Making
  environments map to addresses, bounding the addresses (by call site,
  for k-CFA), and joining values in a store turns the machine's step
  (`s7-step`) into an abstract interpreter over the same node types. The
  primitives give the abstract domain its cases: each says what it
  returns and what it raises.

What remains for an analysis:
- **A front end for buffers being edited.** `analyze.fx` is a first one,
  for the editor. It walks what the reader read, knowing R7RS's binding
  forms; an unknown form is an application, so its parts are still
  walked, as in Yank's desugaring. It changes no global, and the reader
  now keeps every list item's position (`s7-item-spans`). What it lacks
  for a flow analysis is the core itself: it resolves binders but builds
  no nodes, and it doesn't expand macros.
- **Expansion that leaves the live globals alone.** `define-syntax` and
  `define` at top level change the global table when expanded. An
  analysis of a buffer that hasn't run yet should expand into a table of
  its own.
- **The analysis itself.** `editor/flow.fx` is Heist's 0CFA of FX-26 code
  (`docs/fx26-analysis.md`), over a core of the same shape. A version for
  `s7-node` would be the third stage of that plan, run on Scheme.
- **What the editor can then show.** M-. through the analysis, the
  procedures each call can reach, and the types of data each variable can
  hold, as Yank shows them after `M-x flow-run-loads`. Eldoc for Scheme
  exists already, but it asks the running server (`describe`, which calls
  `s7-describe`): every
  global's value is in `s7-globals`, and each closure carries its lambda's
  parameter names. So it knows only what has been run. An analysis would
  know what the text says before it runs.

### For a compiler

**FX-26 has no `eval`.**
- `load-module` is resolved when a program is checked, not when it runs.
- The only code a program can make at run time is machine code, through
  `seal-code` and `native-procedure` (`fixpt/docs/fx26.md`, "Code a
  program makes"). That works only on arm64, and this machine is x86_64.

So s7st can't compile Scheme to FX-26 and run the result in the same
process. What it can do:

1. **Compile to closures, within the interpreter.** This is done ("Speed").
2. **Compile to FX-26 text and run it as a separate process.** Heist runs
   processes already (`editor/process.fx`). The FX-26 checker would then
   type the result, and Fixpt's native machines would run it. Scheme's
   dynamic typing becomes a union type, as `datum` is. `call/cc` needs a
   CPS translation or FX-26's one-shot continuations, which are enough for
   escapes, generators and `guard`.
3. **On arm64, machine code** through `seal-code`, once a back end exists.

The core is the input for each of these, and the expander is shared.

## In the editor

**How it runs.** `editor/scheme.fx` starts `../bin/s7st --serve` the first
time Scheme is asked for, then talks to it in the protocol `s7st/main.fx`
describes:
- each run is a `run` request, and the answers are its output, then its
  value or error;
- C-c C-c sends `interrupt`;
- eldoc sends `describe`.

So the editor doesn't compile s7st when it starts, and a Scheme program
that fails or never ends can't stop the editor. If the server's process
ends, the editor says so and starts a new one when next asked; the
definitions made in the old one are lost.

Its keys:

| key, command                   | what it does                                                                                    |
| ------------------------------ | ----------------------------------------------------------------------------------------------- |
| `M-x run-s7st` (`s7st`, `run-scheme`) | *s7st*, the REPL                                                                        |
| `RET` in *s7st*                | the input run, once its data are complete; otherwise a new line                                 |
| `C-c C-c` in *s7st*            | interrupts what is running                                                                      |
| `M-p`, `M-n` in *s7st*         | the input history                                                                               |
| `C-x C-e`                      | the sexp before point run, its value in the echo area (in .scm, .sld, .ss and .sps buffers)     |
| `C-M-x`                        | the top-level form around point                                                                 |
| `C-c C-b`, `C-c C-l`           | the buffer's forms, as `load` runs a file, so errors give their line                           |
| `C-c C-r`                      | the region                                                                                      |
| `C-c C-z`                      | to *s7st*                                                                                       |
| TAB in *s7st*, M-TAB            | the name before point completed, from those s7st's top level sees                               |
| M-.                            | in a Scheme buffer, a local variable's binder, or a definition in a buffer, as in an FX-26 buffer; for a name defined nowhere, what s7st knows of it |
| eldoc, in those buffers and *s7st* | once s7st runs, what it knows of the name at point, or of the operator of the call around it: `(map f l . ls)`, `car: 1 argument`, `guard: a macro`, `x = (1 2)`. Eldoc does not start s7st. |

**Scheme buffers look like Scheme.** Each `.scm`, `.sld`, `.ss` or `.sps`
buffer has an analysis actor. After each edit (the last of a burst) it
sends the text to the server's `analyze`. The answer becomes the buffer's
annotation, as the FX-26 syntax actor's does:
- faces: keywords, defined names, strings and comments;
- the definitions, for M-.;
- each local variable's binder, for M-.;
- the read's error, in the mode line.

Opening a Scheme file starts the server. TAB and RET indent as in an FX-26
buffer, with Scheme's body forms. Paredit's keys work there too.

**Where output goes.** In *s7st*, output goes before the prompt, as
comint's does. Text typed while something runs waits after the prompt.
When the run ends, an evaluation from a buffer shows its value in the echo
area, after any output on one line.

**Relative file names.** `load`, `open-input-file` and `include` resolve
a relative name against `s7-directory`. A buffer's forms use the
buffer's directory; *s7st* uses the directory of the buffer that was
selected when it was made. `bin/s7st` uses the directory it was started
in.

**Tests:**
- `editor/tests/ui/s7st-analysis.scm.keys`: a Scheme buffer's faces, its
  read error, M-. to a binder, and M-. on a name no buffer defines.
- `editor/tests/ui/s7st-complete.keys`: TAB completion in *s7st*.
- `s7st/tests/server.serve`: the server's protocol, interrupting a loop
  included.
- `editor/tests/ui/s7st-eldoc.scm.keys`: eldoc on a closure and on a
  procedure written in Scheme.
- `editor/tests/ui/s7st-repl.keys`: values, multi-line input, an error
  after output, an infinite loop interrupted, and the history.
- `editor/tests/ui/s7st-buffer.scm.keys`: the buffer's commands.
