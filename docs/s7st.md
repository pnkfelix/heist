# s7st: R7RS Scheme, in FX-26

s7st (branch `s7st`, 2026-10-27) is an implementation of R7RS-small
Scheme, written in FX-26: an interpreter until 2026-10-31, a compiler to
FX-26 since, which Fixpt's `stage` checks and compiles as it runs. It is all in `s7st/`, and runs from the command line
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
| `machine.fx`  | what compiled code runs on: calls, raising, continuations, `dynamic-wind`, the fuel, `force`, the fused calls of built-ins                   |
| `lower.fx`    | the compiler: core lowered to FX-26, staged, run; and the top level (`import`, libraries, `eval`, `load`)                                     |
| `prelude.scm` | what is written in Scheme: `map`, `guard`, `parameterize`, promises, the I/O procedures over ports, a few of SRFI 1's. `prelude.fx` is generated from it by `gen-prelude.py` |
| `session.fx`  | the API clients call: `s7-init!`, `s7-start!`, `s7-continue!`, `s7-take-output!`, `s7-interrupt!`                                            |
| `main.fx`     | the command-line REPL, and the server (its protocol is described at the top of the file)                                                     |

**Scheme is compiled to FX-26, in direct style** (2026-10-31). Up to a
hundred top-level forms at a time are expanded, lowered to an FX-26
datum (`lower.fx`), and checked and compiled by Fixpt's `stage` against a
module of the runtime (`machine.fx`), then run. A Scheme procedure is an
FX-26 procedure, of up to four arguments or of their list; a local is an
FX-26 variable, a box if it is assigned. A call goes through the runtime
(`s7-call1` and its kin), which finds the procedure's code. What a stack
alone does not give comes from FX-26's delimited control, a prompt about
each run (`lower.fx`'s `s7-run-in`):
- **Proper tail calls.** FX-26's calls in tail position take no stack, so
  Scheme's take none.
- **`call/cc` is first-class and re-entrant.** It captures the rest of
  the run up to the prompt, a composable continuation, resumable any
  number of times. Resumed, it aborts the run to the prompt, which
  resumes it in a prompt of its own.
- **`dynamic-wind`** runs its `before` and `after` thunks on every jump
  into or out of its extent: the dynamic state (winds, handlers) is a
  global, which a continuation keeps and puts back on its way.
- **R7RS's exceptions:** `with-exception-handler`, `raise`,
  `raise-continuable`, and `guard` (written in the prelude as R7RS 7.3
  gives it).
- **Clients run it in slices** (`s7-continue! fuel`). Each procedure's
  entry spends fuel; with none left, the rest of the run is captured and
  kept, and the slice ends. The server reads requests between slices, so
  an `interrupt` stops a loop that doesn't end, and the session's state
  survives it.

Until 2026-10-31 s7st was a CEK machine whose continuation was data,
compiled to closures ("Speed", "Before: an interpreter").

**Variables are resolved when expanded, not when run.** A local is a frame
slot, given by depth and index, which the compiler makes an FX-26 variable.
A global is its cell. A `lambda`'s frame
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

## Conformance

`s7st/conformance/run.sh` runs Larceny's R7RS test suite
(`test/R7RS/Lib/tests/scheme/`), read from the sibling repository
`inthematrix-rrof` at d184ff8d into a temporary directory. On 2026-10-27:

| library         | result                     |
| --------------- | -------------------------- |
| base            | 1078 tests passed          |
| case-lambda     | 5 passed                   |
| char            | 139 passed                 |
| cxr             | 28 passed                  |
| eval            | 5 passed                   |
| file            | 75 passed                  |
| lazy            | 33 passed                  |
| load            | 4 passed                   |
| process-context | 2 passed                   |
| read            | 44 passed                  |
| repl            | 10 passed                  |
| time            | 2 passed                   |
| write           | 63 passed                  |
| complex         | not run: no complex numbers |
| inexact         | not run: its tests write complex literals (`-1.0+0.0i`) unconditionally |

`time`'s second test counts down a million between readings of the clock,
and allows 0.1 s of slack. So it needs 10 million loop iterations a
second. s7st does about 14 million ("Speed").

Getting there fixed, among other things:
- datum labels, read and written, with `write` marking cycles and
  `write-shared` marking sharing;
- `equal?` on cyclic data;
- hygiene: a template's free names resolve where the macro was defined,
  skipping bindings around the use;
- `...` as a plain variable when bound;
- `let-values` binding in parallel;
- `quasiquote` with several operands to `unquote`;
- `include` relative to the including file;
- binary ports, and `delete-file` (by running `rm`);
- Unicode decimal digits and case folding (ß, final sigma).

## What is not done

- **Complex numbers.** They're optional in R7RS. Larceny's `complex` and
  `inexact` suites need them.
- **Console input.** It is empty: `read-line` and the others read string
  ports and files.
- **Deleting files** is done by running `rm`, since FX-26 has no primitive
  for it.
- **Hygiene's corners.** A free symbol a template introduces means what its
  name means where the macro was defined: its scopes, then its namespace.
  This assumes the macro's scopes enclose the use, which holds for any
  macro used inside the scope it was defined in.
- **Library details.** Every library sees the built-ins whether it
  imports them or not, and an imported name can be assigned with `set!`
  (R7RS makes that an error).

Each could be added.

## Speed

**Compiled to FX-26** (2026-10-31, `lower.fx`; Fixpt's F8). The
lowering makes plain FX-26 of what it can:
- **Locals are FX-26 variables.** Only an assigned one is a box, read
  through `%lref`, which says if it is not yet defined.
- **A `let`** (a lambda called where it is made, as the expander writes
  one) is an FX-26 `let`: no closure, no call.
- **A procedure set once, where its frame begins,** to a lambda of one
  clause (a named `let`'s loop, a body's `define`) is an FX-26 `letrec`
  procedure. A call of it with as many arguments is a direct FX-26 call.
  Its value elsewhere is one closure, made where the slot is set.
- **A call of a global** that holds one of the commonest built-ins when
  the form is lowered (`+ - * < > <= >= = eq? eqv? cons car cdr null?
  pair? not zero?`) is a fused call (`machine.fx`'s `s7-fadd` and kin).
  It does the integer or pair case in line while every built-in is where
  it was (`s7-builtins-intact`, cleared by assigning or defining a global
  that holds one), and else calls through the cell. In an `if`, a test
  gives a `bool`. Any other global's call reads the cell in the same
  call (`s7-gcall1` and kin).
- **`force` is written in FX-26** (`s7-force`), over the prelude's
  promise records.

What it takes to keep compiled code cheap, all found by profiling:
- **The module staged code is checked against is sealed:** its types
  abstract (`rt-value`), and what the code is given (its constants, cells
  and lambdas' descriptions, and the runtime's procedures) one product,
  `T`. Fixpt prints every type a stage is checked against whole: with
  s7st's value type in it, a stage took 49 ms; sealed, 8 ms.
- **Forms are staged a hundred at a time:** a definition's own code is a
  quarter of a millisecond of a stage. A batch ends before a form with a
  syntax error, which is raised after the forms before it have run, and
  after a top-level `load` or `eval`, whose definitions the next forms
  may need to be expanded.
- **A closure has few free values:** Fixpt makes one in line only with at
  most six on x86_64, else by a call-out to Rust, about a microsecond.
  Each constant in a variable of its own cost R7RS's `lazy` 16 call-outs
  a stream element. So code names `(extract T …)`.
- **The prelude is staged as the program loads** (`main.fx`'s
  `s7-ready`), so that its heap dump (`bin/heist-dump`) holds it compiled:
  a start from the dump is 0.05 s.

Measured 2026-10-31, `s7st/bench/run.sh LARCENY`, Larceny v1.3.1a2 from
`~/Dev/LangPlay/accomplice` (times per run, as before):

| benchmark                     | interpreted (CEK), no kernel | with kernels | compiled | Larceny, interpreted | Larceny, compiled |
| ----------------------------- | ---------------------------: | -----------: | -------: | -------------------: | ----------------: |
| `(fib 25)`                    |                      49.5 ms |      48.7 ms |   7.1 ms |              11.3 ms |            0.5 ms |
| `(tak 18 12 6)`               |                      12.0 ms |      11.9 ms |   1.7 ms |               4.0 ms |            0.1 ms |
| a named-`let` loop, 1,000,000 |                     108.8 ms |       2.5 ms |  25.0 ms |              52.9 ms |            1.1 ms |
| `map` over 200,000            |                     250.1 ms |     250.0 ms |  93.7 ms |              34.7 ms |           12.6 ms |
| `do` over a vector, 500,000   |                      68.0 ms |      82.5 ms |  20.4 ms |              31.1 ms |            1.4 ms |
| countdown from 10,000,000     |                     661.9 ms |      19.8 ms | 243.8 ms |             244.1 ms |            6.6 ms |

s7st is now faster than Larceny's interpreter but on `map` (Scheme here,
compiled code there). The two loops over integers were faster still as
kernels, machine code made of them by `seal-code` (`native.fx`, removed
with the interpreter): the lowering could make those again, and more,
from the same body. R7RS's `lazy` test went from 33 s to 5.5 s, `char`
from 12 s to 6.4 s, Heist's whole suite from 33 s to 9 s.

**Where the time goes now:** in `lazy`, a third is Fixpt's collector:
a pair is four objects (the sum, a product, a box each for `car` and
`cdr`), a closure five. In `char`, the procedures written in FX-26 and
called by a list (`s7-prim-apply`), such as three-argument comparisons.

### Before: an interpreter (2026-10-27 to 10-31)

s7st was a CEK machine whose continuation was data, run one step at a
time: proper tail calls, re-entrant `call/cc` and slices came from the
continuation being a list of frames. Each top-level form was compiled to
two FX-26 closures a node, its code and, where it allowed one, a
quick evaluation of its value with no machine step. Calls and returns
were made directly while fuel lasted. Loops over integers got kernels
(`native.fx`). What it found that still holds: Fixpt's code is sensitive
to where it lands (changes that do nothing at run time moved benchmarks
10–25%, steadily), so a difference under ~25% between two builds is no
evidence; and taking work off a call's path (no product returned only to
be taken apart, no state built) helped where cleverness (frames used
again, closures specialized) did not.

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

**A first analysis was built: `flow.fx`, 0CFA.** It is gone since: the
CFA (`../cfa/`, `docs/cfa.md`) analyses Scheme texts in its place, by
the same expander, and FX-26 ones too. What follows is what it was.
- **Front end.** The buffer's text is expanded by the expander that runs
  code, into a namespace of its own, so its `define`s and `define-syntax`es
  change nothing in the session. Every reference keeps its symbol's span,
  because the reader keeps each list item's place in the pair that holds
  it (`s7-src`) and the expander passes it down.
- **Abstract values.** Kinds of data (number, string, pair, `()`, vector,
  …), the text's lambda clauses, and the session's built-ins, by name.
- **The fixpoint.** The store (frame slots, the text's globals, each
  lambda's results) only grows. The top level and every lambda body are
  evaluated against it until it stops growing.
- **Calls.** A call of a lambda flows its arguments into the parameters
  and takes back its result. A built-in's result comes from a table by
  name. A lambda given to a built-in or to unknown code escapes: it is
  taken to be called with anything.
- **What it says:** at each variable's use, what can reach it (`x: number
  | string`); at each call's operator, what it can call (`calls
  #<procedure square>`).

**In the editor.** The server's `analyze` answers with these notes along
with the faces. Eldoc in a Scheme buffer shows the note at point when it
is of the buffer's current revision (`ui/s7st-flow.scm`).

What remains, as Yank's analysis has it:
- **Allocation sites**, so a pair says what it holds, and `car` of a list
  of numbers is a number.
- **Contexts (1CFA, m-CFA)**, so a procedure called from two places
  keeps their arguments apart.
- **Narrowing**: a variable under `(if (string? x) …)` is a string there.
- **The built-ins written in Scheme** (the prelude's `map`, `for-each`,
  `fold`) analysed rather than escaping lambdas to them. Their text is the
  prelude's, so the same expander and analysis apply.
- **Errors underlined**: calls of what is no procedure, and arity
  mismatches, which the analysis already sees.
- **M-. through the analysis**: to a lambda a call can reach.

### For a compiler

Done (2026-10-31): Fixpt's `stage` (`fixpt/docs/fx26.md`, "Staging code")
checks and compiles FX-26 code a program makes as it runs, and s7st
compiles Scheme to it ("Speed"). It needed Fixpt to make staged code
native code as a program's is (Heist's F8,
`docs/requests/fixpt-stage-native.md`). What is left, by what it would
give:
- **Pairs and closures made of fewer objects** (the collector is a third
  of `lazy`): a pair's two cells as one array, a closure's identity its
  code's sum, not a cell of its own.
- **Kernels again:** a lambda over integers lowered to code over raw
  integers, which Fixpt would compile to machine code as it does a
  program's.
- **`map`, `for-each`, `append` and the like written in FX-26,** as
  `force` now is.
- **Types where the lowering can see them,** so that a known procedure's
  call needs no dispatch, and an integer no box.

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
| eldoc, in those buffers and *s7st* | the flow analysis's note at point, if there is one (`x: number`, `calls #<procedure square>`); else what s7st knows of the name at point, or of the operator of the call around it: `(map f l . ls)`, `car: 1 argument`, `guard: a macro`, `x = (1 2)`. Eldoc does not start s7st. |

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
