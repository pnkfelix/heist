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
| `flow.fx`     | a flow analysis of a text, 0CFA: what can reach each variable, what each call can call                                                      |
| `native.fx`   | loops over integers compiled to x86_64 machine code: kernels ("Speed")                                                                       |
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

**Each top-level form is compiled before it runs** (`machine.fx`'s
`s7-compile`). Every node of the core becomes two FX-26 closures, made
once:
- **Its code** takes the environment, continuation and dynamic state, and
  returns the machine's next state.
- **Its quick evaluation,** where the node allows one, gets the node's
  value with no machine step: constants, variables, lambdas, `if` and
  sequences of such, and calls of pure built-ins on such. It returns the
  value itself, or undefined if it cannot finish. No wrapper is made,
  since in Fixpt every sum is an object allocated.

A call of a closure with one clause, given the right number of quick
arguments, fills the new frame's slots directly.

**Calls and returns made directly, paid for by fuel.** The machine's code
is in continuation-passing style over a continuation that is data, so
each piece of code ends by calling the next in tail position, and FX-26's
tail calls take no native stack. So a call goes straight into the
callee's code (`s7-enter`), and a return straight into the frame on top
of the continuation (`s7-return`). Neither builds a state for `s7-step`.
Each uses a unit of `s7-fuel`, the slice's budget, as a step does. With
none left, the state is built and the slice ends as before, so slices
are as long as they were and an interrupt is seen within about a
millisecond.

A quick evaluation that cannot finish (a variable not
yet defined, an operator that turns out not to be a built-in, an error)
has done nothing another could see, since it calls only pure built-ins.
The node's code then runs it the slow way, and reports the error if
there is one.

A call gets a quick evaluation only if its operator is a global that
holds a pure built-in when the call is compiled. Otherwise a closure's
call would be evaluated twice: tried quickly, given up, then done.

**Fast entries.** The commonest pure built-ins (`+ - * = < > <= >=`,
`eq?`, `eqv?`, `cons`, `car`, `cdr`, `pair?`, `null?`, `not`, `zero?`,
`vector-ref`, `vector-length`) also have an entry for one or two
arguments (`s7-prim`'s `fast`, `prims.fx`'s `s7-init-fast!`). It is
called with no list made, and answers undefined for a case it does not
cover, such as an error or a non-integer. Variables at depth 0 and 1 are
read with no loop (`s7-local-getter`).

On this machine, measured in the program itself with `current-jiffy`:

| benchmark                     | evaluating nodes | compiled | quick values unwrapped, fast entries | Fixpt b7b60d98 | calls and returns direct |
| ----------------------------- | ---------------- | -------- | ------------------------------------ | -------------- | ------------------------ |
| `(fib 25)`                    | 242 ms           | 100 ms   | 65 ms                                | 56 ms          | 49 ms                    |
| `(tak 18 12 6)`               | 69 ms            | 26 ms    | 15 ms                                | 14 ms          | 11 ms                    |
| a named-`let` loop, 1,000,000 | 1209 ms          | 333 ms   | 196 ms                               | 142 ms         | 107 ms                   |
| `map` over 200,000            | 731 ms           | 455 ms   | 398 ms                               | 336 ms         | 314 ms                   |
| `do` over a vector, 500,000   | 729 ms           | 221 ms   | 119 ms                               | 93 ms          | 68 ms                    |

**Where the time goes now** (`FIXPT_PERF_MAP=1 perf record`, Fixpt's
`docs/performance.md`): s7st's own machinery, a few nanoseconds at a
time. Frames and pairs at region `@sc` were call-outs to Rust, 30–50 ns
each. Since Fixpt b7b60d98 (Heist's request,
`docs/requests/fixpt-region-alloc-inline.md`) they are made in line. A
self-calling loop now takes ~70 ns an iteration, about 14 million a
second. Larceny's `(scheme time)` test needs 10 million.

**Fixpt's code is sensitive to where it lands.** Changes that do nothing
at run time move benchmarks by 10–25%: `vec5e5` went 715 → 891 ms when
a lambda that is never run was added to `s7-compile-in`, and 770 → 842
ms when the code that queues kernels was made unreachable. Each result
is steady from run to run, so it looks like the alignment or cache
placement of compiled code. A difference under ~25% between two builds
is therefore not evidence that one is better. The results below may be
partly that.

**Tried, and slower** (2026-10-27), on Fixpt b7b60d98:
- *A loop's frame used again* by a call of its lambda in tail position:
  each frame stamped with how many continuations had been captured, and
  reused only if none had been since, and if no lambda or inner scope in
  the body could hold it. Countdown went from 775 to 840–940 ms. A fresh
  frame is cheap now, and checking whether one can be reused costs more.
- *A closure specialized for one or two arguments* to fill a frame,
  instead of `s7-quick-into`'s walk over a list: 700 to 780 ms. In Fixpt,
  a known global function is cheaper than another closure captured.
- *Naming the compiled lambdas* with `let`, for profiles, costs ~8%. The
  names help in `perf`, so name them in a scratch copy when profiling.

What helped instead was taking work off the call's path: no product
returned only to be taken apart (`s7-new-frame`'s), no state built for a
step.

**Loops over integers, as machine code** (`native.fx`, 2026-10-27).
Fixpt's `seal-code` and `native-procedure` let a program make machine code
and call it. They work on x86_64 here, though Fixpt's `docs/fx26.md`
says arm64 only.

- **Which lambdas get a kernel:** one clause, no rest argument, no
  internal definitions, and a body made only of:
  - `if`;
  - integers: constants, the parameters, and free variables of the
    lambdas around it;
  - `+ - *` and `= < > <= >= zero?`, as the built-ins hold them when the
    body is compiled;
  - other constants, as results;
  - calls of itself in tail position.

  The lambda is compiled as before, and also to x86_64 code, a *kernel*.
- **How it is made:** the instructions come from Fixpt's encoder written
  in FX-26 (`fx26:x86_64.fx`). Each node shape is a fixed run of
  instructions with its slots, constants and labels filled in: copy and
  patch, as stencils are. A small two-pass assembler places the labels.
- **What it touches:** the kernel is a leaf. It calls no routine of the
  runtime and allocates nothing, so no collection can happen while it
  runs, and it needs no frame or stack map. It works on raw 64-bit
  integers in a scratch bloblet's suffix.
- **When it is made:** compiling the lambda only queues it. The kernel is
  made between slices, by `s7-continue!`, so that making machine code
  (`(io native)`, the encoder's region `@k`) is in the effect of what
  drives the machine (`s7-drive-eff`), not of the code the machine runs.
  The lambda's code first looks for its kernel, and runs its body as
  before until there is one.
- **When it is used:** entering the body checks first that the
  built-ins are where they were, that the variable it calls itself
  through still holds it, and that every input is an integer below
  2^60. Otherwise the call is made as before.
- **How it hands back:** an overflow gives up, and so does using up its
  million iterations, after which the slice ends. Either way the kernel
  hands back the arguments of the call of itself it was about to make,
  and the machine makes that call the slow way. That is safe because the
  body changes nothing. Past 64 bits, the slow way goes on in bignums.
  `tests/kernels.scm` covers these cases.

| benchmark                       | before kernels | with kernels |
| ------------------------------- | -------------- | ------------ |
| a named-`let` loop, 1,000,000   | 107 ms         | 2 ms         |
| countdown from 10,000,000       | 700 ms         | 19 ms        |

Start-up grew 0.3 s, for checking the encoder and `native.fx`. `fib`
and `tak` get no kernel: their calls of themselves are not in tail
position. Neither do the `map` and vector benchmarks, which use lists
and vectors.

**Against Larceny** (2026-10-27, `s7st/bench/run.sh LARCENY`, on the same
machine; Larceny v1.3.1a2 from `~/Dev/LangPlay/accomplice`). Times are
per run: s7st's the mean of 3, Larceny's compiled the mean of 20.
"Interpreted" is Larceny's own interpreter (`(evaluator interpret)` at its
R7RS REPL), itself compiled to machine code by Twobit. "Compiled" is
Larceny running the benchmark as a program (`-r7rs -program`), which
Twobit compiles to machine code.

| benchmark                       | s7st, before kernels | s7st, with kernels | Larceny, interpreted | Larceny, compiled |
| ------------------------------- | -------------------- | ------------------ | -------------------- | ----------------- |
| `(fib 25)`                      | 49.5 ms              | 48.7 ms            | 11.4 ms              | 0.5 ms            |
| `(tak 18 12 6)`                 | 12.0 ms              | 11.9 ms            | 4.0 ms               | 0.1 ms            |
| a named-`let` loop, 1,000,000   | 108.8 ms             | **2.5 ms**         | 52.9 ms              | 1.1 ms            |
| `map` over 200,000              | 250.1 ms             | 250.0 ms           | 34.2 ms              | 13.0 ms           |
| `do` over a vector, 500,000     | 68.0 ms              | 82.5 ms            | 31.4 ms              | 1.2 ms            |
| countdown from 10,000,000       | 661.9 ms             | **19.8 ms**        | 245.1 ms             | 4.7 ms            |

The two loops over integers now run as kernels ("Loops over integers, as
machine code"), within 2–4× of compiled Larceny. The vector loop gets no
kernel. Its 68 → 82 ms is the code-placement sensitivity described above:
none of its code changed.

- **On calls and loops without a kernel,** s7st is 2–4× slower than Larceny's interpreter.
- **`map` is not a like comparison.** Larceny's interpreter calls `map`
  and `length` compiled to machine code. s7st's `map` is Scheme, in its
  prelude, run like the program's own code. As FX-26 built-ins, they
  would close most of the gap.
- **Compiled Larceny is 20–140× faster.** Closing that takes code made
  at run time: machine code by `seal-code` ("Openings").

`(fib 25)` is 250,000 calls, so about 5 million procedure calls a second.
The same `fib` written in FX-26, which Fixpt compiles to native code, is
still much faster. FX-26 has no way to make FX-26 code at run time
("Openings").

- **Start-up** is 3.7 s, nearly all of it Fixpt compiling s7st's 6,500
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

**A first analysis is built: `flow.fx`, 0CFA.**
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

**FX-26 has no `eval`.**
- `load-module` is resolved when a program is checked, not when it runs.
- The only code a program can make at run time is machine code, through
  `seal-code` and `native-procedure` (`fixpt/docs/fx26.md`, "Code a
  program makes"). Fixpt's doc says this works only on arm64, but that is
  out of date: on this x86_64 machine `native-code?` is true, and
  `fixpt/crates/fixpt-fx26/tests/programs/made-code-x86_64/leaves.fx`'s
  hand-assembled adder runs (checked 2026-10-27).

So s7st can't compile Scheme to FX-26 and run the result in the same
process. What it can do:

1. **Compile to closures, within the interpreter.** This is done ("Speed").
2. **Compile to FX-26 text and run it as a separate process.** Heist runs
   processes already (`editor/process.fx`). The FX-26 checker would then
   type the result, and Fixpt's native machines would run it. Scheme's
   dynamic typing becomes a union type, as `datum` is. `call/cc` needs a
   CPS translation or FX-26's one-shot continuations, which are enough for
   escapes, generators and `guard`.
3. **Machine code** through `seal-code`. Begun, for loops over integers
   (`native.fx`, "Speed"). For the rest: x86_64 and
   arm64. It must keep the native convention (`define-convention`,
   `fixpt/docs/research/declared-conventions.md`): frames, the collector's
   maps, the write barrier. Fixpt's own back end written in FX-26
   (`native-x64.fx`, the `fx-cells-fxjit-cellcc` machine) shows what an
   FX-26 program must do to emit such code, and has an assembler to start
   from.

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
