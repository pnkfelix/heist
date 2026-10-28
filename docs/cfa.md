# The CFA: a flow analysis of FX-26 and Scheme, as a program of its own

`cfa/` is a control-flow analysis written in FX-26 that analyses programs
written in either FX-26 or Scheme. It runs as its own process,
`bin/cfa --serve`, which the editor queries asynchronously, as it queries
s7st. It is modelled on yank's analysis (`~/Dev/Emacs/yank`,
`src/yank/analysis/`). It is to replace the two analyses Heist has had
until now: `editor/flow.fx`, an FX-26 analysis that runs in the editor,
synchronously; and `s7st/flow.fx`, a Scheme analysis that runs in s7st's
server.

## Shape

- **The core** (`cfa/core.fx`) is the language analysed, whatever the
  program was written in. It is `editor/flow.fx`'s core, plus data kinds
  (`k-const`), primitives (`k-prim`) and numbered references.
  - Every variable, lambda, call, allocation site and reference is
    numbered.
  - A name a world defines nowhere is a primitive of its language.
- **A language** (`cf-lang`) says what calling each of its primitives
  does (`cf-model`):
  - `m-data`: data of some kinds, and whether what it is given escapes;
  - `m-pass`: its arguments passed on;
  - `m-map`: its first argument called on the elements of the lists after
    it.
  The engine knows neither language.
- **Front ends:**
  - `cfa/fx26.fx` reads with Fixpt's own reader and desugars as
    `editor/flow.fx` did. FX-26's types make nearly every standard
    procedure first order.
  - `cfa/scheme.fx` expands with s7st's own expander, so macros expand as
    they would when run. It then turns frame slots into variables, and
    turns `cons`, `car`, `list`, `vector` and `set-car!` into sites and
    fields. Builtins are modelled by `s7-builtin-result`. A builtin escapes
    its arguments unless it is first order (arithmetic, predicates,
    strings, output).
  - The program `bin/cfa` runs is s7st's files, all but `main.fx`, then
    `cfa/program`.
- **The engine** (`cfa/engine.fx`) is an m-CFA (Might, Smaragdakis and
  Van Horn) with yank's worklist.
  - A task is a closure in a contour, or the top level.
  - Each cell keeps the tasks that read it, and a cell that grows queues
    them again.
  - `cf-step! fuel` runs a slice.
  - An escaped site makes its fields unknown, and so does anything stored
    into it later.
- **Notes** (`cfa/notes.fx`):
  - At each use of a variable, what can reach it (`n: int`, `f: inc |
    dec`).
  - At each call's operator, what it can call (`calls inc | dec`), where
    that is more than one primitive.
- **The server** (`cfa/serve.fx`) has a dataset of texts by file.
  - A file's *world* is what is analysed with it. For an FX-26 file, that
    is every `.fx` file of its directory, as `editor/calls.fx` has it; for
    a Scheme file, the file itself.
  - `notes` is answered once the world is analysed as the dataset has it.
  - A `file` request for a world being analysed stops that analysis, and
    it starts again.

## Measured

On the editor's own 20 files as one FX-26 world, there are 9,855 notes.
`bin/cfa` takes 1.8 s at depth 0 and 2.4 s at depth 1, start-up included.

## Next

1. **The editor as a client** (`editor/cfa.fx`): done.
   - C-c f says the note at point. C-c e lists what the call at point can
     call, and C-c r what can call the lambda point is in; both are the
     server's `callees` and `callers` queries.
   - Eldoc shows a note where an FX-26 text declares no type. In a Scheme
     buffer, notes come in place of s7st's, unless a note only says a
     name holds its own procedure.
   - A Scheme buffer starts `bin/cfa --serve`, as it starts s7st; an
     FX-26 one waits for the first C-c f, e or r. From then on every
     FX-26 and Scheme buffer's revisions are sent as they are made
     (`flow-attach`).
   - `editor/flow.fx` and `s7st/flow.fx` are gone.
2. **Types and regions as values** (FX-26): done, where the text says
   them.
   - A `plambda`'s binders, and a module file's `(module-parameters ((r
     region) …))`, are variables. Each `proj` gives them its arguments
     (`k-inst`): a region, a type's name, or another binder's values.
     `(proj (load-module "f") …)` of a world file gives `f`'s binders.
   - A type variable used in a type is a reference to it, so it gets a
     note (`r: @ed | @sc`).
   - A call's note says its callees' declared effects, with each binder
     said by what reaches it (`calls make-box; effect (alloc @ed)`).
   - Not seen: instantiations the checker infers with no `proj`.
3. **Yank's lessons not yet taken:**
   - per-definition numbering and warm continuation after an edit;
   - a set holding unknown dropping its data;
   - small procedures analysed per call site;
   - narrowing by tests;
   - interned sets.
4. **Worlds across languages.** s7st's builtins are FX-26 code
   (`s7st/prims.fx`): a Scheme world could link to them.
