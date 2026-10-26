# Analysis of FX-26 in the editor: the plan

This note is about what the editor should know of FX-26 code beyond its
syntax: what a name refers to, where a value goes, and which closures a
call can reach. It is based on a review of yank's analysis on `main` at
abe5091 (`src/yank/analysis/`, `src/yank/scheme/{resolve,flow,index}.sld`,
`commands/xref.sld`, and the measurements in its DONE.md and TODO.md).

## What Fixpt gives, and what it does not

- **Reading:** Fixpt's own reader (`fx26:eager-reader.fx`) gives syntax
  with a span on every atom, and the editor uses it incrementally
  (`editor/syntax.fx`).
- **Parsing:** Fixpt's parser (`fx26:parser-top.fx`) gives `top` and `exp`
  trees, with a span and an id on each node. Imports, `let*`, `cond` and
  `typecase` are already expanded.
  - Variables are unresolved: `(e-var symbol start end id)`.
  - Binders' names have no spans: lambda parameters, `let` names and
    `tagcase` arm names are bare symbols.
- **Checking:** the checker resolves every name as it checks
  (`check-env.fx`, `k-lookup`) but keeps no record of it. It also keeps
  no types by span, only effect summaries (Fixpt TODO §25).
  - `check-resolve.fx` is something else: it turns parser trees into the
    checker's representation.
- **Flow analysis:** none.

So the editor's resolver and its CFA have to be written. That was R10 of
`fx26-for-yank.md` from the start.

## What yank teaches

- **M-. needs names only.** Yank's M-. never consulted its CFA. It used
  the import form, a desugaring to find local binders (`binder-at`), a
  textual resolver for library imports (`resolve.sld`), and the index.
- **M-? (find uses), values at point, callees at a call, and eldoc's
  inferred signatures need the CFA.** Yank's M-? was CFA-based: calls
  whose operator can be a closure of this lambda. A syntactic
  `references-to` existed, but nothing used it.
- **Measured** (yank DONE.md and TODO.md, as of 2026-10-25):
  - m-CFA has k-CFA's precision at a half to a seventh of the cost, and
    k-CFA's depth beyond 1 bought nothing.
  - What made it fast: interning values and contours, joins that stop at
    the list joined last time, splitting on records only where they hold
    procedures (220 s to 11 s), and making a set that holds "unknown" drop
    its data.
  - Hash-consed intsets made it slower, and were dropped.
  - Warm continuation after an edit takes 1 to 30 steps instead of 32,147,
    with nodes numbered by definition so that an edit renumbers only its
    own definition.
  - What remains costly: yank's 76-file world takes 2.6 s at 0CFA and
    68 s at m-CFA 2, and half its procedures' parameters are still
    "unknown". The sources of "unknown" are escaped procedures, `guard`
    handlers, `dynamic-wind` thunks and `eval`.
- **Corrections to R10 in `fx26-for-yank.md`:**
  - The intsets were tried and dropped.
  - The memo table abandoned "for lack of weak tables" belonged to that
    intset trial.
  - The 5.4 s and 1.9 s figures are from a 40-file world of 2026-10-13.
  - The analysis is about 37% of yank's source, not 55%.

## The stages

1. **Names** (`editor/resolve.fx`).
   - **What it is:** a pass over the reader's syntax, giving for each
     symbol that is a use the binder it refers to: a local (a `lambda`
     parameter, a `let` or `letrec` name, a `tagcase` arm's names, a
     `typecase` name), a definition at the top level or in a `module`, or
     nothing known (a standard name, or another file's).
   - **Why the reader's trees:** binders have spans there, and the syntax
     actor already keeps them, read incrementally.
   - **What it serves:** precise M-., and a syntactic M-? (uses of a name,
     which yank never had), and highlighting a name's other uses.
   - **What it leaves out:** `with`, `import` and `load-module` are
     followed by name only at first. Following them properly is yank's
     `link.sld` job, here by recognising the usual shapes of module
     expressions.
2. **Closure flow** (`editor/flow.fx`), on Fixpt's parser trees, which
   have node ids.
   - **What it is:** "which lambdas reach which calls", at 0CFA, with
     small procedures analysed per call site.
   - **Kept from yank:** its worklist of tasks with cells that remember
     their readers; interned values and contours; results by node, keyed by
     definition so that a warm start after an edit is cheap; time slices.
   - **Dropped from yank, since FX-26 is typed:** k-CFA; the models of
     first-order primitives, since a primitive's result is any value of its
     type; the arity warnings and car-of-non-pair warnings, which the
     checker gives; and most of the "unknown" machinery, which becomes
     "any value of type T" once types are kept by span.
   - **Where it runs:** in a process of its own, since the trees are
     immutable data and can be sent. That needs measuring against copying
     costs.
   - **What it serves:** M-? by flow, callees at a call, and values at
     point.
3. **Types** (needs Fixpt): the checker keeping types and instantiations
   by span (Fixpt TODO §25).
   - **What it serves:** type at point and eldoc, and type arguments as
     the flow analysis's context. Yank found the context that mattered was
     what kind of value comes in, which is what a type argument says.
