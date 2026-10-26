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

## Status (2026-10-26)

**Stage 1, names (`editor/resolve.fx`): done.**
- **What it resolves:** each use goes to its binder by scope: lambda,
  `vlambda` and `plambda` parameters, `let`, `let*`, `letrec`, the
  `letregion` family, `tagcase` arm names, `typecase` names, and a
  module's items over the file's definitions. Quoted data, `case` data,
  labels and tags are not uses. It takes 1.4 ms for 2,000 to 3,000
  references.
- **Links:** imports are followed. Each annotation records, for every
  name a top-level `import` brings in from a module defined by
  `load-module` or `load-input`, the file it comes from (`fx26:name` being
  Fixpt's sources).
- **M-.** goes to the binder, and through an import on into the file the
  name comes from. From the editor's own `syntax.fx` it reaches Fixpt's
  `eager-reader.fx`.
- **M-?** marks a binder's uses, and M-n and M-p move among them. This is
  a syntactic find-uses, which yank never had.

**Stage 2, closure flow (`editor/flow.fx`, `editor/calls.fx`): first
version.**
- **What it computes:** at 0CFA, the lambdas, sites (product, sum, ref,
  pair) and unknown that reach each variable, field and lambda's result,
  in whole passes until the store stops growing.
- **What it serves:** C-c e (what a call can call) and C-c r (what can
  call this lambda), listed in `*xref*`.
- **The editor itself:** 14 files, 1,169 calls and 456 lambdas, in 8
  passes and about 20 ms. No call may reach unknown code. `in-buffer`'s
  `(c b)` reaches exactly the 28 commands `buffer.fx` makes, plus
  `goto-position`, and C-c r on `move-by`'s command lambda finds that one
  call.
- **Fixpt's front end:** 174 files and 41,000 lines, read in 0.45 s and
  analysed in 0.2 s, in 11 passes. It was 4 s before the global names
  were hashed and the numbering stopped being quadratic.
- **What it does not do yet:**
  - **Contexts.** Small procedures are not analysed per call site, so
    the results of a helper used everywhere merge.
  - **Constructors made by `define-datatype`,** which only Fixpt's parser
    expands. Their values are not tracked.
  - **Calls made by the runtime.** The handlers of `attempt` and the
    branches of `race` are not calls in the text. Code they call looks
    unreached, though its body is analysed.
  - **Standard procedures that keep or call what they are given,**
    besides the few named. `fx26:table.fx`'s hash and equality are an
    example: closures given to them do not escape, which is unsound for
    callers. The standard environment's types would say which these are.
  - **Names merged across files.** Globals are merged by name across the
    files of a directory. That is right for a program in several files,
    such as the editor, and wrong for unrelated module files that reuse
    names. That is the case in Fixpt's sources, where the merge makes
    results imprecise.
  - **Warm starts after an edit.** The analysis runs whole, on demand.
