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

## Depth: m-CFA measured (2026-10-26)

`flow.fx` is m-CFA with its depth a setting (`set-flow-depth!`):
- **contours** are the last `m` call sites;
- **closures** are a lambda and the contour it was made in;
- **free variables** are copied into the callee's contour;
- **locals** are addressed by contour; globals and allocation sites have one
  address each.

Depth 0 is 0CFA, and gives what the analysis gave before. Measured on the
editor's own files (`fast`):

| depth | time | tasks | calls reaching several lambdas | values locals can hold, merged | locals holding several |
|---|---|---|---|---|---|
| 0 | 22 ms | 666 | 9 | 2,551 | 317 |
| 1 | 665 ms | 3,477 | 9 | 2,467 | 317 |
| 2 | 3,999 ms | 14,095 | 9 | 2,467 | 317 |

On Fixpt's front end (174 files), depths 0, 1 and 2 took 0.27 s, 57 s
and 295 s. Each found the same 117 calls reaching several lambdas, and
the same 13,133 callees in all.

So, on these programs:
- **What a call can call** (C-c e, C-c r) is the same at every depth.
  That answer is per call site, merged over contours, and no spurious
  closure reached a call through a context's merge.
- **What locals can hold** is 3% smaller at depth 1, and no smaller at
  depth 2.

This fits yank's finding, that context pays where values are merged
(its unknown parameters), not in callee sets. It is also not a verdict
on m-CFA against k-CFA: those differ only above depth 0, and that
comparison was not run. The editor runs at depth 0. Depth stays a
setting, to measure again on code that passes closures through shared
helpers more.

**Cost of depths above 0:** contours are interned by recursion over
their calls through hash tables, and cells are in a hash table keyed by
variable and contour. Neither was tuned, since depth bought nothing here.

## Constructors, and small procedures by call site (2026-10-26)

- **`define-datatype` constructors** are now global lambdas making
  `(sum tag (product (1 …) (2 …) …))`, as Fixpt's parser expands them.
  `tagcase` arms tell `(tag x …)` (the payload) from `(tag (x …) …)` (its
  fields by position). On the editor, callees in all rose from 2,027 to
  2,166: calls to constructors now reach them, where before they reached
  nothing.
- **Small procedures by call site** (yank's `call-site-size`): a named,
  non-recursive lambda of `small-size` nodes or fewer gets each call site
  as its contour, even at depth 0, and lambdas made in it are called in
  the contour they were made in. Measured at depth 0:

  | program | small size | time | tasks | values locals hold | locals holding several |
  |---|---|---|---|---|---|
  | editor | 0 | 25 ms | 697 | 3,051 | 448 |
  | editor | 40 | 150 ms | 2,560 | 3,051 | 448 |
  | Fixpt front end | 0 | 382 ms | 5,184 | 57,171 | 2,359 |
  | Fixpt front end | 20 | 4.1 s | 14,231 | 54,240 | 2,305 |
  | Fixpt front end | 40 | 6.7 s | 16,315 | 52,579 | 2,294 |

  - **What it bought:** nothing in the editor, and 8% fewer values in
    Fixpt's front end. No call's callees changed in either. Yank had a
    third fewer parameter values, for 15% more time.
  - **What it cost:** 6 to 18 times the time. That is the store more than
    the idea: cells in a contour other than the empty one go through
    `fx26:table.fx`'s generic hash table (a closure call to hash, buckets
    as association lists). A faster store for contours, an array per
    lambda's contours say, is what to try before turning it on.
  - **The default** is `small-size` 0 (off), and it is a setting
    (`set-small-size!`).
- **So far,** neither depth nor small procedures has changed what a call
  can call, in either program. The precision that matters to C-c e and
  C-c r came from modelling data (products, sums, refs, pairs) and
  constructors, not from context.

## Correction: the cost was a hash, not the table (2026-10-26)

The costs above for depths 1 and 2, and for small procedures, were
wrong, and so was the explanation given for them: "the generic hash
table". That was a guess, never measured.

**What `perf` showed** (`FIXPT_PERF_MAP=1`, Fixpt's perf-map support):
60% of the time was in `fx26:table.fx`'s `bucket-find`, under
`contour-of`.
- The table picks a bucket as the hash modulo a power of two.
- `flow.fx` hashed its integer keys by the identity, and packed them as
  `a * 2^20 + b`.
- For contours, `b` (the rest of the contour) was nearly always 0. So
  every contour went into one bucket, and each lookup scanned all of
  them. Cell keys had the same flaw.

The hash now brings both halves into the low bits. The table was never
the problem.

**Measured again** (`fast`, depth 0 unless said):

| program | setting | time | tasks | values locals hold | locals holding several |
|---|---|---|---|---|---|
| editor | depth 0 | 25 ms | 697 | 3,051 | 448 |
| editor | depth 1 | 133 ms | 3,687 | 2,967 (−3%) | 448 |
| editor | depth 2 | 1.4 s | 15,285 | 2,967 | 448 |
| editor | small 40 | 70 ms | 2,560 | 3,051 | 448 |
| Fixpt front end | depth 0 | 0.39 s | 5,184 | 57,171 | 2,359 |
| Fixpt front end | depth 1 | 1.6 s | 20,495 | 45,933 (−20%) | 2,173 (−8%) |
| Fixpt front end | depth 2 | 15.9 s | 63,901 | 44,126 (−23%) | 2,172 |
| Fixpt front end | small 40 | 0.87 s | 16,315 | 52,579 (−8%) | 2,294 (−3%) |

What follows from the corrected numbers:
- **What a call can call** is the same at every setting, in both
  programs. C-c e and C-c r stay at depth 0.
- **What variables hold** improves with context in Fixpt's front end:
  20% fewer values at depth 1, for 4 times the time. A display of
  values at point, which the editor does not have yet, would want depth
  1.
- **Small procedures by call site** cost 2.2 times for 3.1 times the
  tasks. That is what whole passes cost; a worklist that re-runs only
  the tasks whose inputs grew, as yank's does, is the next saving.

## Stage 3, types: a first piece (2026-10-26)

**C-c t** marks the expression at point and shows its type in the echo
area, or why the program does not check there.
- **How:** it asks Fixpt's checker through a new primitive, `type-at`
  (FIXPT-CHANGES.md F3). The checker written in Rust checks the program's
  text, keeping each expression's type, up to the form at point.
- **What "the program" is:** a directory with a file named `program`
  (one file a line, in order) is checked as that program. That is how
  `bin/heist-edit` runs the editor too. Any other file is checked alone.
- **Measured:** 21 ms near the start of the editor's 220 KB program,
  0.44 s near its end.

**Not yet:**
- **Types by name.** They are printed expanded, so a command's type is
  hundreds of characters.
- **Hovering** (eldoc-style signatures as point moves).
- **Instantiations at a site,** as context for the flow analysis.
- **Checking past an error** before point.
