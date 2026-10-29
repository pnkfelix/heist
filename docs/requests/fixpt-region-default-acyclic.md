# Request to Fixpt: a region nothing chooses could be `acyclic`

Status: done in Fixpt e4af8997 (pulled 2026-10-29), the prototype taken
as written; Fixpt's suite 962 of 962, with the five tests that asserted
the old regions updated. Drafted 2026-10-29 by Heist, against Fixpt
61a2e792, prototyped in a scratch build (`bench/region-default-acyclic.diff`).

## Summary

When a call instantiates a `poly`'s region binder and nothing at the call
says which region it is, both checkers make it a fresh region (`@r.1`).
A list made there is not `acyclic`. It cannot be given to a procedure
that takes `(listof a (acyclic p))`, nor bound where an `acyclic` list
is declared, unless the programmer says `(the (listof T acyclic) …)`.

Heist's library `kit` (`docs/kit.md`) follows two conventions:
- lists it is given are `(listof a (acyclic p))`;
- lists it makes are at a region `r` the caller chooses, and no
  procedure writes `r`.

Adopting it in ratfink took **101 annotations at 366 calls**. kit
replaced ratfink's own `map`, `filter` and `for-each`, which returned
`acyclic` lists. Each annotation is `(the (listof T acyclic) …)`, some
with `T` a long `productof`.

Heist asks that a region binder nothing solves be `acyclic` when the
`poly` only makes data there: no `ref`, array or continuation is at that
region, and no effect writes it. Prototyped in both checkers, ratfink
compiles with none of the 101 annotations, and runs the same.

## Where the region is not chosen

The context's expected type solves `r` when there is one: in an
argument, in a `define` with a type, in the body of a `lambda` with a
declared type, and in an `if` with an expected type. It is not solved in
the cases below. In each repro, `map` is kit's, `len` takes a `(listof
int acyclic)`, and `xs` is one.

| shape | example | error on 61a2e792 |
| --- | --- | --- |
| a `let` binding | `(let ((ys (map inc xs))) (len ys))` | argument 1 is a `(listof int @r.1)`, where a `(listof int acyclic)` is expected |
| an `if` in a binding | `(let ((ys (if (null? xs) xs (map inc xs)))) (len ys))` | the branches are a `(listof int acyclic)` and a `(listof int @r.1)` |
| a `lambda` given to a `poly` | `(map (lambda ((l (listof int acyclic))) (map inc l)) xss)`, into a `(listof (listof int acyclic) acyclic)` | argument 1 is a `(subr … (listof int @r.1))`, where a `(subr … (listof int acyclic))` is expected |
| a call's result given to a `poly` | `(len (map inc (map inc xs)))` | `` `p` cannot be inferred `` |
| a primitive's list given to a `poly` | `(map inc (list 1 2 3))`, `(map inc (reverse xs))` | `` `p` cannot be inferred `` |

The last two are one case. The inner call's region is made fresh before
the outer call's `(acyclic p)` sees it, so nothing matches `p`.

In ratfink, about 70 of the 101 are the first shape: a kit result bound
by `let` or `let*`, then used as an `acyclic` list.

## The prototype

`default_regions` (`infer.rs`) and `k-default-free` (`check-binders.fx`)
give an unsolved region binder `(acyclic heap)` in place of a fresh
region. The exception is a binder the `poly`'s type uses other than as a
pair's region, or in an effect other than `alloc` or `read`. Such a
binder stays fresh. It is found by walking the type: `not_only_data_regions`
in Rust, `k-not-only-data` in FX-26.

The instantiation is still checked. A default is therefore no less sound
than the `(the (listof T acyclic) …)` the programmer writes today.
Allocating at `acyclic` is already pure, so a caller's effect loses the
`(alloc @r.N)` it had, and gains nothing.

The first version defaulted every binder to `acyclic`. Fixpt's tests
showed which binders must stay fresh:
- a continuation's region: `cwcc_with_a_fresh_region_is_masked`, where
  `(goto acyclic)` is not masked, and `a_licensed_expression_runs_early`;
- a `ref`'s region: `the_checkers_facts_are_in_the_lowered_code` lost its
  `no-escape`;
- a `poly` that declares `(write r)`:
  `masking_keeps_writes_to_the_results_regions`.

The narrowed rule passes those four in the Rust checker. Heist did not
run Fixpt's suite once both checkers had it.

The rule changes some behaviour that tests assert. Each of these tests
expects the old behaviour, so they need updating if the request is taken:
- A type printed with `@r.1` now prints `acyclic`
  (`a_projection_is_inferred_from_the_arguments`,
  `literals_check_against_any_fixed_width`,
  `nil_is_of_the_type_nil_where_nothing_says_which_list`).
- `(length (list 1 2))` now checks (`length_of_an_acyclic_list`).
- `modules/list-joined-with-nil.fx` now runs.

Results with the narrowed rule:

- The repros above all pass.
- ratfink with the 101 annotations taken out compiles in full. On
  61a2e792, 15 of its 16 module files are refused.
- That ratfink, run on the default-everything build, gives the same
  reports and SMT logs as shakedown on Heist's corpus: 123 of 124. The
  exception is `examples/contracts`, whose SMT text already differed
  before kit.

## Compatibility

Code may write a list it got from such a call, where the `poly` itself
doesn't write it: `(set-car! (map f l) …)`. That list was at a fresh
region, and it would now be at `acyclic`, so the write would be refused.
The narrowed rule cannot see the caller's write. The caller must then
say the region, `(the (listof T r) …)`. Heist has no such code, and no
test in Fixpt's suite failed this way.

There is an alternative that keeps fresh regions. Where an `(acyclic p)`
is wanted, a fresh region the program never writes could be taken as
one. That is more work, since the region is chosen at one call and found
unwritten later. Heist has not prototyped it.

## The prompt

When nothing at a call solves a `poly`'s region binder, it is made a
fresh region (`infer.rs` `default_regions`, `check-binders.fx`
`k-default-free`). A list made there is not `acyclic`. That costs a
library that makes lists at a caller's region `r` and takes lists as
`(listof a (acyclic p))`, which Heist's `kit` does: its callers must
write `(the (listof T acyclic) …)` wherever a result is:
- let-bound;
- returned by a `lambda` given to another `poly`;
- given straight to another such procedure, which fails with "`p`
  cannot be inferred".

Heist's ratfink needed 101 such annotations at 366 calls.

Could a region binder nothing solves be `acyclic`, when the `poly` uses
it only as a pair's region and its effects only `alloc` or `read` it?
Heist prototyped that in both checkers, in
`docs/requests/bench/region-default-acyclic.diff` (181 lines). With it,
the repros in `docs/requests/fixpt-region-default-acyclic.md` pass, and
ratfink compiles without the 101 annotations and runs the same. Fixpt's
tests that rely on a fresh region for continuations, `ref`s and declared
writes pass with the narrowed rule in the Rust checker. Five tests assert
the old printed types or refusals and would need updating.
