# Request to Fixpt: masking hides a write that makes `acyclic` data cyclic

Status: open. Drafted 2026-10-29 by Heist, for the user to take to the
Fixpt team. Against Fixpt 6505d8bb. Found while designing `kit`, Heist's
library of FX-26 procedures, whose `map` relies on a procedure that does
not write a region being safe to instantiate at `acyclic`.

## The bug

A procedure polymorphic in a region `r` can write data it allocated in `r`
and returned, and declare only `(alloc r)`: masking drops the write. The
procedure can then be instantiated at `acyclic`, and a walk that both
checkers accept as `pure` and terminating loops forever. Repro, on Fixpt
6505d8bb:

    ;; Declares only (alloc r), but ties its result into a cycle.
    (define f (poly ((r region)) (subr (alloc r) (int) (listof int r)))
      (plambda ((r region))
        (lambda (x) (let ((l (the (listof int r) (cons x nil)))) (begin (set-cdr! l l) l)))))

    ;; A walk of an acyclic list: no spin.
    (define len (subr pure ((listof int acyclic)) int)
      (lambda (xs)
        (letrec ((go (subr pure ((listof int acyclic) int) int)
                   (lambda (xs n) (if (null? xs) n (go (cdr xs) (+ n 1))))))
          (go xs 0))))

    (len (the (listof int acyclic) (f 1)))

`fixpt check` accepts it ("both checkers agree"), and `f` is typed `(poly
((r region)) (subr (alloc r) (int) (listof int r)))`. `fixpt run` does not
end. The same `set-cdr!` written at `acyclic` directly is refused ("this
writes frozen data, whose region is `const`"), so only the route through
polymorphism and masking gets past the check.

## Why

Masking keeps only `alloc`, `goto` and `comefrom` on a region that the
result's type mentions and nothing the expression is given does; it drops
`read` and `write` there (`check.rs:2475`, `mask_keeps`; `check-mask.fx`,
`k-result-keeps?`). At `f`'s `lambda`, `r` is only in the result type, so
the body's `{alloc(r), write(r)}` masks to `(alloc r)`. Dropping the write
is sound for interference (no one outside saw the cells), but not for
`acyclic`, whose guarantee is that nothing ever wrote the data. `letfreeze`
already guards against this, noting a freezing region's writes before
masking (`check.rs`, `mask`'s `self.freezing`, and
`regions/const-is-not-acyclic.fx`); instantiating a region binder at a
frozen region has no such guard.

## Proposal

Keep `read` and `write` on a region the result's type mentions, as
Lucassen and Gifford's masking rule does: a region is masked only when it
is free neither in the types of what the expression is given nor in its
result's type. In `mask_keeps`, the result clause keeps every atom:

    Some(r) if in_result.contains(&r) => true,

and `k-result-keeps?` likewise. Then `f` must declare `(write r)`, and its
instantiation at `acyclic` is refused as a write to frozen data. A
procedure that builds and patches its own result (a queue, tail-consing)
would declare `(write r)` too; inside a `letregion`, or for a region not in
the result, the write is still masked as now.

Tests, for both checkers: the repro above, refused at `f` (its body
writes `r`, which its type does not say); and with `f` declaring `(maxeff
(alloc r) (write r))`, refused where it is instantiated at `acyclic`.

The alternative, a separate kind of write effect that masking keeps for
the result's regions and that only freezing reads, we discourage adopting.
