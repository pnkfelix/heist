# Request to Fixpt: what each maker given a module pays to load

Status: both costs done in Fixpt (pulled 2026-10-29 at e4af8997): cost 1
in 8202075e, the first form read alone; cost 2 in 80f8b222, substitution
leaving alone a type it cannot change (lib-80 3.03 to 1.91 ms a
dependent, by Fixpt's measure). Combo now starts in 0.13 s, ratfink in
0.25 s. Drafted 2026-10-29 by Heist, against Fixpt 61a2e792. Measured with
`bench/module-dependents.sh` and on Heist's combo. The first fix was
prototyped in a scratch build only, and Fixpt's own tests were not run
on it; Heist's Fixpt is unchanged.

## Summary

A maker (a file of `module-parameters`) given another maker, `(a
(load-moduleof "a.fx" z))`, pays two costs each time it is loaded. Both
scale with `a`, and both are paid again by every dependent:

1. **`a.fx`'s source is read whole.** `parse::takes_modules_at` reads the
   entire file to look at its first form. This is item 1 of
   `fixpt-load-time.md`, still open. On combo it is now **42% of
   start-up**: reading only the first form takes combo from 282 ms to
   163 ms.
2. **`a`'s module type is checked again, in the checker written in
   FX-26.** `check-more` spends time on each form whose type mentions
   it: about 26 µs per distinct `poly` signature, and 9 µs per
   distinct monomorphic one, for each dependent. Identical signatures
   are shared and cost almost nothing. Heist avoids this by `hide`.

## The benchmark

`bench/module-dependents.sh FIXPT OUT` builds each case as a maker
`a.fx`, given to N makers `bI.fx`:

    ;; bI.fx
    (module-parameters ((z (load-moduleof "z.fx")) (a (load-moduleof "a.fx" z))))
    (define vI int (+ one I))
    ;; main.fx
    (define z (load-module "z.fx"))
    (define a ((load-module "a.fx") z))
    (define bI ((load-module "bI.fx") z a))   ; for each I

Everything is compiled with `fixpt compile-file`, and each figure is the
median of 20 runs of `fixpt run main.fx`. The procedures are `poly` over
a place, a type, an effect and a region, as kit's are. "Distinct" means
each one's result is a different `productof`.

| case | `a.fx` | ms per dependent, 61a2e792 | with fix 1 |
| --- | --- | ---: | ---: |
| none-0 | defines nothing | 0.93 | 0.88 |
| src-80 | defines 80 distinct procedures itself | **6.62** | 3.09 |
| lib-20 | loads a file of 20 distinct ones | 1.42 | 1.44 |
| lib-80 | loads a file of 80 distinct ones | **3.13** | 3.10 |
| mono-80 | as lib-80, monomorphic | 1.69 | 1.73 |
| same-80 | as lib-80, all 80 of one type | 0.96 | 0.95 |
| hidden-80 | as lib-80, the load in a `hide` | 0.96 | 0.93 |

In src-80, cost 1 is the difference between the two builds, 3.5 ms per
dependent. Cost 2 is what remains, the same as lib-80. Heist's kit
`lists.fx`, 22 procedures, costs 0.98 ms per dependent above none-0,
about 45 µs per procedure. That is more than the synthetic signatures
cost, since kit's are larger.

## Cost 1: `takes_modules_at` reads the whole file

`takes_modules_at` (`parse.rs`) is called on every load, `.fasl` or not.
Its comment says "the rest is not read", but it calls
`Reader::read_all`. The prototype reads one datum:

    -    match fixpt_read::Reader::new(&text, …, &mut interner).read_all() {
    -        Ok(forms) => takes_modules(&forms, &interner),
    -        Err(_) => false,
    -    }
    +    let first = fixpt_read::Reader::new(&text, …, &mut interner).read();
    +    match first {
    +        Ok(Some(first)) => takes_modules(std::slice::from_ref(&first), &interner),
    +        _ => false,
    +    }

With it, combo (15 module files, 13 of them makers, most given
`term.fx`, `rat.fx` and four or five more) starts in 163 ms rather than
282 ms. That is an A/B of two builds of the same tree with the same
flags, differing only in this change. On the profile without it,
`takes_modules_at` was 63% of the time the 20 dependents of src-80 added.

## Cost 2: the module type, checked for each dependent

Timing each `call_global` into the front end (lib-80's shape, with
Heist's kit as `lib.fx`, N = 20) puts most of the added time in
`check-more`. It takes 17.7 ms over 67 calls with kit, and 2.0 ms
without. Traced through `syn::check_only`, two forms per dependent
account for it:

| form checked by `check-more` | without kit | with kit |
| --- | ---: | ---: |
| `(define %shared:input:bI.fx (%loaded …))`, the dependent's load | 55 µs | 272 µs |
| `(define bI ((load-module "bI.fx") z a))`, its use | 25 µs | ~450 µs |

Both forms' types contain `a`'s, since `bI`'s parameter is `(load-moduleof
"a.fx" z)`. Not applying `bI` (`(define bI (load-module "bI.fx"))`) saves
nothing: the maker's own type still holds `a`'s. Reading the larger text
(`read-text-at`) added 3.5 ms more. Heist didn't attribute the rest, nor
look inside `check-more`, whose words a profile knows only by position.

Identical signatures cost nothing (same-80), so the checker already
shares some work by type. It doesn't share it across the dependents of
one module, whose parameter types are the same `a`.

## The prompt

Two costs of loading a maker given another maker, `(a (load-moduleof
"a.fx" …))`, paid again by every dependent; measured on Fixpt 61a2e792
by Heist's `docs/requests/bench/module-dependents.sh`:

1. `parse::takes_modules_at` still reads the whole file to see its first
   form (Heist's `fixpt-load-time.md`, item 1). Reading one datum,
   `Reader::read` and `takes_modules(std::slice::from_ref(&first), …)`,
   takes Heist's combo from 282 ms to 163 ms. On a maker of 80
   definitions it saves 3.5 ms per dependent.
2. The checker written in FX-26 (`check-more`) spends time on `a`'s
   module type for each dependent: on its `(%loaded …)` define, and on
   each use of it. That's about 26 µs per distinct `poly` signature in
   `a`'s type, per dependent. A library of 22 procedures held by a
   maker that 10 others are given costs 10 ms of start-up. Could the
   checker share that work across the dependents of one module? For
   instance, the type `(load-moduleof "a.fx" z)` stands for could be
   made and checked once per file key and arguments, as identical
   signatures already are. Heist hides such libraries for now (`(hide
   (define kl (load-module …)))`).
