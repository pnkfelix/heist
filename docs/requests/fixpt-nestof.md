# Request to Fixpt: `(nestof L)`, nested proper lists

Status: open. Drafted 2026-11-10 by Heist, against Fixpt 07b0d743. It grew
out of the macros request (`fixpt-macros-from-heist.md`, item 5), but it
stands on its own: we think it is a useful middle ground between
`listof` and `datum`, and a good place to exercise FX-26's unions,
narrowing and bounded variables. The repros are in `bench/nestof/`; run
each with `fixpt run FILE`. Each file's name says what it probes, and its
output on 07b0d743 is quoted below.

## Summary

A **nest** is a proper list whose elements are leaves or nests. Nothing
in it is dotted. `(nestof L)` says what its leaves are, as `(listof T)`
says what a list's elements are:

```
(define-type (nestof (l type)) (mu n (listof (oneof l n) acyclic)))
(define-type atom (oneof int f64 char bool string symbol keyword))
(define-type form (nestof atom))
```

A nest is always nil or a pair, never a leaf. That's the point: `cdr`
of a nonempty nest is a nest, so code takes nests apart as it takes
lists apart, with no narrowing. A `datum` gives no such guarantee,
because any pair in it may have a non-list tail.

This exact definition can be written in FX-26 today, and much of it works
(below). We ask Fixpt for four things:
1. `nestof` as a standard type constructor, beside `listof`;
2. procedural macros' input typed `(nestof atom)`;
3. quoted literals that are nests typed as nests;
4. code polymorphic over the leaf type, which needs bounded type
   variables.

## Why: the transformer that motivated it

A procedural macro's input is a `datum`, so a transformer has to narrow
it before it can take it apart. The macros request's
`transformer-datums.fx` needed a datum-to-list map and a `typecase` per
symbol. The same body, with `form` typed as a nest, checks with no
helpers (`nest.fx`, prints `ok`):

```
(define* rec (subr spin (form) datum)
  (lambda (form)
    (let ((fields (cdr (cdr form))))                    ; a list, statically
      `(begin (fields ,@fields) (count ,(list-length fields))
              ,@(fmap (lambda ((f (oneof atom form))) (if (pair? f) `(with ,(car f)) f)) fields)))))
```

With `form : datum` (`datum-body.fx`), the first `,@` is refused: `` a
(listof datum acyclic) is expected here, and this is a datum ``.

A use of a macro is always a list, `(name arg …)`, so the input is a nest
whenever no dot is written. FX-26 source needs no dots: variadic
procedures are `vlambda`. Heist's 78 lines that write a dot are all
Scheme: s7st's and ratfink's preludes, held in strings, and
docstrings and comments that describe Scheme data.

## What works today, with the definition above

| repro | shows | output |
| --- | --- | --- |
| `nest.fx` | taking a nest apart with no narrowing; a flat list is a nest, and a nest is a datum | `ok` |
| `covariant.fx` | `(nestof symbol)` ≤ `(nestof atom)` | `ok` |
| `typecase-elem.fx` | `typecase` narrows an element, `(oneof atom form)`, to its atom kind | `x` |
| `null-narrow.fx` | `null?` narrows a nest; `car` of a nonempty one is an element | `head` |
| `region-param.fx` | a nest at a place, `(listof (oneof l n) (acyclic p))`, polymorphic over `p` | `2` |
| `datum-to-form.fx` | a checked conversion from `datum`: a dotted datum is refused, a dot-free one becomes a form (by copying) | `dotted: refused, a form` |

The subtyping chain is `(listof symbol acyclic)` ≤ `(nestof atom)` ≤
`datum`. So nests go wherever data goes, and a transformer may still
return a `datum`.

## What does not work, and what we ask

### 1. Leaves must be told apart from nests, and FX-26 enforces it

`(nestof (listof int acyclic))` is refused (`overlap-pairs.fx`), and so is
`(nestof (oneof int nil))` (`overlap-nil.fx`): `` a `oneof`'s members must
be told apart at run time ``. This is the right rule, since otherwise
`pair?` and `null?` could not tell a leaf from a nest. Two things about
it:
- **The refusal is in the wrong place.** It points at the family's
  definition (1:46). The mistake is in the line that instantiates it
  with an overlapping leaf type.
- **`anyof` allows overlapping leaves, but nothing narrows them.** With
  `anyof` in place of `oneof`, `(listof int acyclic)` leaves are accepted
  (`anyof-overlap.fx`, `accepted`). A built-in `nestof` should take the
  `oneof` side, and say why in its refusal: a nest's leaves must not be
  nil or pairs.

### 2. Code polymorphic over the leaf type: bounded type variables

`(poly ((l type)) (subr spin ((nestof l)) int))` is refused, even with
the type argument given (`build-poly.fx`): `` a l cannot be in a
`oneof`: its shape at run time is not known ``. So a library cannot
offer one `nest-length` or `nest-map` for every leaf type. Each leaf type
needs its own copy, which defeats the point of a type constructor.

What would fix it is a type variable bounded by shape. Fixpt f6d31209
added bounded effect variables, `(e effect (within E))`. The type-side
equivalent, say `(l type (within atom))`, would tell `oneof` that `l`'s
shapes are among `atom`'s, so none is nil or a pair. Then `(oneof l
(nestof l))` is told apart at run time for every `l` within the bound. A
built-in `nestof` could take its parameter with exactly that bound.

### 3. Quoted literals are always `datum`

`'(a (b c) 1)` cannot be declared a `form` (`quote-literal.fx`). Nor can
`'(a b)` be declared a `(listof symbol acyclic)` (`quote-flat.fx`): `` a
… is expected here, and this is a datum ``. The quote rewrite wraps every
list it builds in `(the datum …)`. We ask that a literal with no dot be
typed as the nest (or list) it is, with `datum` reached by subtyping.
Today a test or example must build nests with `list`, and as item 4
shows, even that isn't always enough.

### 4. Building a nest needs a known expected type

`(list 1 (list 2 3))` checks as a `form` argument of a monomorphic
procedure (`nest.fx`). Given to a parameter of a `poly` over the place,
`list` takes its element type from its first element and refuses the
second: `this is a (listof int r), where a int is expected`. This is how
`list` is typed in general, but nests show it most, because they are
heterogeneous by design.

### 5. Intersections of data types

`(allof datum form)` is refused (`allof-datum.fx`): `` a member of an
`allof` is a `subr` type, or a product of them ``. Here that costs
nothing, because `form` ≤ `datum`, so their meet is just `form`. We
list it because nests raise the questions where intersections of data
types would matter:
- **What does `pair?` narrow a `datum` to?** The answer is roughly
  `datum` ∩ pair. Then `cdr` of it is still a `datum`, not a list.
- **What narrows a `datum` to a nest without copying it?** A test, say
  `datum-nest?`, whose result is `(bool (then (shape 0 (nestof atom))))`.
  That would make `datum-to-form.fx`'s copy unnecessary.
  `datum-proper-list?` exists, but it does not narrow, and it does not
  look inside the elements.
- **Are a nest's two narrowings one fact?** `(oneof L (nestof L))`
  narrowed by `pair?` is a nonempty nest, and narrowed by `null?` is nil.
  An element type that is an intersection is what would tell the checker
  this.

## What we would do with it

- **Macros:** transformers over `(nestof atom)` (item 5 of the macros
  request), with a use containing a dot refused when it's expanded.
- **casing:** its models are S-expressions, read and then walked as
  `datum`s. `casing/model.fx` names `datum` 94 times and has `head`,
  `items` and `nth` for taking forms apart. A model never needs a dot.
- **combo:** SMT-LIB2 has no dotted pairs, so `combo/sexp.fx`'s reader
  could give nests, and `combo/smtlib.fx` could take commands apart
  without narrowing.
