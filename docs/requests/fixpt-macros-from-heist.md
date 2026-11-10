# Request to Fixpt: macros, as Heist found them

Status: open. Drafted 2026-11-09 by Heist, against Fixpt 07b0d743. While
surveying where Heist's FX-26 code could use macros, we wrote macros for
it and probed what the macro system can and cannot do. These are the
problems we hit, most important first. Each has a repro in
`bench/macros/` (run with `fixpt run FILE`, or `fixpt run main.fx` in
the directory), whose header comment gives the output on 07b0d743.
`bench/macros/works.fx` shows what already works.

## 1. A module file cannot use macros at all (blocking)

Heist has 7 subsystems:
- **s7st and cfa** are each one program whose files `fixpt run` reads in
  order. Their files share a top level, so macros already work in them,
  including across files and through `compile-file --program`.
- **The other 5** (editor, combo, ratfink, casing, kit) are module files,
  loaded with `load-module`, most with `module-parameters`. That is 28k
  of Heist's 38k lines of FX-26, not counting tests.

A module file cannot use a macro by any of the three routes we tried:

| route | repro | refusal |
| --- | --- | --- |
| a macro the file defines itself | `module-own/` | `` `twice` is a macro of this file: one is used where its file is imported (`import-with-syntax`), not in its file, for now `` |
| a macro imported from another file | `module-import/` | `` unbound variable `import-with-syntax` `` |
| a macro the loading program defines | `module-toplevel/` | `` unbound variable `twice` `` |

The third is expected, since a module file is read against the standard
environment. We list it so that you know we tried it.

What we ask, in order of value to us:
- **(a) A file's own macros, used in the file after they are defined.**
  This alone would make every candidate below usable everywhere.
- **(b) `import-with-syntax` in a module file.** Then shared macros could
  live in kit, which has no module parameters, so it meets
  `import-with-syntax`'s condition already.
- **(c) Later, `import-with-syntax` of a file with module parameters.**
  Most of Heist's files have them.

## 2. `syntax-rules` lacks R7RS's ellipsis tails

- **In a pattern:** `(_ s (k e) ... (else d))` is refused with ``read
  error: `...` follows the part it repeats, last in a list``
  (`ellipsis-pattern-tail.fx`). R7RS 4.3.2 allows `P … Pk`.
- **In a template:** `(cond ((string=? v k) e) ... (else d))` is refused.
  The message, `` `(((string=? v k) e) ... (else d))` is of none of the
  shapes this part may have ``, does not say that the ellipsis's
  position is the problem (`ellipsis-template-tail.fx`).

Together these rule out the commonest shape of all: some clauses, then a
default. We had to move the default first, `(string-case s default (k
e) …)`, and recurse over the clauses.

## 3. Inference: literals, and simple recursion

- **Clauses that differ by a literal are refused as overlapping.**
  `(else d)` and `(k e)` are refused (`literal-overlap.fx`), although
  `else` is a declared literal; R7RS tries clauses in order. We would
  like a literal to tell clauses apart, or clauses tried in order.
- **A two-clause recursion is inferred as a non-contractive `mu`.** The
  base case `(_ v d)` with the step `(_ v d (k e) c ...)` gets ``a
  `mu`'s variable is used where no pair is around it``
  (`infer-recursive.fx`). The signature `((many expr) expr (expr expr)
  ...)`, written by hand, works. The refusal could suggest that
  signature, or at least say which part needs one.

## 4. Field labels in templates, and tagcase clauses passed through

- **Labels must be keywords in a template, and only one refusal says
  so.** `(extract p x)` in a template is refused with a helpful hint (``a
  tag or label in a template is a keyword: `#:x`, not `x` ``).
  `(product (x a) (y b))` gets only `` is of none of the shapes this
  part may have `` (`product-labels.fx`). With `(#:x a)` both work.
- **A macro cannot pass its use's `tagcase` clauses through.**
  `(_ e (tag v body) ...)` → `(tagcase e (tag v body) ...)` is refused:
  `` could be of more than one of this part's shapes ``
  (`tagcase-clauses.fx`). We would like a way to say "a tagcase clause"
  in a signature, for match-like wrappers.

## 5. Procedural transformers: datums are hard to take apart

A transformer's input is a `datum`, and taking one apart takes code of
your own every time (`transformer-datums.fx`, a record with `with-FIELD`
setters, which works once these are written out):
- **`,@x` needs `x` to be a `(listof datum acyclic)`.** A datum that is a
  proper list is refused.
- **There is no standard `map`** (`,apropos map` finds none), so a
  transformer writes its own, over a datum it must narrow.
- **`(symbol->string (car f))` is refused.** `car` of a datum is a datum,
  so each use needs a `typecase` to narrow it.
- **None of these refusals has a position inside the transformer.** Each
  is reported at the transformer's start (3:5). The third, for example,
  says only ``argument 1 is a datum, where a symbol is expected``.

What would help:
- a narrowing test, datum to `(listof datum acyclic)`. `datum-proper-list?`
  exists but does not narrow.
- `,@` accepting a `datum`. Its use already says the operand is a list.
  The refusal comes from the rewrite, not from what `,@` means:
  `parser.fx`'s `quoted` makes `,@e` into `((with #%fx append) e …)`,
  and `append` takes a `(listof datum R)`. `car` and `cdr` take a
  `datum` and trap at run time if it is not a pair, "so that Scheme code
  that takes apart data it has not tested ports as written" (`fx26.md`,
  Datums). `,@` could do the same:
  - in the middle of a list, walk the datum with checked `car` and
    `cdr`, and trap if it is not a proper list;
  - last in a list, `` `(a ,@e) ``, check nothing: R7RS's `append`
    takes any value as its last argument, so this is `(cons a e)`, a
    `datum` already. All three of `transformer-datums.fx`'s `,@`s are
    of this kind.
- positions within the transformer in its refusals.

## 6. Smaller things

- **No `when` or `unless`.** Heist writes `(if c (begin …) #u)` about
  170 times. A standard `when` would be a three-line macro.
- **`sum` can be defined but not called.** `(define sum …)` is accepted,
  but a call `(sum xs)` is read as the `sum` form, and refused with only
  `` `(sum tag expression)` `` (`define-sum.fx`). This isn't about macros,
  but we hit it while writing them. Either refuse the definition, or say
  in the refusal that `sum` is a form.
- **Every macro refusal is called a `read error`.** That's true of when
  it happens, but it sends one looking for a reader problem.

## What already works

`bench/macros/works.fx` shows these working in a program; `` => 6 B
first=5 -=2 ``:
- a typed loop macro, `(loop go EFF ((x T init) …) RESULT body)`, with
  effects such as `(maxeff spin (read @a))` and region-polymorphic types
  passed through;
- `when`;
- `string-case`, with its signature written;
- a family of registrations, one macro whose template uses another.

A procedural `define-record` that defines a type and its setters works
too (`transformer-datums.fx`). So do `compile-file --program` across
files, and keyword literals in patterns. Item 1 is what keeps these out
of most of Heist.
