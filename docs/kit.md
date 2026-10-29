# kit: Heist's library of FX-26 procedures

`kit/` holds the R7RS-style procedures that Heist's programs (s7st, combo,
ratfink, the editor; the CFA too) each wrote for themselves, because
FX-26 has no standard library beyond Fixpt's primitives (`fixpt/TODO.md`
§22). Each file is a module of no state, loaded by path:

    (define lists (load-module "../kit/lists.fx"))
    (import lists map filter list-sort)

What needs the runtime (identity tables, a generic `equal?`, `write` of any
value, control, I/O) is Fixpt's to give, and is not here.

Started 2026-10-29, once Fixpt 61a2e792 fixed the masking hole that kit's
signatures depend on (`docs/requests/fixpt-mask-hides-acyclic-writes.md`).
combo uses it (`rat.fx`, `term.fx` and the modules given `term`), and
ratfink its numbers, lists and strings.

## Conventions

- **Lists given are frozen and acyclic**: `(listof a (acyclic p))`, at any
  place `p` (the heap's `acyclic`, or an arena's). Walking one ends, so no
  procedure says `spin`: each is usable in `pure` code and in a
  specification's logic functions. Reading one is `(read (acyclic p))`,
  nothing at the heap. Every list in the four programs is `acyclic` but for
  a handful. A list whose spine is written needs a `spin` variant (as
  `cyc-map` would be), written when a program needs one.
- **Lists made are at a region `r` the caller chooses**. No procedure here
  writes `r`, so the checker lets a caller choose `acyclic` (`(the (listof
  int acyclic) (map f l))`), or a writable region.
- **Not found is `#f`**, as in R7RS: an index or a digit is a `(union false
  nat)`, taken apart by `bool?`. An element of a type variable cannot be in
  a union (no shape is known), so `find` gives `none` or `(some x)`.
  `member` gives the tail from the element found, so nil when none is.
- **Equality and order are given** (`(member x l string=?)`, `(list-sort <
  l)`), as R7RS's `member` and SRFI 132's `list-sort` take them.
- **Loops the checkers cannot see end are given fuel** they never run out
  of, so that they stay `pure`: `list-sort`'s depth by the length;
  `gcd`, `expt`, `integer-length` and `number->string` by `bit-bound`
  (four times the decimal length, more than the bits).
- **R7RS's forms, not a host's.** A character's or string's written form
  is R7RS's; s7st (s7's) and ratfink (Larceny's) keep their own.

## What is in it

"Seen in" names the programs with a local version, from a survey of their
definitions (local loops not counted); a procedure seen in fewer than two
is kit's for completeness beside one that was.

### `kit/lists.fx`

| procedure | seen in |
| --- | --- |
| `map`, `map2`, `for-each`, `for-each2`, `filter`, `remove` | ratfink (`core.fx`), combo (`filter-ints`, `map-neg`), and loops everywhere |
| `fold`, `fold-right`, `reduce` | ratfink, combo (`ints-max`) |
| `any`, `every`, `find` | the editor (`has-each?`), ratfink (`all-equal?`), the CFA |
| `list-index` | s7st (`s7-index-of`), the CFA (`cf-index`) |
| `member`, `member?`, `delete` | s7st, combo, ratfink, the editor (`member-string?` and kin, five of them), the CFA; combo's `remv-once` |
| `list-ref` | s7st (`s7-field`), combo (`field`), the editor (`s7-nth-field`, `s7-nth-string`) |
| `list-tail`, `take` | s7st (`s7-take`, `s7-drop`), ratfink (`vals-head`, `vals-tail`), the CFA |
| `concatenate` | ratfink (three `apply-append-…`), combo |
| `list=?` | combo (`ints=?`), the CFA (`same-path?`) |
| `list-sort` (stable merge sort) | s7st (`s7-sort-strings`), the editor (`sorted`), combo (`sort-ints`, `list-sort-terms`), the CFA |

### `kit/numbers.fx`

| procedure | seen in |
| --- | --- |
| `abs` | ratfink (`iabs`) |
| `gcd`, `lcm` | s7st, combo, ratfink |
| `floor-quotient`, `floor-remainder`, `truncate-…` | s7st, combo (`floor-div`), ratfink |
| `expt` | s7st (`s7-expt-int`), combo (`expt10`, `expt2`), ratfink (`expt10`) |
| `integer-length` | s7st, ratfink (`bit-length`) |
| `exact-integer-sqrt` | s7st, ratfink (`isqrt`) |
| `number->string` (a radix) | s7st, combo (`digits`), ratfink |
| `radix-digit`, `string->integer` | s7st, combo (`radix`, `decimal`, `hex-value`), ratfink, the editor (`digits-value`, `s7-integer`) |
| `ratio->f64` | s7st, ratfink |

### `kit/chars.fx`

| procedure | seen in |
| --- | --- |
| `digit-value` (Unicode's decimal digits) | s7st, ratfink, combo (`digit?`) |
| `char-delimiter?` | s7st, ratfink, the editor |
| `char-name`, `name->char`, `written-char` | s7st, ratfink |

### `kit/strings.fx`

| procedure | seen in |
| --- | --- |
| `string-prefix?`, `string-suffix?` | ratfink (`string-starts?`, `-ends?`), the editor (`starts-with?`) |
| `string-index`, `string-index-from` | ratfink (two) |
| `string-concatenate`, `string-join` | s7st, combo, ratfink, the editor (`joined`), the CFA |
| `string-split`, `string-tokenize` | the editor (`words`, `s7-fields`), ratfink (`split-words`), the CFA |
| `string-pad-right`, `string-pad` | ratfink (`pad`), the editor (`padded`) |
| `written-string` | s7st, ratfink |

## Where kit differs from the versions it replaces

- `integer-length` is SRFI 151's: of a negative `n`, that of `-n-1`.
  s7st's and ratfink's `bit-length` take `|n|`.
- `ratio->f64` is correctly rounded (ties to even) for a normal result.
  s7st's keeps 62 bits of the quotient and scales: it may round twice.
- `string-pad-right` and `string-pad` truncate, as SRFI 13's do;
  ratfink's `pad` only pads.
- The written forms are R7RS's: `#\x1f`, `"\x1;"`. s7st's and ratfink's
  follow their hosts.

## Three things a caller meets

- **In a module file, kit is loaded in a `hide`**, by each file that uses
  it:

      (hide (define kit-lists (load-module "../kit/lists.fx"))
            (import kit-lists map filter))

  Otherwise kit's module and the names imported are items of the file's
  module, and in its type; every maker given that module (`(load-moduleof
  "term.fx" …)`) reads the whole of that type as it is loaded, about 1 ms
  for kit's lists. In combo, `term.fx` holding kit visibly cost 13 ms of
  start-up; hidden, nothing measurable. Each file loading kit itself is
  cheap: every load of a path is one module, made once
  (`docs/requests/fixpt-module-type-per-dependent.md`).

- **A list made is `acyclic` where nothing says otherwise.** Since Fixpt
  e4af8997 (`docs/requests/fixpt-region-default-acyclic.md`), a region
  a call leaves unsolved, that the procedure only allocates and reads as a
  list's, is `acyclic`: a kit result bound by `let`, a list literal or a
  kit result given straight to kit, needs no `(the (listof T acyclic)
  …)`. Before it, ratfink needed 112 such annotations; it has none now. A
  caller that writes a list kit made says the list's region.
- **Imported procedures are the program's globals**, so a caller's effect
  has `(read (globals map …))`, and a caller declared `pure` is refused.
  Within a module the reads are none. Exports read as constants are
  `fixpt/TODO.md` §22's wish.

## Tests

`kit/tests/NAME-test.fx`, one a module, each checked (refused at nothing,
both checkers agreeing) and run by `kit/tests/run.sh`, and in `cargo
nextest run` as `kit::NAME`. Each asserts each procedure's answers;
`lists-test.fx` also checks a caller's effect has no `spin`, and uses a
list built in an arena.

## Next

- Programs adopt kit, one at a time, each kept if its tests pass and its
  start-up does not grow: s7st and the CFA have the most to drop.
- A `spin` variant of a list procedure, if a program needs one.
