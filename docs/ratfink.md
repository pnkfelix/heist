# ratfink: shakedown in FX-26, for Scheme and FX-26 programs

`ratfink/` is a port of shakedown (`~/Dev/LangPlay/shakedown`, at 80ed588),
a bounded model checker for Scheme written in R7RS Scheme for Larceny, to
FX-26. Like the CFA (`docs/cfa.md`), it is meant to check programs written
in either language: a core that knows neither, and a front end for each.
Like combo (`docs/combo.md`), it is used two ways:

- **as a program**, `bin/ratfink`, run as shakedown is run
  (`ratfink [--unwind N] [--split] … file …`), and as a server,
  `bin/ratfink --serve`;
- **as a library**: a program loads its module files, as `ratfink/ratfink.fx`
  does.

## Plan (2026-10-29)

1. **The Scheme front end and the core, as shakedown has them**, checked
   for exactness against shakedown: the same reports byte for byte, and the
   same SMT-LIB text sent to z3 (`SHAKEDOWN_SMT_LOG` against
   `RATFINK_SMT_LOG`), on shakedown's examples, the programs of its
   `test/check-test.scm`, and its corpus.
2. **`--solver combo`** in place of shakedown's `--solver lockpick`:
   combo's module files linked in (`smt.fx`'s interface).
3. **The FX-26 front end**: FX-26 text read with Fixpt's reader (as
   `cfa/fx26.fx` reads it), types erased, into the forms the core compiles.
4. **`--serve`**, as combo's and the CFA's servers.

## Design: what the port changes

- **One value type**, `rf-value` (core.fx), for the checked program's
  values and its text alike, as shakedown uses Larceny's values for both:
  concrete data, terms, symbol choices, unions, several values, closures,
  primitives, records, ports, tables.
- **Mutable slots are arrays.** A pair is an array of two slots (car,
  cdr), so that the store (`store!`, logs, the trail) treats frames,
  global cells, vectors, records' fields and pairs alike, as shakedown's
  `slot-ref` does.
- **Path aborts and errors are aborts to one prompt tag** (`rf-tag`, at
  region `@rk`); shakedown's `guard`s that restore state and raise again
  are prompts that restore and abort again.
- **Splits use composable continuations** where shakedown uses Larceny's
  re-entrant `call/cc`: a split captures the rest of the proof up to the
  proof's prompt, runs the first arm and resumes it, and then aborts with
  `finished` (a composable continuation returns, where Larceny's call/cc
  jumps). The arms left are each run under a fresh prompt.
- **Evaluation order.** Where shakedown's code makes terms, constants,
  aliases or temporaries in a `let`'s inits, ratfink makes them in the
  order Twobit does (right to left), as combo does, so that term ids,
  constant names and playback text are shakedown's.

## The FX-26 front end (`ratfink/fx26.fx`)

An `.fx` file is read with Fixpt's syntax (`#u`), the module files its
`load-module`s name followed (Fixpt's `fx26:` modules and
`ratfink/proof.fx` are ratfink's own, in Scheme), types erased: FX-26's
forms are special forms of the compiler in FX-26 mode (`eval.fx`,
`install-fx26-forms!`). A product is an alist of its labels, a sum
`(label . value)`, a datatype's value a sum of a product labelled 1, 2, ….

**Specifications.** A procedure whose type `requires` or `ensures` is a
contract (`define/contract`), and has a proof of its own calling it on
symbolic values of its parameters' types, its calls inside that proof
stubs (a value of the result's type assumed to meet the `ensures`): the
proof is modular, as Fixpt's verifier's. A `nat` parameter requires
`(<= 0 x)`, a `nat` result ensures it; `(bool (then …) (else …))` is an
`ensures` of `implies`. A local `letrec`'s specification is a stub for
its callers, and a verification of its body where the `letrec` is. A
*harness* (a `unit` result, a body that `assert`s; what `fixpt test`
runs) has a proof on symbolic values too, as has a `proof-…` procedure
of no arguments.

**Values of a type** (`type-value`; a stub's result, `type-shape`):

| type | symbolic value |
| --- | --- |
| `int`, `nat`, `(nat k)` | an integer; `nat`'s assumed `≥ 0`; `k` itself |
| `i32`, `u32`, `i64`, `u64` | an integer in the type's range |
| `bool` | a boolean |
| `unit`, `(proves …)` | `#u` |
| `char`, `string`, `symbol`, `f64`, `f32` | one of a *domain*: the program's literals of the type (up to 6; a quote's symbols), and `#\a`; `""`, `"a"`; `ratfink-other`; `0.0`, `1.0`, `-0.5` (the solver has no sort for them) |
| `(listof T r)`, `(arrayof T r)` | up to 4 elements (a stub's result, 8) |
| `(nlist T k)`, `(pairof A B r)`, `(ref T r)` | of their parts |
| `(productof …)`, `(sumof …)` | each field's; one of the labels' |
| a `define-type`'s name, a family applied, a datatype, `mu`, `dletrec` | unfolded, 3 deep at most (a recursive value's depth) |
| a `poly`'s type variable | `'opaque` |

A procedure with a parameter of another type (a procedure's, `datum`, a
module's) has no proof. A proof over a domain's type is exhaustive only
over the domain.

**Counterexamples** show a proof's inputs as FX-26 expressions of their
types (`proof-inputs`, rendered by `render-input`): `p = (product (x 2)
(y 3))`, `t = (leaf)`, `xs = (list 0 0)`, `b = (new -1)`; then what else
the model says, of constants not made for the inputs (a stub's result).

**Not yet:** playback (running a counterexample under Fixpt); telling an
`ensures` that is not inductive (Fixpt's verdict) from a false one; type
checking (a program Fixpt refuses is checked as written).
`ratfink/tests/fx26/types.fx` has true and false claims over these types.
