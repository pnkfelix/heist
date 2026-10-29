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
