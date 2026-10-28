# combo: lockpick in FX-26

`combo/` is a port of lockpick (`~/Dev/LangPlay/lockpick`, at 2bae0a4), a
SAT and SMT solver written in R7RS Scheme for Larceny, to FX-26. It is
used in two ways:

- **As a program**, `bin/combo`, run as lockpick is run:
  - SMT-LIB2 from a file, or from standard input with `-in`;
  - DIMACS with `--dimacs` (`--proof`, `--stats`, `--no-elim`), and iCNF with `--icnf`;
  - a server, `--serve`, for a client such as the editor.
- **As a library**: a program loads combo's module files, as `combo/combo.fx`
  does. `combo/tests/linked.fx` uses the solver on terms directly.

## Layout

Each file is a module file, made once, in order, from those before it. The
files are listed in `combo/program`, and each corresponds to one of
lockpick's libraries. All of combo's state is at region `@cb`, and `cb-eff`
(sat.fx) is what its procedures do.

| File | lockpick's | What it is |
|---|---|---|
| sat.fx | `(lockpick sat)`, sat-core.scm | CDCL: watches, first-UIP learning with minimization, VSIDS, Glucose restarts, LBD reduction, assumptions, the theory interface, DRAT |
| rat.fx | Scheme's exact numbers | rationals over FX-26's `int` (a bignum where it must be) |
| dimacs.fx | `(lockpick dimacs)` | CNF and iCNF read from bytes; answers as text |
| elim.fx | `(lockpick elim)` | bounded variable elimination, subsumption |
| term.fx | `(lockpick term)` | hash-consed terms and Boolean constructors |
| bv.fx, arith.fx | `(lockpick bv)`, `(lockpick arith)` | bitvector and linear arithmetic constructors |
| eval.fx | `(lockpick eval)` | a term's value under an assignment |
| simplex.fx | `(lockpick simplex)` | the simplex of Dutertre and de Moura, branch and bound, cube test, Gomory cuts, integer equalities |
| blast.fx | `(lockpick blast)` | Tseitin, bit-blasting, totalizers, atoms of the simplex |
| smt.fx | `(lockpick smt)` | an SMT context: assertions, push/pop, checks, values |
| sexp.fx | `(lockpick sexp)` | SMT-LIB2 S-expressions, read from text fed to it |
| smtlib.fx | `(lockpick smtlib)` | the command language, answered as z3 does |
| serve.fx | (new) | the server's sessions and protocol |
| main.fx | `(lockpick main)` | the program's options |

## How it differs from lockpick

- **Representation:**
  - A term is an int, its id; the term store keeps its operator, parameters,
    name, arguments and sort.
  - A sort is an int: Bool -1, Int -2, Real -3, and a bitvector its width.
  - A clause is an int array, referred to by its number in the solver's
    clause table, so that watches, reasons and clause lists are int arrays
    too. lockpick's other clause store, the arena (`LOCKPICK_ARENA`), is not
    ported.
- **Errors are values.** FX-26's `attempt` cannot run code that writes, and
  parsing writes the term store. So a command's first error is kept in the
  session (`fail!`), each step checks it (`bad?`), and no term is built once
  one has failed. The blaster never fails, because the parser refuses what
  it cannot do, as lockpick's does.
- **The reader is fed text** (`sexp-feed!`) and does no I/O. The command
  line feeds it lines, and the server feeds it requests.
- **Proofs** are kept as lines and written out at the end.
- **Not ported:** theory propagation (`LOCKPICK_PROPAGATE`), which is off in
  lockpick by default.
- **Evaluation order.** Where lockpick's code makes two terms or SAT
  variables in one `let`, combo makes them in the order Twobit does, so that
  ids and variable numbers, and with them the search, are lockpick's own.
  Twobit evaluates a `let`'s inits, and `vector`'s arguments, right to left;
  calls, `cons`, `list` and `map` left to right (measured on lockpick's own
  Larceny, compiled as lockpick compiles). Seven places depend on it:
  - `full-adder`;
  - the Tseitin cases for `and`, `or`, Boolean `=` and `ite`;
  - `concat`;
  - `div`/`mod` definitions;
  - pseudo-Boolean sums.

  Before this, `ring_2exp10_8vars_1ite_unsat` timed out, against 0.09 s for
  lockpick; now it is 121 conflicts in both.

## Verified

- **SAT:** the same searches as lockpick (conflicts, decisions,
  propagations), with or without elimination, on uuf-50/100 and SATLIB's
  parity, bmc, blocksworld and logistics. Models satisfy every clause, and
  drat-trim verifies the proofs.
- **SMT:** on lockpick's fuzzer (`test/fuzz/fuzz_smt.py`), 800 scripts
  (QF_UF, QF_BV, QF_LIA, QF_LRA) give byte for byte lockpick's output,
  models included. Run against z3 by the same fuzzer, every answer agrees
  and z3 accepts every model.
- **Benchmarks:** on lockpick's SMT-LIB benchmark lists, no answer
  disagrees.
- **Tests:** `combo/tests` (nextest `combo::`) holds lockpick's fast
  regression scripts, fuzz scripts, the commands and their errors, CNFs (with
  `--stats`), iCNF, a server session and the linked program. The expected
  outputs of the `.smt2`, `.cnf` and `.icnf` tests are lockpick's, but for
  combo's name.

## Measured (2026-10-28, shared 128-core machine)

**Build and start-up**
- `bin/heist-compile combo` takes 1.8 s from clean and makes 6.4 MB of
  `.fasl`s. With them combo starts in 0.48 s (1.8 s from source); lockpick
  starts in 0.05 s from its heap image.

**SAT instances**, start-up included:

| Instance | lockpick | combo |
|---|---|---|
| par16-2 | 0.23 s | 0.71 s |
| bmc-ibm-12 | 3.1 s | 4.6 s |
| bmc-galileo-8 | 1.3 s | 1.8 s |

The searches are the same.

**SMT-LIB** (lockpick's lists, 60 s limit):

| List | lockpick solved | combo solved | combo's time where both solve |
|---|---|---|---|
| QF_LRA | 56 of 56 | 56 | the same (1.0×) |
| QF_LIA | 96 of 106 | 94 | 1.2× |
| QF_BV | 109 of 125 | 109 | 1.5× |

On QF_LIA, the two that only lockpick solves take it 55 s and 57 s, which at 1.2× is
past the limit.

**Where the time goes.** In the SAT core, as in lockpick: `propagate!` is
half. Fixpt calls small procedures rather than inlining them, so the hot
loops take the solver's arrays into locals, and `imply!` and `lit-neg` are
written into `propagate!`.

## FX-26, as the port found it

- **Names that are special forms** cannot name a procedure: `sum` (it
  builds a `sumof` value) and `with` (it opens a module). A local loop
  named either is parsed as the form.
- **Mutual recursion** among a module's items needs `define`, not
  `define*`.
- **Inferred types.** A list or array built in one branch needs `(the T …)`
  more often than one would like: `(if c (list x) nil)`, an array whose
  length is a value (`narrayof`), a product whose fields hold `new` refs.
- **No duplicate names.** A module that includes two others may not define
  a name either of them does. Neither may the program that includes them
  all, so combo's names are distinct across its files (elim.fx's `el-`,
  blast.fx's `tt` and `ff`).
- **A checker disagreement** in a refused program's message:
  `docs/requests/fixpt-checkers-print-list-arguments.md`.

## Next

- Speed:
  - the blaster's string keys (`ite` gates, divisions) as ints;
  - the term store's operator strings as small ints;
  - the 0.48 s start-up.
- lockpick's unit tests (`test/*-test.scm`) as FX-26 tests of the library.
- An editor client, if one is wanted: `--serve` is ready for one.
