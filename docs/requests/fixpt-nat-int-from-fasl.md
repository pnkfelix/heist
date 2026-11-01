# Request to Fixpt: a `nat` refused as an `int` of a type read from a `.fasl`

Status: open. Drafted 2026-11-01 by Heist, for the user to take to the
Fixpt team. Against Fixpt 63b95ef0 (Heist's `fixpt/` subtree), x86_64
Linux. Found when 63b95ef0's `length` and `list-length` began to give a
`nat`: the CFA (`cfa/fx26.fx`) passes one to a procedure of its own taking
an `int`, and was refused when run from its `.fasl`s, though compiled
without complaint.

## The bug

Every `nat` is an `int` (`docs/fx26.md`, "Naturals"), but a `nat` is
refused where an `int` is expected when the `int` is a type read back from
a `.fasl`. Two repros.

One file, which a program's `.fasl` cannot keep all of: a name it defines
twice is kept as its form, checked again at load against the declarations
the `.fasl` made, whose types were read from reps.

    ;; a.fx
    (define f (subr pure (int) int) (lambda (n) (+ n 1)))
    (define g (subr (maxeff (read @globals) spin) () int) (lambda () 0))
    (define g (subr (maxeff (read @globals) spin) () int) (lambda () (f (length (list 1 2 3)))))

    $ fixpt compile-file --program a.fx     # accepted
    $ fixpt run a.fx
    fixpt: a.fx:3:69: argument 1 is a nat, where a int is expected
    $ FIXPT_NO_FASL=1 fixpt run a.fx        # accepted

Two files, the callee's from its `.fasl`, the caller's from source:

    ;; a.fx
    (define f (subr pure (int) int) (lambda (n) (+ n 1)))
    ;; b.fx
    (define g (subr (maxeff (read @globals) spin) () int) (lambda () (f (length (list 1 2 3)))))

    $ fixpt compile-file --program a.fx
    $ fixpt run a.fx b.fx
    fixpt: b.fx:1:69: argument 1 is a nat, where a int is expected

Both are accepted from source; the second also with
`(f (the int (length …)))`. The
CFA's case is the first kind: a form of `cfa/fx26.fx` that its `.fasl` did
not keep, checked at load (we did not find which of `kept_binding`'s
reasons it was).

## The cause

`check.rs`'s `sub_rules` (line 3823 at 63b95ef0):

    (Ty::Nat(_), Ty::Base(_)) => b == self.int,

compares type ids, and types are not interned (`Arena::ty` pushes a new
entry each time). A type read from a rep (`reps.rs`, `"base" =>
Ty::Base(…)`) is a new `Ty::Base(int)`, not `self.int`, so the rule
fails. The rule above it, for `i32` and its kin, compares names:

    (Ty::Base(x), Ty::Base(y)) => x == y || (… && self.interner.name(y) == "int")

## What we ask

- The rule by name, as its neighbour is:

      (Ty::Nat(_), Ty::Base(y)) => self.interner.name(y) == "int",

  Heist tried it (not kept in Heist's `fixpt/`). Both repros are
  accepted, and so is the CFA without its workaround: its `basic.fx` test
  gives the expected output from its `.fasl`s. We did not run Fixpt's
  suite with it.
- The other comparisons of a type with the arena's own by id, which a type
  read from a rep would fail in the same way: `(Ty::False, Ty::Base(_)) =>
  b == self.bool_` beside it (we could not make it fail: a `#f` argument
  seems to be typed `bool` already), and `t == self.int` or `self.bool_`
  in `specs.rs` (85, 90), `smt_theory.rs` (145) and `spec_tests.rs`
  (268). Or `Base` types interned, so that comparing ids is sound.
- A test: the one-file repro above. We did not look at whether the
  checker written in FX-26 has the same rule.

Heist works around it with `(the int …)` at the CFA's one call
(`cfa/fx26.fx`), noted in `FIXPT-CHANGES.md`.
