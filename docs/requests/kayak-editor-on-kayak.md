# A request to the Kayak team: what Heist's editor needs to run on kayak

Status: drafted 2026-10-26 by Heist, for the user to take to the Kayak
team. Measured at kayak 18da385 (Fixpt pin f03cabe2).

---

Heist is a family of FX-26 programs; the first is an Emacs-like editor,
about 345 KB of FX-26 in fourteen files, today run by `fixpt run`. We
would like to run it on `kayak-fx26 --run` instead. `kayak-fx26 --check`
already agrees with Fixpt on every test program of Fixpt's
(`scripts/compare-checkers.py`), and accepts and runs effect polymorphism
at a program's top level. What stops the editor is narrower than that
agreement suggests: one gap in how files loaded with `load-module` are
checked, which Fixpt's test programs do not reach, and four small
things. In order of importance:

## 1. Files loaded with `load-module` are checked by KFX's rules

A loaded file is expanded into the program that loads it
(`kfx/check-defs.kfx`, `parameters-given`), and checked as KFX would
check it, not as `--check` checks a program's own top level. Two things
FX-26 allows there are refused. The editor needs both: its actor
library is a module parameterized by the client's effect, and its key
decoder is polymorphic in the effect of its byte source.

**1a. Effect polymorphism inside a loaded file.** The same definition
is accepted, and runs, at top level.

`mod.fx`:
```scheme
(define-type (thunk (e effect)) (subr e () int))
(define twice (poly ((e effect)) (subr (maxeff e spin) ((thunk e)) int))
  (plambda ((e effect)) (lambda (f) (+ (f) (f)))))
```

`main.fx`:
```scheme
(define m (load-module "mod.fx"))
(import m twice (type thunk))
(define* main (subr (maxeff (io clock) spin) () int)
  (lambda () ((proj twice (io clock)) (lambda () 21))))
```

- `fixpt run main.fx`: exit status 42.
- `kayak-fx26 --check main.fx` and `--run main.fx`: `kfx: mod.fx:2: in
  made--load--0--main: an effect KFX does not have: ~e`.
- With `mod.fx`'s two definitions pasted into `main.fx` in place of the
  load and import, kayak checks it and `--run` exits 42.

**1b. Module parameters that are not regions.**

`runner.fx`:
```scheme
(module-parameters ((r region) (e effect)))
(define run-twice (subr (maxeff e spin) ((subr e () int)) int)
  (lambda (f) (+ (f) (f))))
```

`main.fx`:
```scheme
(define m ((proj (load-module "runner.fx") @g (io clock))))
(import m run-twice)
(define* main (subr (maxeff (io clock) spin) () int)
  (lambda () (run-twice (lambda () 21))))
```

- `fixpt run main.fx`: exit status 42.
- `kayak-fx26 --check main.fx` and `--run main.fx`: `kfx: runner.fx:
  module parameters KFX gives regions alone, as many as the file has`.

The loaded file cannot instead name an effect the loader defines: in
FX-26 a loaded file does not see the loader's definitions, so the
effect must come in as a parameter.

**Why the comparison with Fixpt does not see this:** no program in
Fixpt's `tests/programs` loads a file that is polymorphic in an effect,
or gives a module an effect. Both programs above could join kayak's
test programs as they are, with Fixpt's answer, 42.

## 2. Two of Fixpt's built-in modules

The editor loads `fx26:eager-reader.fx` (for its incremental syntax
analysis) and `fx26:table.fx` (for its flow analysis). Kayak builds in
neither (`scripts/built-in.py`, `MODULES`); `kayak-fx26` says `kfx:
cannot read fx26:eager-reader.fx`. With what they load:

- `fx26:eager-reader.fx`, `fx26:eager-reader-types.fx`,
  `fx26:eager-reader-states.fx`, `fx26:syn.fx`
- `fx26:table.fx`, `fx26:table-types.fx`

All six are in Fixpt at the pin (`crates/fixpt-fx26/src/`).

## 3. `parse-nat`

Fixpt's `(subr pure (string int) int)` (`standard.rs`, at the pin).
`kayak-fx26 --check` on `(define x parse-nat)`: `nothing is named
parse-nat`.

## 4. The character name `#\delete`

R7RS's name for character 127. `(define c char #\delete)`: Fixpt
checks it (`define c : char ! pure`); kayak says `no character is named
delete`.

## What Heist will handle itself

Heist has changed its own copy of Fixpt three times (Heist's
`FIXPT-CHANGES.md`), and the editor uses all three:

- `attempt`, a failure caught in place;
- `type-at`, the checker's type at a place in a program's text;
- `(io process)` and six `process-*` primitives, for programs run
  beside this one.

Fixpt has not taken them, so we do not ask kayak for them: the
reference should not run ahead of its oracle. Until Fixpt has them,
Heist would run on kayak without those features.

## What we could not see past

We found each refusal by working around the one before it, in a copy
of the editor. We could not work around 1b, so we do not yet know what,
if anything, kayak refuses after it. Given the checker's agreement with
Fixpt, we expect little.

Heist's own record of how this was found: `docs/kayak-as-host.md`.
