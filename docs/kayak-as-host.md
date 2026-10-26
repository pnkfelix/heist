# Kayak as Heist's host, instead of Fixpt: where it stands (2026-10-26)

`kayak/` is a squashed git subtree of Kayak (`git@github.com:pnkfelix/kayak.git`),
main at 18da385, added by Heist's ee65a9cb. As with `fixpt/`: our
changes are `git diff ee65a9cb HEAD -- kayak/`; upstream comes in by
`git subtree pull --prefix=kayak ~/Dev/LangPlay/kayak main --squash`.
Kayak's own Fixpt pin (`kayak/FIXPT_REV`, f03cabe2) is newer than
Heist's Fixpt base (1e4d4ed6).

**The question:** can the editor run on Kayak's FX-26 engine
(`kayak-fx26 --run FILE… -- ARG…`) instead of `fixpt run`?

**The answer: not yet, but the distance is short and specific.**
Kayak's checker for FX-26 at large (`kayak-fx26 --check`) agrees with
Fixpt on all of Fixpt's test programs (`kayak/scripts/compare-checkers.py`:
of 433 Fixpt accepts, 0 refused, 64 printed differently; all 341 Fixpt
refuses, refused). Effect polymorphism, refused by KFX, is accepted and
runs (`(poly ((e effect)) …)` with `proj`, `(maxeff e spin)`, a type
abbreviation over an effect, an effect variable in an inner `letrec`:
each gives Fixpt's answer). The engine builds (`cargo build --release -p
kayak-fx26`) and runs the editor's `rope-test.fx`.

## What stops the editor, in the order met

Each was found by running `--check` on the editor's program, then
working around it in a scratch copy to find the next.

1. **`#\delete`** (`screen.fx`): Kayak's reader lacks the R7RS character
   name. Trivial.
2. **Modules loaded from files are checked by KFX's rules, not FX-26's.**
   What is accepted at a program's top level is refused in a file
   loaded with `load-module`. Kayak expands a loaded file into the
   loader (`kfx/check-defs.kfx`, `parameters-given`) and does so only as
   KFX allows:
   - **Effect polymorphism inside a loaded file:** refused ("an effect
     KFX does not have: ~e"). A four-line module defining `twice` over
     an effect, loaded and called, is refused; the same at top level is
     accepted and runs. The editor's `keys.fx` (`read-key`) and
     `core.fx` (the actor library) need it.
   - **Module parameters other than regions:** refused ("module
     parameters KFX gives regions alone"). `core.fx` is
     `(module-parameters ((ed region) (world effect)))`. Inside the
     loaded file, the loader's `world` is rightly not in scope, so the
     effect has to come in as a parameter.

   These two are the real work, and they are Kayak's: its loader made
   FX-26's. Fixpt's test programs do not exercise either, so
   `compare-checkers.py` does not see them.
3. **Fixpt's built-in modules:** Kayak builds in some of them
   (`kfx/built-in.kfx`, `scripts/built-in.py`), not
   `fx26:eager-reader.fx` (with `eager-reader-types.fx`,
   `eager-reader-states.fx`, `syn.fx`) or `fx26:table.fx` (with
   `table-types.fx`), which the editor's syntax actor and flow analysis
   load. Adding them to that list is mechanical.

What the scratch copy did not get past is item 2: with no effect
parameter, `core.fx` cannot name the editor's `world` effect.

## What it would then lack: primitives

Checked one by one under `--check`:
- **Heist's own changes to Fixpt** (`FIXPT-CHANGES.md`): `type-at` (F3,
  C-c t), the six `process-*` and the `(io process)` effect (F4: compile,
  grep, shells), and `attempt` (F1: a command's failure caught in
  place). Kayak has none, as expected: Heist has not offered them
  upstream.
- **`parse-nat`**: missing.
- **There:** `terminal-raw`, `terminal-restore`, `terminal-size`,
  `stdin-ready?`, `read-byte`, `u8->int`, `read-file`, `write-file`,
  `list-dir`, `utf8->string`, and the concurrency the actor core is
  built on (`spawn`, `send`, `receive`, `pselect`, `race`, `par`,
  `icell-get`).

## In short

To run the editor on Kayak:
- **Kayak:** its module loader must check loaded files as FX-26 (effect
  polymorphism) and take effect parameters. It also needs
  `#\delete`, `parse-nat`, and the reader and table built-in modules.
- **Heist's three Fixpt changes** (F1 `attempt`, F3 `type-at`, F4
  processes) must be ported. Or the editor runs without them at first:
  without C-c t and subprocesses, and without catching a command's
  failure.

After that, whether the rest of the editor's FX-26 passes is unknown
until those refusals are past; the checker's agreement with Fixpt on
774 programs suggests most of it will.

Speed is the other question, unmeasured here: Kayak PLAN §9 (as of
2026-10-14) put its engine at about 9× Fixpt's slowest machine on `fib`,
with native tiers planned.
