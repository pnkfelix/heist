# Changes Heist made to Fixpt

`fixpt/` is a squashed git subtree of Fixpt (`git@github.com:pnkfelix/fixpt.git`).
Heist edits it in place when the editor port needs something FX-26 lacks.
This file records each change: what was needed, why a library could not
do it, and what it cost. Kayak will need the same changes later
(see `docs/fx26-for-yank.md`, "Who does what").

## Base

- Fixpt `main` at 1e4d4ed6 (2026-10-25), added by Heist's 86eff712.

## Reading and moving the base

- Our changes: `git diff 86eff712 HEAD -- fixpt/`. After a pull, use the
  newest `Squashed 'fixpt/' content from commit …` commit instead.
- Taking upstream: `git subtree pull --prefix=fixpt ~/Dev/LangPlay/fixpt main --squash`.
  Upstream rebases its `main` at times; a squashed pull does not care.
- Offering a change upstream: `git subtree split --prefix=fixpt` gives a
  branch of Fixpt's tree with our commits on it.

## Changes

None yet. Each entry takes this form:

### Fn. Title (library | primitive | language)

- **Needed for:** the editor feature, and the `fx26-for-yank.md` requirement.
- **What changed:** files, forms, primitives, types.
- **Why not a library:**
- **Machines covered:** which of Fixpt's machines and checkers have it.
- **Kayak will need:**
