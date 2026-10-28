# To Fixpt: one module built up file by file, tried on combo

Status: 2026-10-28, Heist's answer to the Fixpt team's suggestion to pass
each file one anonymous module, `env`, built up by `extend`, in place of a
maker call with every module so far as an argument. For the user to take
to the Fixpt team. Against Fixpt ec7a02b0.

## What was tried

The shape cannot be written yet. A file's single `env` must be typed by
everything so far, and nothing in FX-26 names that type by reference:

- there is no type-level `extend`;
- `load-moduleof` takes module values, and a file with one parameter has
  none in scope.

So the experiment was on combo, whose composites have no abstract types
(its datatypes print as transparent descriptions), with each file's `env`
typed by the composite's type written out. The checker printed those types
for `e2 = (extend m-sat m-rat)`, `e3 = (extend e2 m-dimacs)`, … They are 15
to 77 KB, with no abstract types, `select`s or inferred regions. The
program then builds `e2`, `e3`, … with `extend` and gives each maker its
`env`.

## What it gave

Both checkers accept it, and it runs, but every measure is worse:

| Measure | before | env chain |
|---|---|---|
| Rust checker, `fixpt check` | 0.30 s | 1.02 s |
| FX-26 checker, `fixpt check` | 0.67 s | 1.07 s |
| run from `.fasl`s (CPU) | 0.47 s | 1.35 s |

- **FX-26 checker:** argument checking (`k-check-argument`) took the same
  absolute time before and after (365 against 379 samples). It did not
  become one identity check.
- **Rust checker:** its application checks (`synth_app_of`) went from 24 to
  680 samples.

The argument's type (what `extend` built) and the parameter's (the same
type, parsed from its text) are evidently not the same node. That is the
condition the suggestion said to verify first. With the type written out
it does not hold, so the gain would need the parameter's type to *be*
the composite, named by reference.

## What would let it be tried as meant

1. **A way to type a file's parameter as "the composite so far" without
   writing it out**, so that the node is shared. For example, a type
   `(extendof T U)` beside `extend`, or `load-moduleof` given module types
   where no later type selects from a value. With that, the headers would
   be constant-size, as you said.
2. **§69 for the editor.** resolve, syntax, sexp, flow and frame export
   generative types, which a composite would have to carry abstract.

## What it could win, measured

- **Editor, full `fixpt check`:** application checking is about 16% of
  `fixpt check editor.fx` (Rust `synth_app_of` 10.5%, FX-26
  `k-check-argument` 5.9%), not all of it maker calls. Printing the
  programs' types (`show_ty`, 17%) costs as much again.
- **Editor, starting from `.fasl`s:** argument checking is about 11% of
  the load, roughly 0.05 s.
- **Larger, separate wins** are in `docs/requests/fixpt-load-time.md`: a
  source file read whole for its first form, the executable read whole on
  every run, and CRCs. Those took combo's start from 0.49 s to 0.29 s.
