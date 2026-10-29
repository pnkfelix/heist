# Proposal to Fixpt: finding soundness bugs by machine, and a mechanized proof

Status: open. Drafted 2026-10-29 by Heist, for the user to take to the
Fixpt team. Against Fixpt 6505d8bb. Prompted by the masking bug of
`fixpt-mask-hides-acyclic-writes.md`, which was found only because the user
asked "couldn't effect masking bypass that property?". The user's two
questions: what method would have found it without such a question, and
what framework to model FX-26 in and prove its static semantics sound
against its dynamic semantics, termination of `spin`-free code included.

## What the bug says about the existing proof

`docs/research/soundness.md` labels Corollary C2, "frozen data is never
written; `finite` data is acyclic", **Proved** (from T1 and T2 over the
core K26). The bug breaks C2: a location allocated at `acyclic` is written
after it is made. So the hole is in a proof believed complete, not in an
unproved corner. Where, we believe:

- **The region substitution.** `f` is typed with `r` abstract, then `r :=
  acyclic`. That substitution preserves typing only if every write to `r`
  is still in the effect, and masking dropped it (`mask_keeps` drops `read`
  and `write` on a region only the result mentions). In K26 the
  substitution lemma must carry a side condition, no write to a region
  instantiated at a frozen one, that masking can falsify.
- **T0, the elaboration** of the checkers' derivations into K26, is
  "sketched": the step where the checkers' masking and K26's typing could
  part.
- **T3 does not cover it.** T3 ("masking hides only fresh state") speaks of
  locations of `dom σ` before the run; this write is to a location the call
  made. T3 can hold while C2 fails.

## 1. Finding such bugs by machine

**Make each theorem a monitor, and generate programs against them.**

### Monitors: a sanitizer machine

A reference interpreter (or an instrumented machine) in which regions exist
at run time: each location tagged, as it is allocated, with the region its
allocation was *instantiated* at. It checks each claim the type system
makes where it could fail:

| theorem | monitor |
| --- | --- |
| C2, frozen | a write to a location tagged frozen (`const`, `acyclic`, any place) |
| C2, acyclic | data reaching a position typed `acyclic` has no cycle |
| T3, effects | at each call, the reads and writes of locations older than the call are covered by its latent effect under the instantiation |
| T5, termination | `spin`-free code given a step budget; running out of it |
| C1, places | an access to a place that has ended |

On the repro of `fixpt-mask-hides-acyclic-writes.md`, the first monitor
fires at the `set-cdr!`. Running programs normally cannot find this bug (it
loops, or does not, in silence), and comparing the two checkers cannot
either: they share the rule.

### Generators, by expected yield

1. **Bounded exhaustive enumeration of small typed programs** (the small
   scope hypothesis; SmallCheck or Feat style, or PLT Redex's
   `redex-check`). Klein et al., *Run Your Research* (POPL 2012), found
   errors in most of the published semantics they mechanized and tested
   this way. The witness here is five constructs (`plambda`, `cons`,
   `set-cdr!`, an instantiation at `acyclic`, a walk): within the reach of
   enumeration over K26's grammar.
2. **Feature-interaction generation.** List each rule that *removes*
   effect information (masking, the REPL licence, `letregion` and its kin,
   the exemptions of known procedures) and each that *relies* on it
   (freezing, instantiation at frozen regions, the termination check,
   `par`'s disjointness, the compiler's reordering), and generate programs
   for each pair. This bug is masking × instantiation at a frozen region;
   many of F1–F17 in `soundness-findings.md` look like other cells of the
   same matrix.
3. **Adversarial agents, judged by the monitors.** One agent per
   guarantee: "write a program both checkers accept that the sanitizer
   flags for C2". The monitor makes an agent's claim a run, not an
   argument; "couldn't masking bypass this?" becomes a standing task.
4. **Mutating the test programs** (`crates/fixpt-fx26/tests/programs/`)
   toward those pairs: cheap, and good at variants of bugs already found.

## 2. A formal model and a mechanized proof

**Two layers: an executable model first, then the proof in Rocq (Coq)
with Iris.**

### An executable model of K26

In PLT Redex (FX-87's and FX-91's reference implementations, in
GiffordHistory, are Racket), or as an interpreter in the prover's
language. It is the oracle for the monitors and the enumeration above, and
it makes T0's "sketched" elaboration a definition.

### The proof: Rocq with Iris, by semantic typing

- **Regions as Iris invariants.** A frozen region is a persistent
  invariant (never written); an acyclic one adds that it has no cycle.
  Masking is framing out the ownership of fresh, private regions. The
  substitution `r := acyclic` must re-establish the invariant: where this
  bug would have stopped the proof. RustBelt and Iris's logical relations
  for effect systems are proofs of this kind, mechanized.
- **Termination is the hard part.** Iris's step-indexing gives safety,
  not termination. The routes:
  - *Transfinite Iris* (Spies et al., PLDI 2021), made for
    termination-sensitive reasoning in Iris;
  - a separate logical relation, not step-indexed, for the `spin`-free
    fragment, where the effect system confines higher-order store;
  - the size-change check itself formalized and proved (Krauss mechanized
    size-change termination in Isabelle: a template).

### The alternatives

- **Lean 4**: quick to work in, and the better choice for extracting a
  verified checker; but nothing in it yet matches Iris for higher-order
  store (a Lean port of Iris exists; we do not know how mature it is now).
  Preferable only if the team would rather build that machinery than learn
  Rocq.
- **Isabelle/HOL**: the best automation (Sledgehammer, and the size-change
  formalization), and weaker separation logic for higher-order store.
- **Agda**: good for intrinsically typed definitional interpreters, and
  little automation.

### Scale, and joining the proof to the code

K26's memory fragment is a matter of person-months; everything (control,
places, processes) at RustBelt's scale, of years. To join the proof to the
code without verifying the Rust checker, the checkers can **emit their
typing derivations in K26**, checked by a small kernel proved against the
mechanized rules: each accepted program then carries a proof, and a bug
like this one is a derivation the kernel refuses, however the checkers
came to accept the program. Fixpt already compiles with certificates for
its cellular code; this is the same habit, at the type system.

## Proposed order

1. The sanitizer machine, its five monitors.
2. Enumeration over K26's grammar, and the feature-interaction matrix.
3. The Rocq/Iris proof of C2 and T3 (what Heist's `kit` would rely on:
   its list procedures' `acyclic` signatures).
4. Termination last.
