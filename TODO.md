# Heist: what is to be done

Each item says where its design is. When one is done, it goes, and the
commit that did it says so.

## The CFA (`cfa/`, `docs/cfa.md`)

1. **Types and regions: what is left.** Done: a `plambda`'s binders and a
   module file's flow from each `proj` (cfa/fx26.fx), and a call's note
   says its callees' declared effects with their binders said by what
   reaches them. Left:
   - Instantiations the checker infers (no `proj`) are not seen.
   - Effect abbreviations (`cmd-eff`) are said by name, not expanded.
   - A binder's values are those of the empty contour.
2. **Yank's lessons, not yet taken** (`docs/cfa.md`, "Next"):
   - per-definition numbering and warm continuation after an edit, in
     place of a cold start on every change;
   - a set holding unknown dropping its data;
   - small procedures analysed per call site;
   - narrowing by tests;
   - interned sets.
3. **Worlds across languages.** s7st's builtins are FX-26 code
   (`s7st/prims.fx`): a Scheme world could link to them, rather than take
   them as primitives.

## Fixpt

- **The checkers disagree on how to print a list type.** Since Fixpt
  fc9e56fe, `fixpt check editor.fx` ends "the checkers disagree": the
  FX-26 checker prints `(listof T acyclic)` as `(union nil (pairof T
  (listof T acyclic) acyclic))`. Both accept the program. This is to be
  written up as a request (`docs/requests/`).
