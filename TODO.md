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
2. **Yank's lessons, not yet taken** (`docs/cfa.md`, "Next"). Measured
   first (2026-10-28), so as to take only those that pay:
   - **Warm continuation after an edit: not needed yet.** The server
     analyses the editor's world (20 files, 8,800 notes) in 0.31 s, cold,
     after each edit. Joining strings pairwise and escaping by characters
     took it from 1.7 s, and 4.4 s after an edit.
   - **Precision.**
     - FX-26 is precise already: 83 of 8,800 notes hold unknown, and depth
       1 changes no note (notes merge contours).
     - Scheme is not. On s7st's `prelude.scm`, 115 of 463 notes hold
       unknown, down from 160 since `apply` calls with its list's
       elements and rest parameters are lists. What is left is built-ins
       taken to keep what they are given (`call-with-values`, records,
       `values`), and a library's procedures called only from outside.
       Next: model those built-ins; narrowing by tests; unknown dropping
       data.
   - Notes by contour (what a call or variable is in each context), not
     merged, before small procedures per call site can show anything.
3. **Worlds across languages.** s7st's builtins are FX-26 code
   (`s7st/prims.fx`): a Scheme world could link to them, rather than take
   them as primitives.

## Fixpt

- **The checkers disagree on how to print a list type.** Since Fixpt
  fc9e56fe, `fixpt check editor.fx` ends "the checkers disagree": the
  FX-26 checker prints `(listof T acyclic)` as `(union nil (pairof T
  (listof T acyclic) acyclic))`. Both accept the program. This is to be
  written up as a request (`docs/requests/`).
