# Heist: what is to be done

Each item says where its design is. When one is done, it goes, and the
commit that did it says so.

## The CFA (`cfa/`, `docs/cfa.md`)

1. **The editor's flow features, from the CFA.**
   - C-c e and C-c r (`editor/calls.fx`), eldoc in FX-26 buffers, and
     Scheme buffers' notes (`editor/scheme.fx`, from s7st's `analysis`
     answer) should all come from `bin/cfa --serve`.
   - The server needs queries beyond notes for that: the callees at a
     call, the callers of a lambda, and whether a lambda escapes.
   - Then `editor/flow.fx` and `s7st/flow.fx` go, and so do `calls.fx`'s
     synchronous runs.
2. **Types and regions as values** (FX-26).
   - A `plambda` becomes a lambda of its type and region parameters. A
     `proj`, or a module made with region arguments, becomes a call whose
     arguments are region and type constants (`cf-kind`: `@ed`, `buffer`).
   - Then "where does region `r` come from" is "what reaches variable
     `r`".
   - The effects a call can have are its callees' declared effects, with
     their region variables given what reaches them.
3. **Yank's lessons, not yet taken** (`docs/cfa.md`, "Next"):
   - per-definition numbering and warm continuation after an edit, in
     place of a cold start on every change;
   - a set holding unknown dropping its data;
   - small procedures analysed per call site;
   - narrowing by tests;
   - interned sets.
4. **Worlds across languages.** s7st's builtins are FX-26 code
   (`s7st/prims.fx`): a Scheme world could link to them, rather than take
   them as primitives.

## Fixpt

- **The checkers disagree on how to print a list type.** Since Fixpt
  fc9e56fe, `fixpt check editor.fx` ends "the checkers disagree": the
  FX-26 checker prints `(listof T acyclic)` as `(union nil (pairof T
  (listof T acyclic) acyclic))`. Both accept the program. This is to be
  written up as a request (`docs/requests/`).
