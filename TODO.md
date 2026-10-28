# Heist: what is to be done

Each item says where its design is. When one is done, it goes, and the
commit that did it says so.

## The CFA (`cfa/`, `docs/cfa.md`)

1. **Types and regions as values** (FX-26).
   - A `plambda` becomes a lambda of its type and region parameters. A
     `proj`, or a module made with region arguments, becomes a call whose
     arguments are region and type constants (`cf-kind`: `@ed`, `buffer`).
   - Then "where does region `r` come from" is "what reaches variable
     `r`".
   - The effects a call can have are its callees' declared effects, with
     their region variables given what reaches them.
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
