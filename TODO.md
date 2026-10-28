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
     - Scheme is less so. On s7st's `prelude.scm`, 90 of 453 notes hold
       unknown, down from 160:
       - `apply` calls with its list's elements;
       - rest parameters are lists;
       - built-ins that call what they are given say how (`m-calls`):
         `call/cc`, `dynamic-wind`, `call-with-values`,
         `with-exception-handler`, the prelude's `filter`, `fold`,
         `member` and `assoc` with a procedure, hash tables' walkers, and
         ports' `call-with-…`;
       - records' procedures are lambdas over a record site.
       - narrowing by tests (2026-10-28), as yank's first steps: a
         branch knows what a builtin predicate (`pair?`, `procedure?`, …;
         `integer?` only in the then-branch), a record's predicate, a
         truth test (`#t` and `#f` are kinds of their own), or `not` of
         one said of a local variable no `set!` assigns. Notes holding
         several values 129 to 114.
       - the rest of yank's narrowing: after an `if` one of whose
         branches cannot return (`error`, `raise`, `exit`), the forms
         after it; comparisons with constants (`eq?`, `eqv?`, `equal?`,
         `memq`, `memv`, `member`; `case`), quoted symbols kinds of their
         own (`'add`, widened to `symbol` past 8 in a cell); fields
         nothing stores to (`(car x)`, a record's field: accessors and
         modifiers are fields read and written); the program's own
         one-parameter predicates, read as formulas; `and` and `or`; a
         `let`'s variable bound to another (`case`'s key) narrowing it too.
         Notes holding several values 114 to 111.
       What is left is mostly the prelude's own library procedures, whose
       callers are outside it. A set holding unknown dropping its data
       (yank's collapse) is there, but off (`bin/cfa --collapse`): it only
       dropped sites here (kinds cost nothing and say what is known), and
       even so made 27 more notes hold unknown on the editor, for no time
       saved -- yank needed it where worlds did not finish. Next:
       `make-parameter` and promises (the prelude makes them as closures
       over pairs). Beyond yank's narrowing still: correlated values
       (`(cdr x)` a list because `(pair? x)`), and `or` narrowing its
       `then` (to the union of its tests). FX-26 narrows by `tagcase` and
       `typecase` already.
   - Notes by contour (what a call or variable is in each context), not
     merged, before small procedures per call site can show anything.
3. **Scheme worlds of libraries** (2026-10-28, done in part). A Scheme
   file's world is it and the libraries it imports, all the way down,
   found where s7st finds them, in `-L` directories, under the
   directories of the files' own libraries, and in their own directory.
   On yank's `cfa.sld` (1906 lambdas with its libraries), it settles in
   1.5-2.6 s. Notes holding unknown went from 2828 of 5065 (alone) to
   1093 of 4357, after modelling:
   - R6RS and SRFI 69 hash tables as sites;
   - the `c[ad]+r` family as fields;
   - vectors and lists converted, element to element;
   - `make-parameter` and `parameterize` as a cell;
   - `call/cc`'s continuation as a lambda storing into the call's result;
   - R6RS fixnums and Larceny's sizes as first order;
   - built-ins `s7-builtin-result` did not know, by what they give.
   `bin/cfa --progress` says where unknown came from: escapes by
   primitive, names defined nowhere, and the first cells to hold
   unknown. Left:
   - the next seeds (`census` walks Larceny's heap: rightly unknown;
     `lambda->core`'s records);
   - a library edited does not re-analyse the worlds that import it (a
     world's key is its file);
   - libraries share one namespace, so names the libraries keep to
     themselves can collide.
   - Lists a site a position (yank's spine, 32; 2026-10-28): `list`, rest
     arguments, and `map`'s results (a list of each call's own, built
     position by position); `apply` gives a list's elements by position.
     The prelude's notes holding unknown 75 to 41; yank's cfa.sld 1093 to
     1081, but 2.6 s to 8.2 s (a spine of 8: the same notes, 7.0 s --
     the cost is `map`'s results flowing, not the sites). Not yet: a
     function's results apart by position (they are per task: at depth
     0, `map`'s positions hold the same).
   - Small procedures' call sites as contexts, and sites split by
     contour (2026-10-28, yank's): a named, non-recursive procedure of
     at most 40 nodes is called in a contour of its call site even at
     depth 0, and a lambda made in one runs where it was made; a site in
     a recursive procedure is split by the contour allocating it, at most
     8 a site. Yank's cfa.sld: notes holding unknown 1081 to 1052, but
     8.2 s to 19.7 s (yank measured +15%: here 1877 contours, the
     closures made in small procedures copied for each); splitting every
     site, not only recursive procedures', was 48 s for the same notes.
     To measure: what of the cost is the closures made in small ones.
   - What each context sees (2026-10-28): notes stay the union, and
     `bin/cfa --contexts`, the server's `contexts` query and the
     editor's C-c d say, at a variable or call whose contexts see
     different things, each: `in line 7: inc ; in line 8: dbl`.
4. **Worlds across languages.** s7st's builtins are FX-26 code
   (`s7st/prims.fx`): a Scheme world could link to them, rather than take
   them as primitives.

## Fixpt

- **The checkers disagree on how to print a list type.** Since Fixpt
  fc9e56fe, `fixpt check editor.fx` ends "the checkers disagree": the
  FX-26 checker prints `(listof T acyclic)` as `(union nil (pairof T
  (listof T acyclic) acyclic))`. Both accept the program. This is to be
  written up as a request (`docs/requests/`).
