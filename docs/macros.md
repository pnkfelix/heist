# Macros in Heist's FX-26

Since Fixpt 5983942d, a module file can use the macros it defines
itself; since eed406e0, one with module parameters too. Heist uses a macro where it makes a file shorter: its uses must save more
characters than its definition costs. `tools/macros/` does the rewriting,
and keeps to that rule.

## The macros

| macro | stands for |
| --- | --- |
| `(loop go E ((x T init) …) R body)` | `(letrec ((go (subr E (T …) R) (lambda (x …) body))) (go init …))` |
| `(when c e …)` | `(if c (begin e …) #u)` |
| `(unless c e …)` | `(if c #u (begin e …))` |
| `(def-prim name min max (a) body)` | `(s7-prim! name min max (lambda ((a s7-values)) body))`, s7st only |

`loop` is a named loop, typed: its variables, each with its type and
first value, then the type of its result. The body calls `go` to loop
again.

**Where a file already uses a macro's name**, the file defines the macro
under another name: `loop` as `iterate`, `when` as `if-so`, `unless` as
`if-not`. Such a use might be a variable, a field or a tag (ratfink's
`rf-loop-at` has a field `loop`). `def-prim` is not called `prim`,
which is a tag of s7st's values. A name in quoted data does not count.

## Where they are defined

- **A module file** defines the macros it uses, after its header
  comment (and its `module-parameters`), under the line
  `;; Macros: each file defines its own, for now`. Fixpt can't yet
  import a macro into a module file: `import-with-syntax` there is
  refused, "not yet" (`docs/requests/fixpt-macros-from-heist.md`, 1(b)).
  When it can, the definitions could move to kit.
- **s7st and the CFA** are programs whose files share a top level, so
  `s7st/value.fx`, first in both, defines theirs for all of them. They
  use `iterate`, since three of s7st's files have a variable `loop`.

## What is not rewritten, and why

- **A use with an FX-26 keyword alone as one of its parts**, other than
  a loop's name: a loop variable named `region`, or `fields` as a first
  value or as `when`'s test. Fixpt eed406e0 refuses these
  (`docs/requests/bench/macros/keyword-args.fx`), though it takes a
  keyword inside a part's list, and plain code may bind it.
- **A loop whose name is used as other than a call** in its body, such
  as a label.
- **A form with a comment in a part the rewrite drops.**
- **A loop that isn't called at once**, with its variables' first values:
  `(letrec ((go …)) (begin (go 0) …))` stays a `letrec`.

## The tools

```
python3 tools/macros/survey.py                 # what could be rewritten, per file
python3 tools/macros/rewrite.py FILE…          # module files: what it would do
python3 tools/macros/rewrite.py --write FILE…  # … and do it
python3 tools/macros/rewrite.py --write --program $(for f in $(cat s7st/program) main.fx; do echo s7st/$f; done) \
                                                  $(for f in $(cat cfa/program); do echo cfa/$f; done)
python3 tools/macros/prims.py --write …        # s7st's registrations, the same files
```

Saved: 50,891 characters on Fixpt 5983942d (module files without
parameters, s7st and the CFA), and 47,980 more on eed406e0 (43 files
with module parameters, and uses that name a keyword), 98,871 in all.

A file or program that defines some of these macros already has its
remaining uses rewritten with them, and the others' definitions added
after its last `define-syntax` if they pay. A macro's own definition is
never rewritten.

The rewrite keeps every kept part's text as written (comments, strings,
line breaks), shifting the lines of each part as its start moves. After a rewrite:
`bin/heist-compile --force all`, then the tests both ways.
