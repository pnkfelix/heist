# Macros in Heist's FX-26

Since Fixpt 5983942d, a module file can use the macros it defines itself.
Heist uses a macro where it makes a file shorter: its uses must save more
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
  comment, under the line `;; Macros: each file defines its own, for now`.
  Fixpt can't yet import a macro into a module file:
  `import-with-syntax` there panics (`docs/requests/fixpt-macros-from-heist.md`).
  When it can, the definitions could move to kit.
- **s7st and the CFA** are programs whose files share a top level, so
  `s7st/value.fx`, first in both, defines theirs for all of them. They
  use `iterate`, since three of s7st's files have a variable `loop`.

## What is not rewritten, and why

- **Module files with module parameters** (43 of the 53 such files would
  gain): Fixpt 5983942d refuses a file's own macros there, as "an
  `include` around the use". These files hold most of what macros would
  save: 44,625 characters, against 50,891 saved so far.
  `tools/macros/rewrite.py --with-parameters` rewrites them once Fixpt
  allows it.
- **A use that names an FX-26 keyword** other than at the head of a list,
  such as a variable or a label called `fields`, `cond` or `void`
  (`acyclic`, `pure`, `type`, `region` and `effect` are fine). Fixpt
  refuses such a name in a macro's use, though plain code may bind it.
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

The rewrite keeps every kept part's text as written (comments, strings,
line breaks), shifting the lines of each part as its start moves. It
leaves alone a file that defines a macro already. After a rewrite:
`bin/heist-compile --force all`, then the tests both ways.
