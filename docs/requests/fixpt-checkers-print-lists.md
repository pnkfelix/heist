# Request to Fixpt: the checkers print an imported list type differently

Status: drafted 2026-10-28 by Heist, for the user to take to the Fixpt
team. Against Fixpt fff9f9e4 (seen since fc9e56fe). Heist's
`fixpt check editor/editor.fx` has ended "the checkers disagree" since;
both checkers accept the program.

## The prompt

The checkers print a list type a module imports differently when the
module also imports a type abbreviation whose definition uses it. Repro,
on Fixpt fff9f9e4, `fixpt check` of:

    (define m (module
      (define-type cmd (subr pure () unit))
      (define-type cmds (listof cmd acyclic))
      (define-type (reply (s type)) (productof (state s) (cmds cmds)))
      (define-type (msg (s type)) (subr pure (s) (reply s)))))
    (define n (module (import m (type msg cmds))))

ends "the checkers disagree": for n, the Rust checker prints (desc cmds
(listof (subr pure () unit) acyclic)), the checker written in FX-26 (desc
cmds (union nil (pairof (subr pure () unit) (listof (subr pure () unit)
acyclic) acyclic))). Importing cmds alone, or msg alone, they agree. It
looks like the minimal-graph printing (34f8b64) or the interning
(d0b239f, fff9f9e4) of the FX-26 checker meeting the listof that msg's
body holds: the same list type, one node unrolled a level. (Both print m's
own cmds, inside n's lib-like nesting in Heist's case, as (union nil
(pairof cmd cmds acyclic)) -- agreeing, but that too is a listof
unrolled.) Please make the FX-26 checker print it as the Rust one does,
(listof … acyclic).
