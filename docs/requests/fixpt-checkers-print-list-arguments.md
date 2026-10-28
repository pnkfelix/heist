# Request to Fixpt: the checkers print an argument's list type differently

Status: drafted 2026-10-28 by Heist, for the user to take to the Fixpt
team. Against Fixpt ec7a02b0. Seen while porting lockpick to FX-26
(`combo/`): a refused program, so it costs nothing but a message, but
`fixpt check` ends "the checkers disagree" where both refuse it.

## The prompt

The checkers print a list type at an inferred region differently in an
argument mismatch's message. Repro, on Fixpt ec7a02b0, `fixpt check` of:

    (define* f (subr pure ((listof int acyclic)) int) (lambda (l) 0))
    (define* g (subr pure (int) int) (lambda (n) (let ((l (if (> n 0) (list n) nil))) (f l))))

ends "the checkers disagree": the Rust checker says `argument 1 is a
(listof int @r.1), where a (listof int acyclic) is expected`, the checker
written in FX-26 `argument 1 is a (union nil (pairof int (listof int @r.1)
@r.1)), where …`. Both refuse the program, rightly. It looks like
ec7a02b0's fix (a description shown by its class's first node) not yet
reaching the printing of an inferred type in a message: the same list
type, unrolled one level. Please make the FX-26 checker print it as the
Rust one does, `(listof int @r.1)`.
