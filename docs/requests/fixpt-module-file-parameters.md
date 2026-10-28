# Request to Fixpt: files whose parameters are modules

Status: mostly done by Fixpt in 6447f9b0 (2026-10-28), pulled by
Heist's 30d080c6 and used by the editor (87dae480): `module-parameters`
of modules, (1) expressions as items, and (2) every module parameter
included, hidden. Not done: (3). The cost of `include` (6.4 s against
4.5 s) is much reduced by 62261413 (`fixpt-include-cost.md`), which also
gives `(m T qualified)`, a parameter not included. Found using it:
`(module-parameters ())`, for a file with state and no modules, gave a
`(poly () …)` that `load-moduleof` did not apply, so `base.fx` stayed a
`lambda`; Fixpt 35bf4c4f made it a maker of none, and `base.fx` is a
`module-parameters` file now. Drafted
2026-10-28 by Heist, against Fixpt 2d706414.

## The prompt

Heist's editor now runs as 15 load-input files, each a function of the
modules the files before it make (branch editor-modules; thanks for
2d706414, typing is as fast as with globals). Every file had to be
rewritten the same way, and we'd like sugar for it. Each file is now
(lambda ((m-base (load-input-moduleof "base.fx")) (m-buffer
(load-input-moduleof "buffer.fx" m-base)) ...) (module (hide (include
m-base) (include m-buffer) ...) ...the file as it was...)). We'd like to
write instead, as a file's first form, (module-parameters ((m-base
(load-moduleof "base.fx")) ...)), with the rest of the file its items as
now, loaded as ((load-module "buffer.fx") m-base). Today module-parameters
takes only kinds ("a kind is region, place, effect, type, ..."), so this
is refused. Three smaller things from the same conversion, in order of
how much they cost us: (1) a module item that is an expression, run for
its effect when the module is made, in order: the editor's ~200 top-level
registrations, (define-command! "name" ...), had to become (hide (define
x-reg-N (define-command! ...))); (2) a short way to use a module's names
in a file without giving them on, which is (hide (include m)) for every
parameter now, or that as the default for a module parameter; (3) a
parameter typed by a file alone, its own module arguments taken from the
parameters before it of the same files, so that the n-th file need not
repeat (load-input-moduleof "buffer.fx" m-base) for every file before it.
Separately, start-up is 6.1 s against 4.4 s as globals, and we measured
where (FIXPT_TIME_PHASES=1 fixpt check): the Rust checker is the same,
2.3 s, but the FX-26 checker goes from 2.3 s to 4.6 s. Most of it is
frame.fx, our biggest file (1431 lines, 8 module parameters): it adds
0.97 s to the FX-26 checker as globals, 1.06 s as a plain (module ...),
1.43 s as (lambda () (module ...)), and 1.97 s as a module that does
(hide (include m)) of the 8 modules, with or without the lambda and the
load-input-moduleof parameters. So the parameters' types cost nothing we
can see; include does, about 0.9 s for that one file. GC is a part of
it: at most 43.6 M words in use against 19.5 M, 4 major collections
against 2 (FIXPT_GC_SUMMARY). Is (1)-(3) sound and worth it, is
module-parameters the right place for the main one, and can include, or
whatever (2) becomes, cost what the same names cost as globals?
