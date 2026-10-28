# Request to Fixpt: files whose parameters are modules

Status: drafted 2026-10-28 by Heist, for the user to take to the Fixpt
team. Against Fixpt 2d706414.

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
repeat (load-input-moduleof "buffer.fx" m-base) for every file before it;
those types grow as the square of the files, and checking them is most
of the 1.7 s our start-up still loses to globals (6.1 s against 4.4 s).
Is (1)-(3) sound and worth it, and is module-parameters the right place
for the main one?
