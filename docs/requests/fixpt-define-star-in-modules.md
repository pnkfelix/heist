# Request to Fixpt: a `define*` item in a module reads `@globals`

Status: drafted 2026-10-28 by Heist, for the user to take to the Fixpt
team. Against Fixpt 6447f9b0. Heist's workaround: `editor/scheme.fx`'s
three hook procedures are `define`, not `define*` (merge 0032cc98).

## The prompt

In a module made by a lambda (or a module-parameters file), a define*
item used as a value gets (read @globals) added to its own effect, so it
no longer fits where its declared type is expected; the same item written
with define does not. Repro, on Fixpt 6447f9b0, both checkers agree:
(define m (module (define-type cmd (subr (maxeff (read @globals) (read
@heap)) () unit)) (define hook (ref (listof (subr pure (int) cmd)
acyclic) @heap) (new nil)))) (define mk (lambda () (module (hide (include
m)) (define* f (subr pure (int) cmd) (lambda (k) (lambda () #u))) (define
r unit (set hook (list f)))))) gives "a (subr pure (int) ...) is expected
here, and this is a (subr (read @globals) (int) ...)". Changing define*
to define makes it check. Heist hit it merging s7st into the modular
editor: editor/scheme.fx sets three hooks to its own define* procedures
(s7-eldoc, s7-no-definition, s7-attach), and we changed those three to
define for now. s7st has 398 define*s, so this would bite if s7st became
modules. Is define* in a module meant to read a global (its own name, for
recursion?), and if so can that read stay out of the type when the item
is used as a value?
