# Request to Fixpt: a program `.fasl` writes recursive types out in full

Status: done by Fixpt in fc9e56fe (2026-10-28), pulled by Heist's
598ccfe7: s7st's `.fasl`s 4.0 MB in all, compiled in seconds, s7st
starting in 1.08 s against 3.90 s from source. Not checked again: the
stale `prims.fasl` and the abort. Drafted against Fixpt b26b2efc.

## The prompt

A program's .fasl (compile-file --program a.fx b.fx) writes each type in
its `use`, `def` and `init` lines with no abbreviation, its recursive
types unrolled as nested mu's, so the file grows exponentially in the
number of mutually recursive types, and loading it more so. Repro: K
types, each a sumof referring to every other, in a.fx -- (define-type tI
(sumof (zI unit) (c0 (listof t0 acyclic)) ... (cK-1 (listof tK-1
acyclic)))) for each I -- and in b.fx 20 procedures (define* gI (subr pure
(t0) t0) (lambda (x) (g(I-1) x))), then (define main (lambda () 0)). b.fasl
is 59 KB at K=2, 274 KB at 4, 6.8 MB at 6, 46 MB at 7; compiling takes
22 s and running from the .fasls 32 s at K=7, against 0.23 s from source.
s7st (Heist's s7st/, 14 files, s7-value and its kin) hits it: expand.fx's
.fasl is 111 MB for 78 KB of source, one `use s7-qq-cons` line 772 KB
for (subr s7-eff (s7-node s7-node s7-span) s7-node), s7-value unrolled 30
times in it; the whole program took 444 s to compile and 485 s to run
from its .fasls before aborting ("fatal runtime error: failed to initiate
panic, error 5"). Please name the abbreviations a program's types use (as
7bdee41 and ef7011d did for module files), here across a program's
files. Two more things seen in s7st, not minimized: prims.fasl is stale
as soon as it is written ("`s7-init-numbers!` uses `s7-parse-number`,
which is not here at the type it was"), and the abort above.
