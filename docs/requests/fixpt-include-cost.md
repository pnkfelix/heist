# Request to Fixpt: `include` costs the FX-26 checker too much

Status: done by Fixpt in d0b239f, 6226141 (types interned, the cyclic
walk kept by type; `DONE.md` §149, §151) and 7395549 (`(m T qualified)`,
the second ask), pulled at 62261413 by Heist's 2dde955f. Fixpt measured
4.17 s against 4.10 s as globals; on Heist's machine the editor of
87dae480 starts in 5.0 s against 3.8 s as globals (6.4 s against 4.5 s
before), so not quite parity here. Drafted against Fixpt 6447f9b0. Follows
`fixpt-module-file-parameters.md`, whose measurements these are.

## The prompt

Module-parameters files include every module parameter, hidden, with no
way to opt out, and include is what makes Heist's modular editor slow to
start: 6.4 s against 4.5 s as globals, all of it in the FX-26 checker
(2.3 s → 4.6 s; the Rust checker is unchanged). Measured with
FIXPT_TIME_PHASES=1 fixpt check on frame.fx, our biggest file (1431
lines, 8 module parameters), the FX-26 checker time it adds is 0.97 s as
globals, 1.06 s as a plain (module ...), 1.43 s as (lambda () (module
...)), and 1.97 s as a module that does (hide (include m)) of the 8
modules, with or without the lambda and the parameters. So about 0.9 s of
it is include, for one file. GC grows with it: at most 43.6 M words in
use against 19.5 M, 4 major collections against 2 (FIXPT_GC_SUMMARY).
Something seems wrong for it to cost that much, since the same names as
globals cost almost nothing. Two asks: first, find out why include costs
this much in the FX-26 checker and fix that; second, give
module-parameters a way not to include a parameter, so a file can name
what it uses with import, or reach it with with, instead.
