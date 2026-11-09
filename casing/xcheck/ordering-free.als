-- casing/tests/ordering-free.cs in Alloy
open util/ordering[Day] as ord
sig Day {}
one sig Monday extends Day {}
--# 1
run { last = Monday }
--# 2
run { first = Monday }
assert line { (all d: Day | lone d.ord/next and lone ord/next.d)
              and Day = first.*ord/next and no ^ord/next & iden }
--# 3
check line for 4
