-- casing/tests/ordering.cs in Alloy
open util/ordering[State] as ord
sig Token {}
sig State { holds: set Token }
fact { no first.holds }
fact { all s: State | some s.ord/next implies
         (s.holds in s.ord/next.holds and one s.ord/next.holds - s.holds) }
assert grows { all a, b: State | lt[a, b] implies a.holds in b.holds }
--# 1
check grows
assert atMostTwo { all s: State | #s.holds <= 2 }
--# 2
check atMostTwo for 3 but 4 State
--# 3
run { #Token = 1 } for 3 but 4 State
assert ends { first = min[State] and last = max[State]
              and prevs[last] = State - last and nexts[first] = State - first
              and ord/prev = ~ord/next }
--# 4
check ends for 5
assert pairs { all a, b: State | larger[a, b] = larger[b, a] and smaller[a, b] in a + b
                                and (lt[a, b] iff gt[b, a]) and (lte[a, b] or gte[a, b]) }
--# 5
check pairs for 5
