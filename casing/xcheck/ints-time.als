-- casing/tests/ints-time.cs in Alloy. Alloy's plus wraps, so tick says
-- what casing's exact + means: at 7, where 8 is no atom, it cannot happen.
one sig Counter { var n: Int }
fact { Counter.n = 5 }
pred tick { Counter.n != 7 and Counter.n' = Counter.n.plus[1] }
pred wrap { Counter.n' = Counter.n.plus[1] }
fact { always (Counter.n' = Counter.n or tick or wrap) }
--# 1
run { eventually Counter.n = 7 } for 3 but 1..4 steps
assert tickStops { always (Counter.n = 7 implies not tick) }
--# 2
check tickStops for 3 but 1..4 steps
assert neverNegative { always Counter.n >= 0 }
--# 3
check neverNegative for 3 but 1..5 steps
