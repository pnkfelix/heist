-- casing/tests/time.cs in Alloy
one sig S { var x: lone S }
fact { no x }
fact { always (some x' iff no x) }
assert alternates { always (some x or after some x) }
--# 1
check alternates for 3 but 1..4 steps
assert untilFirst { no x until some x }
--# 2
check untilFirst for 3 but 1..4 steps
assert onceEmpty { always (some x implies once no x) }
--# 3
check onceEmpty for 3 but 1..4 steps
assert sinceEmpty { always (some x implies (some x since no x)) }
--# 4
check sinceEmpty for 3 but 1..4 steps
assert beforeEmpty { always (some x implies before no x) }
--# 5
check beforeEmpty for 3 but 1..4 steps
assert never { always no x }
--# 6
check never for 3 but 1..4 steps
--# 7
run { some x releases no x } for 3 but 1..4 steps
--# 8
run { no x ; some x } for 3 but 1..4 steps
