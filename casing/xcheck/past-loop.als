-- casing/tests/past-loop.cs in Alloy
one sig S { var x: lone S }
fact { no x }
fact { always (some x' iff no x) }
--# 1
run { eventually (no x and once some x) } for 3 but 1..4 steps
assert firstEmpty { always (no x implies historically no x) }
--# 2
check firstEmpty for 3 but 1..4 steps
--# 3
run { eventually (no x and once (some x and once (no x and before some x))) } for 3 but 1..4 steps
