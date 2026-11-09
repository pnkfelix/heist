-- casing/tests/ints.cs's wrapping commands in Alloy, whose arithmetic
-- wraps (no -n): casing's +% is Alloy's plus.
assert succWrapping { all i: Int | i.plus[1] > i }
--# 2
check succWrapping
