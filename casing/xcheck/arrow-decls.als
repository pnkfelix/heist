-- casing/tests/arrow-decls.cs in Alloy
sig D {} sig E {}
--# 1
run { some r: D some -> one E | #r = 3 } for 3 but exactly 2 D, exactly 3 E
--# 2
run { some r: D some -> one E | #r = 3 } for 3 but exactly 3 D, exactly 2 E
assert onto { all r: D some -> one E | #E <= #D }
--# 3
check onto
