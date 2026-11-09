-- casing/tests/sigfacts-time.cs in Alloy
sig Cell { var val: lone Cell } { this not in val }
sig Cell2 { var val2: lone Cell2 }
fact { all c: Cell2 | c not in c.val2 }
assert neverSelf { always no val & iden }
--# 1
check neverSelf for 3 but 2 Cell, 1..3 steps
assert neverSelf2 { always no val2 & iden }
--# 2
check neverSelf2 for 3 but 2 Cell2, 1..3 steps
