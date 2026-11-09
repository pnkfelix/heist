-- casing/tests/arrows.cs in Alloy
sig A {} sig B {} sig C {}
one sig Map {
  bij: A one -> one B,
  part: A -> lone B,
  pm: A -> (B one -> one C),
  grp: A -> lone (B -> C)
}
assert sameSize { #A = #B }
--# 1
check sameSize
assert partial { all a: A | lone a.(Map.part) }
--# 2
check partial
--# 3
run { some a: A | no a.(Map.part) } for 3 but 2 A, 2 B, 2 C
assert nested { all a: A, b: B | one b.(a.(Map.pm)) }
--# 4
check nested
assert onePair { all a: A | lone a.(Map.grp) }
--# 5
check onePair
--# 6
run { some a: A | #a.(Map.grp) = 1 } for 3 but 1 A, 2 B, 2 C
