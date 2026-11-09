-- casing/tests/ints.cs in Alloy, with noOverflow (-n): an instance whose
-- arithmetic overflows is dropped. casing's arithmetic is exact instead,
-- so the two agree where nothing needs a value out of range.
--# options: -n
--# 1
assert succ { all i: Int | i.plus[1] > i }
check succ
--# 3 skip: a value out of range that is no atom: Alloy's is in range
--# 4 skip: constants out of range (42, 8), and mod, which Alloy lacks
assert divides { all a, b: Int | b != 0 implies a = a.div[b].mul[b].plus[a.rem[b]] }
--# 5
check divides for 3 but 3 Int
--# 6 skip: mod, which Alloy lacks
assert byZero { 1.div[0] = 0 }
--# 7 differs: Alloy defines x div 0; casing leaves it to the solver
check byZero
sig Item { price: Int }
--# 8 differs: the sum passes 7, which noOverflow drops
run { (sum t: Item | t.price) > 20 } for 3 but exactly 3 Item
assert sumNonneg { (all t: Item | t.price >= 0) implies (sum t: Item | t.price) >= 0 }
--# 9
check sumNonneg
assert prices { int[Item.price] = (sum p: Item.price | p) }
--# 10
check prices
