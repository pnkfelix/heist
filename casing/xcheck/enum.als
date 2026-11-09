-- casing/tests/enum.cs in Alloy
enum Color { Red, Green, Blue }
sig Shirt { color: Color }
assert three { #Color = 3 }
--# 1
check three for 2
assert order { first = Red and Red.next = Green and last = Blue and lt[Red, Blue] }
--# 2
check order
--# 3
run { some color.Green and no color.Red } for 3 but 2 Shirt
