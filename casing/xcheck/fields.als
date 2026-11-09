-- casing/tests/fields.cs in Alloy
sig Place {}
sig Person { disj home, work: lone Place, fav: lone Place }
assert apart { no home & work }
--# 1
check apart
assert notApart { no home & fav }
--# 2
check notApart
