-- casing/tests/sigfacts.cs in Alloy
sig Person { likes: set Person, best: lone likes } { this not in likes }
assert noSelf { no likes & iden }
--# 1
check noSelf
assert bestLiked { best in likes }
--# 2
check bestLiked
--# 3
run { some best } for 3 but 2 Person
sig Key {}
sig Room { keys: disj set Key }
sig Box { things: set Key }
assert ownKeys { all disj a, b: Room | no a.keys & b.keys }
--# 4
check ownKeys
assert ownThings { all disj a, b: Box | no a.things & b.things }
--# 5
check ownThings
