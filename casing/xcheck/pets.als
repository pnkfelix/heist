-- casing/tests/pets.cs in Alloy
sig Person { owns: set Animal }
abstract sig Animal { owner: lone Person }
sig Dog extends Animal {}
sig Cat extends Animal {}
one sig Rex extends Dog {}
fact { owner = ~owns }
fact { some Rex.owner }
pred twoCats[p: Person] { #(p.owns & Cat) = 2 }
--# 1
run twoCats for 3
assert dogOrCat { all a: Animal | a in Dog or a in Cat }
--# 2
check dogOrCat for 5
assert everyoneOwns { all p: Person | some p.owns }
--# 3
check everyoneOwns for 3
