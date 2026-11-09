-- casing/tests/types.cs in Alloy
sig Person { owns: set Pet }
sig Pet { owner: lone Person }
sig Cat extends Pet {} sig Dog extends Pet {}
sig Tame in Pet {}
sig Rock {}
fact { no owns.owns }
fact { no Cat & Dog }
fact { some Tame & Cat }
pred silly[r: Rock] { some r.owner }
fun petsOf[p: Person]: set Pet { p.owns }
assert petsOwn { no petsOf[Person].owns }
assert fine { all p: Person | p.owns in Pet }
--# 1
check fine
--# 2
run { some Rock <: owns }
--# 3
run { Rock in Pet }
