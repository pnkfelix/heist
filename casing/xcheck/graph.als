-- casing/tests/graph.cs in Alloy
sig Node { edges: set Node }
fact { all n: Node | n not in n.^edges }
pred chain { some a, b, c: Node | b in a.edges and c in b.edges }
--# 1
run chain for 3
assert acyclic { no ^edges & iden }
--# 2
check acyclic for 4
