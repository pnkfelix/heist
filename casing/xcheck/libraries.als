-- casing/tests/libraries.cs in Alloy
open util/relation
open util/graph[Node] as g
open util/graph[P] as pg
sig Node { edges: set Node }
sig P { le: set P }
assert dagAcyclic { g/dag[edges] implies no ^edges & iden }
--# 1
check dagAcyclic
--# 2
run { g/tree[edges] and some edges } for 3 but exactly 3 Node
assert treeOneRoot { (g/tree[edges] and some Node) implies one g/roots[edges] }
--# 3
check treeOneRoot
assert ringStrong { g/ring[edges] implies g/stronglyConnected[edges] }
--# 4
check ringStrong
assert strongRing { g/stronglyConnected[edges] implies g/ring[edges] }
--# 5
check strongRing
--# 6
run { totalOrder[le, P] } for 3 but exactly 3 P
assert toAntisymmetric { totalOrder[le, P] implies antisymmetric[le] }
--# 7
check toAntisymmetric
assert eqSymmetric { equivalence[le, P] implies le = ~le }
--# 8
check eqSymmetric
assert domRan { dom[le] in P and ran[le] in P }
--# 9
check domRan
assert pgRoots { pg/dag[le] implies pg/roots[le] in P }
--# 10
check pgRoots
