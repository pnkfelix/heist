-- casing/tests/decls.cs in Alloy
sig Node { edges: set Node }
assert apart { all disj a, b: Node | a != b }
--# 1
check apart
assert notApart { all a, b: Node | a != b }
--# 2
check notApart for 3 but 1 Node
--# 3
run { some s: set Node | #s = 2 and s.edges in s } for 3 but 2 Node
assert setsIn { all s: set Node | s in Node }
--# 4
check setsIn
--# 5
run { some r: Node -> Node | r in edges and #r = 2 } for 3 but 2 Node
--# 6 skip: a universal over sets, in a fact's place: Alloy cannot skolemize it
--# 7 skip: one over sets: Alloy cannot skolemize it
--# 8 skip: lone over sets: Alloy cannot skolemize it
assert oneAtom { (one a: Node | some a) iff one Node }
--# 9
check oneAtom
--# 10
run { some disj s, t: some Node | s + t = Node } for 3 but 3 Node
pred closed[s: set Node] { some s and s.edges in s and some edges }
--# 11
run closed for 3 but 2 Node
pred two[disj a, b: Node] { b in a.edges }
--# 12
run two for 3 but 2 Node
