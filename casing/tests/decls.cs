;; Declarations: #:disj, and multiplicities of quantified variables and
;; parameters (higher-order: sets, not atoms).
(sig Node (edges Node #:set))

;; disj: distinct atoms. Without it, a and b may be the same.
(assert apart (all ((a b Node #:disj)) (!= a b)))
(check apart)
(assert not-apart (all ((a b Node)) (!= a b)))
(check not-apart (Node 1))

;; a set of nodes closed under edges, two of them: skolemized, as Alloy does
(run (some ((s Node #:set)) (and (= (size s) 2) (in (join s edges) s))) (Node 2))
;; negated, in a check: also skolemized (the counterexample's set is the
;; solver's to choose), and there is none
(assert sets-in (all ((s Node #:set)) (in s Node)))
(check sets-in)
;; a relation's default multiplicity is set: r ranges over sub-relations
(run (some ((r (-> Node Node))) (and (in r edges) (= (size r) 2))) (Node 2))

;; a universal over sets in a fact, which Alloy refuses (it cannot be
;; skolemized): casing binds every set of nodes. Every nonempty proper
;; subset has an edge leaving it, so the graph is strongly connected.
(pred (connected) (all ((s Node #:some)) (or (= s Node) (some (diff (join s edges) s)))))
(assert reach (implies (connected) (all ((a b Node)) (in b (join a (* edges))))))
(check reach)
;; one and lone over sets count the sets
(run (one ((s Node #:set)) (= s Node)))
(assert lone-none (lone ((s Node #:lone)) (no s)))
(check lone-none)
;; over atoms (#:one), they count atoms
(assert one-atom (iff (one ((a Node)) true) (one Node)))
(check one-atom)

;; disjoint sets: a partition of the nodes in two
(run (some ((s t Node #:some #:disj)) (= (union s t) Node)) (Node 3))

;; a run's parameters: a set of nodes, closed and nonempty, shown as $s
(pred (closed (s Node #:set)) (and (some s) (in (join s edges) s) (some edges)))
(run closed (Node 2))
;; disjoint parameters
(pred (two (a b Node #:disj)) (in b (join a edges)))
(run two (Node 2))
