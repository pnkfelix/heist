;; Libraries: (open util/relation), (open util/graph S), Alloy's, written
;; in casing, names in kebab-case. #:as names a library's definitions a/…,
;; so one may open util/graph on two sigs.
(open util/relation)
(open util/graph Node)
(open util/graph P #:as pg)
(sig Node (edges Node #:set))
(sig P (le P #:set))

(assert dag-acyclic (implies (dag edges) (no (inter (^ edges) iden))))
(check dag-acyclic)
(run (and (tree edges) (some edges)) (exactly Node 3))
(assert tree-one-root (implies (and (tree edges) (some Node)) (one (roots edges))))
(check tree-one-root)
(assert ring-strong (implies (ring edges) (strongly-connected edges)))
(check ring-strong)
(assert strong-ring (implies (strongly-connected edges) (ring edges)))
(check strong-ring)

(run (total-order le P) (exactly P 3))
(assert to-antisymmetric (implies (total-order le P) (antisymmetric le)))
(check to-antisymmetric)
(assert eq-symmetric (implies (equivalence le P) (= le (~ le))))
(check eq-symmetric)
(assert dom-ran (and (in (dom le) P) (in (ran le) P)))
(check dom-ran)
;; util/graph on P, as pg: its own roots, not Node's
(assert pg-roots (implies (pg/dag le) (in (pg/roots le) P)))
(check pg-roots)
