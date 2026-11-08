;; A first model: nodes and edges, acyclic.
(sig Node (edges Node #:set))
(fact (all ((n Node)) (not (in n (join n (^ edges))))))
(pred (chain) (some ((a b c Node)) (and (in b (join a edges)) (in c (join b edges)))))
(run chain 3)
(assert acyclic (no (inter (^ edges) iden)))
(check acyclic 4)
