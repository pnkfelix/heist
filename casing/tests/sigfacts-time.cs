;; in a model that changes, a sig fact holds in every state, as in Alloy 6
;; (a fact holds in the first unless it says always)
(sig Cell (val Cell #:lone #:var) #:fact (not (in this (join this val))))
(sig Cell2 (val2 Cell2 #:lone #:var))
(fact (all ((this Cell2)) (not (in this (join this val2)))))
(assert never-self (always (no (inter val iden))))
(check never-self (Cell 2) (steps 1 3))
(assert never-self2 (always (no (inter val2 iden))))
(check never-self2 (Cell2 2) (steps 1 3))
