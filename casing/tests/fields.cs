;; Fields declared together, (home work Place #:disj): disjoint relations,
;; Alloy's disj home, work: Place. (#:apart is Alloy's f: disj T.)
(sig Place)
(sig Person (home work Place #:lone #:disj) (fav Place #:lone))
(assert apart (no (inter home work)))
(check apart)
(assert not-apart (no (inter home fav)))
(check not-apart)
