;; Sig facts (#:fact F, of each atom `this`), fields whose type mentions
;; `this`, and #:apart fields (distinct owners' values apart).
(sig Person (likes Person #:set)
            (best (join this likes) #:lone)          ; one of those this likes
            #:fact (not (in this (join this likes))))
(assert no-self (no (inter likes iden)))
(check no-self)
(assert best-liked (in best likes))
(check best-liked)
(run (some best) (Person 2))

(sig Key)
(sig Room (keys Key #:set #:apart))
(sig Box (things Key #:set))
(assert own-keys (all ((a b Room #:disj)) (no (inter (join a keys) (join b keys)))))
(check own-keys)
(assert own-things (all ((a b Box #:disj)) (no (inter (join a things) (join b things)))))
(check own-things)
