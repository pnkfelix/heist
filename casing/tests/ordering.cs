;; #:ordered, Alloy's util/ordering: a trace in the Alloy 4 style, states
;; in a line. A state after the first holds one more token than the one
;; before it. The atoms of State are interchangeable, so next is fixed to
;; their order, as Kodkod's symmetry breaking fixes it.
(sig Token)
(sig State #:ordered (holds Token #:set))
(fact (no (join (first State) holds)))
(fact (all ((s State)) (implies (some (join s next))
                                (and (in (join s holds) (join (join s next) holds))
                                     (one (diff (join (join s next) holds) (join s holds)))))))
(assert grows (all ((a b State)) (implies (lt a b) (in (join a holds) (join b holds)))))
(check grows)
;; an ordered sig's scope is exact: 4 states need 3 tokens
(assert at-most-two (all ((s State)) (<= (size (join s holds)) 2)))
(check at-most-two (State 4))
(run (= (size Token) 1) (State 4))
;; the module's functions and predicates
(assert ends (and (= (first State) (min State)) (= (last State) (max State))
                  (= (prevs (last State)) (diff State (last State)))
                  (= (nexts (first State)) (diff State (first State)))
                  (= prev (~ next))))
(check ends 5)
(assert pairs (all ((a b State)) (and (= (larger a b) (larger b a)) (in (smaller a b) (union a b))
                                      (iff (lt a b) (gt b a)) (or (lte a b) (gte a b)))))
(check pairs 5)
