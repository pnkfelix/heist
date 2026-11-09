;; A model that changes: more instances are more traces of the first's
;; configuration (its static relations as they are), as Alloy's "next"
;; (Pardinus's nextP): those of k states, then of k+1, up to the most
;; steps; each a trace not found before, whatever lasso spells it.
(sig L #:one (on L #:lone #:var))
(fact (no on))
;; two traces of 2 states: empty, then on, then back (or not)
(run (eventually (some on)) (M 0) (steps 1 2) #:count)
;; of 3 states, 9 lassos more; 3 of them spell those two again (empty,
;; on, empty, the loop back to on, spells empty, on, empty, on, …): 8
(run (eventually (some on)) (M 0) (steps 1 3) #:count)
;; symmetry is broken in every state. Two lamps, none lit in state 0, one
;; pair in state 1: 4 pairs, each with 2 loops, 8; up to renaming the
;; lamps, a lamp lit by itself or by the other: 2 pairs, 4.
(sig M (lit M #:lone #:var))
(fact (no lit))
(run (and (always (no on)) (eventually (one lit))) (exactly M 2) (steps 2 2) #:count #:symmetry 0)
(run (and (always (no on)) (eventually (one lit))) (exactly M 2) (steps 2 2) #:count)
;; the configuration is the first's: of up to 3 lamps, the formula
;; wants 2, and with no symmetry broken any 2 would do; the next traces
;; keep the first's 2
(run (and (always (no on)) (= (size M) 2) (eventually (one lit))) (M 3) (steps 2 2) #:instances 3 #:symmetry 0)
