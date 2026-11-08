;; #:ordered with a one part: that part's atom is its own, so the atoms are
;; not interchangeable, and next is left to the solver (with the facts that
;; make it a line). Were it fixed, Monday's atom would always come first.
(sig Day #:ordered)
(sig Monday #:one #:extends Day)
(run (= (last Day) Monday))
(run (= (first Day) Monday))
(assert line (and (all ((d Day)) (and (lone (join d next)) (lone (join next d))))
                  (= Day (join (first Day) (* next)))
                  (no (inter (^ next) iden))))
(check line 4)
