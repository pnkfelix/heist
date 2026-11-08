;; A counter that changes: tick adds 1, exactly. At 7 no atom is 8, so
;; tick cannot happen there; it does not wrap to -8. wrap adds 1 with +%,
;; and does.
(sig Counter #:one (n Int #:var))
(fact (= (join Counter n) 5))
(event (tick) #:writes n (= (join Counter (prime n)) (+ (join Counter n) 1)))
(event (wrap) #:writes n (= (join Counter (prime n)) (+% (join Counter n) 1)))
(fact (always (or (stutter) (tick) (wrap))))
(run (eventually (= (join Counter n) 7)) (steps 1 4))
(assert tick-stops (always (implies (= (join Counter n) 7) (not (tick)))))
(check tick-stops (steps 1 4))
(assert never-negative (always (>= (join Counter n) 0)))
(check never-negative (steps 1 5))
