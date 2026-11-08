;; Past operators where the loop comes back: state 0 seen again after x
;; was present has x in its past, though its first visit does not.
(sig S one (var x (lone S)))
(fact (no x))
(fact (always (iff (some (prime x)) (no x))))
(run (eventually (and (no x) (once (some x)))) (steps 1 4))
(assert first-empty (always (implies (no x) (historically (no x)))))
(check first-empty (steps 1 4))
;; nested: once more than one level deep needs the loop unrolled twice
(run (eventually (and (no x) (once (and (some x) (once (and (no x) (before (some x)))))))) (steps 1 4))
