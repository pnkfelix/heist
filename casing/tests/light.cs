;; A light that changes from state to state: events whose writes say
;; what they may change (every other relation that changes is unchanged).
(sig Light (var on (lone Light)))  ; on: a light's own atom if it is on
(sig Switch one (var pressed (set Light)))
(event (toggle (l Light)) (writes on)
  (if (some (join l on)) (no (join l (prime on))) (= (join l (prime on)) l)))
(event (press (l Light)) (writes pressed)
  (= (prime pressed) (union pressed (-> Switch l))))
(fact (no on))
(fact (no pressed))
(fact (always (or (stutter) (some ((l Light)) (or (toggle l) (press l))))))
(assert stays-off (always (no on)))
(check stays-off (Light 1) (steps 1 4))
(assert on-once (all ((l Light)) (eventually (some (join l on)))))
(check on-once (Light 1) (steps 1 3))
(pred (blink) (and (eventually (some on)) (eventually (no on)) (always (eventually (some on)))))
(run blink (Light 1) (steps 1 4))
