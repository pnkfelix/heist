;; More instances: #:instances n shows up to n, each found by blocking those
;; before; #:count counts them all. #:symmetry n is the length of each
;; lex-leader predicate (20 if not said; 0 breaks no symmetry), as Alloy's
;; symmetry setting. Alloy 6.2.0 counts the same, either way (xcheck/).
(sig A)
(sig B (f B #:lone))
;; 56 instances that differ by atoms' names; 27 up to renaming
(run (in none none) 2 #:count #:symmetry 0)
(run (in none none) 2 #:count)
;; a witness's value tells two instances apart, as a skolem's does in Alloy
(run (some ((a A)) (some a)) 2 (exactly A 2) (B 0) #:count #:symmetry 0)
(run (some ((a A)) (some a)) 2 (exactly A 2) (B 0) #:count)
;; the first three, and whether there are more
(pred (p (b B)) (some (join b f)))
(run p 2 (A 0) #:instances 3)
;; all there are, with fewer than asked for
(run p 2 (A 0) #:instances 10)
;; more counterexamples
(assert has-f (all ((b B)) (some (join b f))))
(check has-f 2 (A 0) #:instances 2 #:count)
