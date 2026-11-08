;; An arrow's multiplicities, (-> (col A #:one) (col B #:lone)): Alloy's
;; A one -> lone B.
;; Several operands nest to the right, as Alloy's arrows do.
(sig A) (sig B) (sig C)
(sig Map #:one
     (bij (-> (col A #:one) (col B #:one)))         ; a bijection
     (part (-> A (col B #:lone)))                   ; a partial function
     (pm (-> A (-> (col B #:one) (col C #:one))))   ; for each a, B to C a bijection
     (grp (-> A (col (-> B C) #:lone))))            ; for each a, at most one pair
(assert same-size (= (size A) (size B)))
(check same-size)
(assert partial (all ((a A)) (lone (join a (join Map part)))))
(check partial)
(run (some ((a A)) (no (join a (join Map part)))) (A 2) (B 2) (C 2))
(assert nested (all ((a A) (b B)) (one (join b (join a (join Map pm))))))
(check nested)
(assert one-pair (all ((a A)) (lone (join a (join Map grp)))))
(check one-pair)
(run (some ((a A)) (= (size (join a (join Map grp))) 1)) (A 1) (B 2) (C 2))
