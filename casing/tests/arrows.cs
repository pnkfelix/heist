;; An arrow's multiplicities, (-> (one A) (lone B)): Alloy's A one -> lone B.
;; Several operands nest to the right, as Alloy's arrows do.
(sig A) (sig B) (sig C)
(sig Map #:one
     (bij (-> (one A) (one B)))                 ; a bijection
     (part (-> A (lone B)))                     ; a partial function
     (pm (-> A (-> (one B) (one C)))))          ; for each a, B to C a bijection
(assert same-size (= (size A) (size B)))
(check same-size)
(assert partial (all ((a A)) (lone (join a (join Map part)))))
(check partial)
(run (some ((a A)) (no (join a (join Map part)))) (A 2) (B 2) (C 2))
(assert nested (all ((a A) (b B)) (one (join b (join a (join Map pm))))))
(check nested)
