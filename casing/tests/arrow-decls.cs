;; An arrow's multiplicities in a declaration: a function from D onto E.
(sig D) (sig E)
(run (some ((r (-> (col D #:some) (col E #:one)))) (= (size r) 3)) (exactly D 2) (exactly E 3))
(run (some ((r (-> (col D #:some) (col E #:one)))) (= (size r) 3)) (exactly D 3) (exactly E 2))
(assert onto (all ((r (-> (col D #:some) (col E #:one)))) (<= (size E) (size D))))
(check onto)
