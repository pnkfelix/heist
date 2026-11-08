;; An arrow's multiplicities in a declaration: a function from D onto E.
(sig D) (sig E)
(run (some ((r (-> (some D) (one E)))) (= (size r) 3)) (exactly D 2) (exactly E 3))
(run (some ((r (-> (some D) (one E)))) (= (size r) 3)) (exactly D 3) (exactly E 2))
(assert onto (all ((r (-> (some D) (one E)))) (<= (size E) (size D))))
(check onto)
