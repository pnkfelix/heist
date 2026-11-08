;; enum: an abstract sig whose parts are its values, one each, ordered as
;; written (Alloy's enum opens util/ordering on it, its order fixed).
(enum Color Red Green Blue)
(sig Shirt (color Color))
(assert three (= (size Color) 3))
(check three 2)
(assert order (and (= (first Color) Red) (= (join Red next) Green) (= (last Color) Blue) (lt Red Blue)))
(check order)
(run (and (some (join color Green)) (no (join color Red))) (Shirt 2))
