;; Alloy's types, as its warnings: where the types say an expression is
;; always empty, or two sides always disjoint. They change nothing found.
(sig Person (owns Pet #:set))
(sig Pet (owner Person #:lone))
(sig Cat #:extends Pet) (sig Dog #:extends Pet)
(sig Tame #:in Pet)                                 ; typed as Pet
(sig Rock)
(fact (no (join owns owns)))                        ; a Pet is not a Person: always empty
(fact (no (inter Cat Dog)))                         ; always disjoint
(fact (some (inter Tame Cat)))                      ; fine: Tame is of Pet, Cat below it
(pred (silly (r Rock)) (some (join r owner)))       ; a Rock owns nothing
(fun (pets-of (p Person)) (join p owns))
(assert pets-own (no (join (pets-of Person) owns))) ; through a function: Pet . owns
(assert fine (all ((p Person)) (in (join p owns) Pet)))
(check fine)
(run (some (<: Rock owns)))
(run (in Rock Pet))
