; lockpick timeout
; found by fuzz_smt.py, seed 485668043
(declare-const v1 Bool)
(declare-const v2 Bool)
(declare-const v3 Bool)
(assert ((_ pbeq 1680 3000) v3))
(assert ((_ pbeq 2576 3000 -3 -1) (not (xor v3 v2 false)) v2 v1))
