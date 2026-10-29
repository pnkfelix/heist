;;; proof.fx: what a proof harness written in FX-26 calls. A harness is a
;;; procedure of no arguments whose name begins proof-; it loads this file,
;;; as any module, so that it type-checks and runs under Fixpt, where it is
;;; one run: any-integer is 0, any-boolean #f, assume nothing, and assert
;;; fails the run if its test is false. ratfink (fx26.fx) reads these names
;;; as its own forms instead: symbolic values, and checks.

(define* any-integer (subr pure () int) (lambda () 0))
(define* any-boolean (subr pure () bool) (lambda () #f))
(define* assume (subr pure (bool) unit) (lambda (ok) #u))
(define* assert (subr pure (bool) unit) (lambda (ok) (if ok #u (error "assertion failed"))))
(define* cover (subr pure (bool) unit) (lambda (ok) #u))
