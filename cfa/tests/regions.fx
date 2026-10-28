;;; Types and regions flow where the text says them: a plambda's binders
;;; given what each proj gives, a type's use of one a reference to it.
(define fresh (plambda ((r region)) (lambda () (the (ref int r) (new 0)))))
(define a ((proj fresh @ed)))
(define b ((proj fresh @sc)))
(define pair-of (plambda ((t type) (r region)) (lambda ((x t)) (the (listof t r) (list x)))))
(define c ((proj pair-of int @ed) 1))
(define d ((proj pair-of string @fl) "s"))
;;; A call's effect: its callee's declared one, its binders said by what
;;; reaches them.
(define* make-box (poly ((r region)) (subr (alloc r) () (ref int r))) (plambda ((r region)) (lambda () (new 0))))
(define e ((proj make-box @ed)))
(define* bump! (subr (write @sc) ((ref int @sc)) unit) (lambda (b) (set b 1)))
(define f (bump! (the (ref int @sc) (new 0))))
