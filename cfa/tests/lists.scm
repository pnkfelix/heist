;;; Lists a site a position (yank's spine); map by position, its list its own.
(define (inc n) (+ n 1))
(define (dbl n) (* n 2))
(define l (list inc "two" 3))
(define a (car l))
(define b (cadr l))
(define c (caddr l))
(define (pick . xs) (cadr xs))
(define d (pick 1 dbl 3))
(define e (apply (lambda (x y) y) (list "x" inc)))
(define fs (map (lambda (f) f) (list inc dbl)))
(define gs (map (lambda (n) (+ n 1)) (list 1 2)))
(define g ((car fs) 1))
(define h (car gs))
;;; Each position its own: the first of l is inc only, pick's second dbl only.
(define i ((car l) 1))
(define j ((pick 1 dbl 3) 2))
;;; Two lists to one apply: each formal the union of the lists' elements
;;; there; a rest parameter () where the shorter ends.
(define (three x y . z) z)
(define (go l) (apply three l))
(go (list inc "one" 'a))
(go (list dbl 2))
