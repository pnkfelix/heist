; syntax-rules, its hygiene, and records.
(define (show . xs) (for-each display xs) (newline))
(define-syntax swap!
  (syntax-rules () ((_ a b) (let ((tmp a)) (set! a b) (set! b tmp)))))
(define tmp 1)
(define other 2)
(swap! tmp other)
(show tmp " " other)
(define-syntax my-or
  (syntax-rules () ((_) #f) ((_ e) e) ((_ e r ...) (let ((t e)) (if t t (my-or r ...))))))
(define t 5)
(show (my-or #f t))
(define-syntax while
  (syntax-rules ()
    ((_ c body ...) (let lp () (when c body ... (lp))))))
(define i 0)
(while (< i 3) (display i) (set! i (+ i 1)))
(newline)
(define-syntax my-let*
  (syntax-rules ()
    ((_ () body ...) (let () body ...))
    ((_ ((x v) rest ...) body ...) (let ((x v)) (my-let* (rest ...) body ...)))))
(show (my-let* ((a 1) (b (+ a 1)) (c (* b 3))) (list a b c)))
(define-syntax for
  (syntax-rules (in from to)
    ((_ x in lst body ...) (for-each (lambda (x) body ...) lst))
    ((_ x from a to b body ...) (do ((x a (+ x 1))) ((> x b)) body ...))))
(for x in '(a b c) (display x))
(for y from 1 to 3 (display y))
(newline)
;; Nested ellipses, and a tail after an ellipsis.
(define-syntax flat
  (syntax-rules () ((_ (a ...) ...) '(a ... ...))))
(show (flat (1 2) (3) (4 5 6)))
(define-syntax pairs
  (syntax-rules () ((_ (k v) ...) (list (cons 'k v) ...))))
(show (pairs (a 1) (b 2)))
(define-syntax last-of
  (syntax-rules () ((_ x ... y) 'y)))
(show (last-of 1 2 3))
(define-syntax vec-first
  (syntax-rules () ((_ #(a b ...)) 'a)))
(show (vec-first #(p q r)))
(define-syntax dotted
  (syntax-rules () ((_ a . rest) '(a rest))))
(show (dotted 1 2 3))
;; A custom ellipsis, and (... ...).
(define-syntax my-list
  (syntax-rules ::: () ((_ x :::) (list x :::))))
(show (my-list 1 2 3))
(define-syntax ell
  (syntax-rules () ((_ x) '(x (... ...)))))
(show (ell z))
;; Local macros.
(show (let-syntax ((double (syntax-rules () ((_ x) (* 2 x))))) (double 21)))
(show (letrec-syntax ((ev? (syntax-rules () ((_ n) (if (= n 0) #t (od? (- n 1))))))
                      (od? (syntax-rules () ((_ n) (if (= n 0) #f #t)))))
        (ev? 2)))
(define (f)
  (define-syntax add1 (syntax-rules () ((_ x) (+ x 1))))
  (add1 41))
(show (f))
;; A macro that defines.
(define-syntax def-const (syntax-rules () ((_ name v) (define name v))))
(def-const answer 42)
(show answer)
;; Shadowing a keyword locally.
(show (let ((if (lambda (a b c) 'shadowed))) (if 1 2 3)))
(show (let ((list vector)) (list 1 2)))
;; Records.
(define-record-type point (make-point x y) point? (x point-x set-point-x!) (y point-y))
(define p (make-point 3 4))
(show (point? p) " " (point? 5) " " (point-x p) " " (point-y p))
(set-point-x! p 10)
(show (point-x p))
(write p) (newline)
(show (guard (e (#t (error-object-message e))) (point-x 5)))
;; cond-expand, include-free library forms.
(cond-expand (r7rs (show "r7rs")) (else (show "other")))
(cond-expand ((and s7st (not foo)) (show "s7st")) (else (show "no")))
(import (scheme base) (scheme write))
(define-library (my lib) (export double) (import (scheme base)) (begin (define (double x) (* 2 x))))
(import (my lib))
(show (double 4))
