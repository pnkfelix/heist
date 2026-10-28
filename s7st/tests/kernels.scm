; Loops over integers run as machine code (native.fx), and what makes them
; give up, or not be used: each answer is the one the slow way gives.
(define (show . xs) (for-each (lambda (x) (write x) (display " ")) xs) (newline))
(define (count-loop n) (let loop ((i 0) (acc 0)) (if (= i n) acc (loop (+ i 1) (+ acc i)))))
(show (count-loop 10) (count-loop 1000000))
; past 64 bits: given up, then done the slow way, in bignums
(define (grow x n) (if (= n 0) x (grow (* x 3) (- n 1))))
(show (grow 1 30) (grow 1 50) (grow 1 100))
(define (sub-down x n) (if (= n 0) x (sub-down (- x 4611686018427387904) (- n 1))))
(show (sub-down 0 5))
; not integers: the slow way
(show (count-loop 5.0) (grow 1.5 3) (grow 1/2 3))
; constants returned, and zero?, and every comparison
(define (down n) (if (> n 0) (down (- n 1)) 'done))
(define (z n) (if (zero? n) "zero" (z (- n 1))))
(define (cmp a b) (if (< a b) (cmp (+ a 1) b) (if (<= a b) 'le (if (>= a b) (if (= a b) 'eq 'ge) 'no))))
(show (down 1000000) (z 10) (cmp 0 5) (cmp 7 5))
; a free variable read on entry; a parameter that is not
(define (scale k) (let loop ((i 0) (acc 0)) (if (= i 10) acc (loop (+ i 1) (+ acc (* k i))))))
(show (scale 3) (scale -2))
; calling itself through a variable that comes to hold another
(define (f n) (if (= n 0) 'f (f (- n 1))))
(define g f)
(set! f (lambda (n) 'other))
(show (g 5))
; built-ins redefined after the kernel is made
(define (sum-to n acc) (if (= n 0) acc (sum-to (- n 1) (+ acc n))))
(show (sum-to 100 0))
(define saved +)
(set! + (lambda (a b) (- a b)))
(show (sum-to 100 0))
(set! + saved)
(show (sum-to 100 0))
