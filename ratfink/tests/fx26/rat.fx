;;; Proofs about combo's rationals (combo/rat.fx), as ratfink checks an
;;; FX-26 program: bin/ratfink ratfink/tests/fx26/rat.fx

(define m-proof (load-module "../../proof.fx"))
(define m-rat (load-module "../../../combo/rat.fx"))
(import m-proof any-integer assume assert cover)
(import m-rat floor-div euclid-div rat-sign int->rat rat-neg rat< rat-max make-rat rat-den)

"floor-div is the floor of n/d, for d > 0."
(define* proof-floor-div (subr spin () unit)
  (lambda ()
    (let ((n (any-integer)) (d (any-integer)))
      (begin
        (assume (> d 0))
        (let ((q (floor-div n d)))
          (begin
            (assert (<= (* q d) n))
            (assert (< n (* (+ q 1) d)))))))))

"The sign of a rational is that of its numerator."
(define* proof-sign (subr spin () unit)
  (lambda ()
    (let* ((n (any-integer)) (r (int->rat n)))
      (begin
        (assert (= (rat-sign r) (cond ((< n 0) -1) ((> n 0) 1) (else 0))))
        (assert (= (rat-sign (rat-neg r)) (- 0 (rat-sign r))))))))

"rat-max is one of its arguments, not below either."
(define* proof-max (subr spin () unit)
  (lambda ()
    (let* ((a (int->rat (any-integer))) (b (int->rat (any-integer))) (m (rat-max a b)))
      (begin
        (assert (not (rat< m a)))
        (assert (not (rat< m b)))
        (cover (rat< a b))))))

"A false claim, for a counterexample: euclid-div is quotient."
(define* proof-euclid-is-quotient (subr spin () unit)
  (lambda ()
    (let ((a (any-integer)) (b (any-integer)))
      (begin
        (assume (not (= b 0)))
        (assert (= (euclid-div a b) (quotient a b)))))))

(define main (subr spin () int) (lambda () 0))
