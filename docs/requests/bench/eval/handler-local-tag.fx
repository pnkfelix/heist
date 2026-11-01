;; Option 1 with a tag the turn makes: user code polymorphic in its region,
;; given the tag; `insert` captures and aborts to it; the handler collects.
;; Runs: "point; insert a; message 7;". `handled` must declare the control
;; effects on `r`: its prompts around a resumed continuation do not
;; delimit, but the `letregion` that made `r` and the tag masks them (the
;; Fixpt team's reading, 2026-11-01; Heist had declared `turn-eff` alone).
(define-effect turn-eff (maxeff spin nondet (read @globals) (read @ed) (alloc @ed)))
(define-type request (sumof (insert string) (message string) (point unit)))
(define-type requests (listof request acyclic))
(define-type (asked (r region)) (productof (req request) (k (composable int requests turn-eff r))))
(define-type (tag (r region)) (prompt-tag requests (asked r) turn-eff r))
(define-type user-code
  (productof (code (poly ((r region)) (subr (maxeff turn-eff (goto r) (comefrom r)) ((tag r)) unit)))))
;; Ask the handler: `r`'s answer, an int (0 but for `point`).
(define ask (poly ((r region)) (subr (maxeff turn-eff (goto r) (comefrom r)) ((tag r) request) int))
  (plambda ((r region))
    (lambda ((t (tag r)) (q request))
      ((proj (proj call-with-composable-continuation r) requests (asked r) turn-eff int (maxeff turn-eff (goto r) (comefrom r)))
       (lambda ((k (composable int requests turn-eff r))) (abort-current-continuation t (product (req q) (k k))))
       t))))
(define user user-code
  (product (code (plambda ((r region))
                   (lambda ((t (tag r)))
                     (let ((p ((proj ask r) t (sum point #u))))
                       (begin ((proj ask r) t (sum insert "a"))
                              ((proj ask r) t (sum message (int->string p)))
                              #u)))))))
;; The turn: a tag in a region of its own; each request collected, and the
;; code resumed (with 7 for `point`).
(define run (subr turn-eff (user-code) requests)
  (lambda (u)
    (letregion r
      (let ((t (the (tag r) (make-continuation-prompt-tag))))
        (letrec ((handled (subr (maxeff turn-eff (goto r) (comefrom r)) ((subr (maxeff turn-eff (goto r) (comefrom r)) () unit)) requests)
                   (lambda (body)
                     (prompt t (begin (body) nil)
                       (lambda ((a (asked r)))
                         (cons (extract a req)
                               (handled (lambda () (begin ((extract a k) (tagcase (extract a req) (point u 7) (insert s 0) (message s 0))) #u)))))))))
          (handled (lambda () ((proj (extract u code) r) t))))))))
(define shown (subr (maxeff (read @globals) spin) (requests) string)
  (lambda (rs) (if (null? rs) ""
                   (string-append (tagcase (car rs) (insert s (string-append "insert " s)) (message s (string-append "message " s)) (point u "point"))
                                  "; " (shown (cdr rs))))))
(define turn (subr turn-eff (user-code) (sumof (ok requests) (lost string)))
  (lambda (u)
    (attempt (the (sumof (ok requests) (lost string)) (sum ok (run u)))
             (lambda ((why string)) (the (sumof (ok requests) (lost string)) (sum lost why))))))
(define main (subr (maxeff turn-eff (io stdout)) () int)
  (lambda () (begin (tagcase (turn user) (ok rs (write-out (string-append (shown rs) "\n"))) (lost m (write-out m))) 0)))
