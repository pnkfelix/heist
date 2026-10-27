;;; session.fx: what a client of s7st calls.
;;;
;;;   (s7-init!)                 the interpreter made ready: once
;;;   (s7-input-state text)      whether text typed is all there: complete,
;;;                              incomplete (RET should not send it), bad
;;;   (s7-start! text file echo) the text's forms, to run; each value shown,
;;;                              as a REPL does, if `echo`
;;;   (s7-continue! fuel)        at most `fuel` steps run: still running,
;;;                              done (with the last value), or failed
;;;   (s7-take-output!)          what was written since last taken
;;;   (s7-interrupt!)            what runs stopped
;;;   (s7-eval-string! text)     all of that at once: the output, then the
;;;                              last value or the error (for tests)
;;;
;;; There is one interpreter: its globals are FX-26 globals.

"Where the machine is: stopped, when it has nothing to run."
(define s7-machine (ref s7-state @sc) (new (sum s-done s7-unspecified)))

(define-type s7-status (sumof (running unit) (done s7-value) (failed string)))
(define-type s7-input (sumof (complete unit) (incomplete unit) (bad string)))

"What a condition that nothing handled says: an error's message and its
irritants, written; anything else, written."
(define* s7-condition-message (subr s7-eff (s7-value) string)
  (lambda (obj)
    (tagcase obj
      (errobj e (letrec ((go (subr s7-eff (s7-values (listof string acyclic)) (listof string acyclic))
                               (lambda (l acc) (if (null? l) acc (go (cdr l) (cons (s7-show (car l) #t) (cons " " acc)))))))
                  (s7-concat (reverse (the (listof string acyclic)
                                           (go (s7-value->values (extract e irritants)) (list (extract e message))))))))
      (else y (string-append "uncaught exception: " (s7-show y #t))))))

"Whether `text` holds whole data, as a REPL's RET asks."
(define* s7-input-state (subr s7-eff (string) s7-input)
  (lambda (text)
    (tagcase (s7-read-all text "")
      (data d (sum complete #u))
      (stop r (tagcase r
                (incomplete u (sum incomplete #u))
                (bad b (sum bad (extract b message)))
                (else y (sum complete #u)))))))

"The forms of `text` (from `file`, \"\" if typed) made what the machine
runs next, each value shown if `echo`. (none), or what is wrong with it."
(define* s7-start! (subr s7-eff (string string bool) (sumof (none unit) (bad string)))
  (lambda (text file echo)
    (tagcase (s7-read-all text file)
      (data forms (begin (set s7-machine (s7-return-state s7-unspecified (list (sum k-top (product (forms forms) (echo echo) (text text))))
                                                          s7-no-dyn))
                    (sum none #u)))
      (stop r (sum bad (tagcase r
                         (incomplete u "the text ends inside a datum")
                         (bad b (string-append (s7-where (product (file file) (start (extract b at)) (end (extract b at))) text)
                                               (extract b message)))
                         (else y "")))))))

(define* s7-busy? (subr (read @sc) () bool)
  (lambda () (not (s7-stopped? (get s7-machine)))))

"At most `fuel` steps run."
(define* s7-continue! (subr s7-eff (int) s7-status)
  (lambda (fuel)
    (let ((st (s7-run (get s7-machine) fuel)))
      (begin
        (set s7-machine st)
        (tagcase st
          (s-done v (sum done v))
          (s-failed f (sum failed (s7-condition-message (extract f obj))))
          (else y (sum running #u)))))))

"What `display` and its kin have written to the console since this was
last asked."
(define* s7-take-output! (subr s7-eff () string)
  (lambda ()
    (tagcase s7-console
      (port p (let ((s (s7-port-text p))) (begin (set (extract p out) nil) s)))
      (else y ""))))

(define* s7-interrupt! (subr s7-eff () unit)
  (lambda () (set s7-machine (sum s-done s7-unspecified))))

"`text` run to its end: what it wrote, then its last value (written) or
`Error: …`."
(define* s7-eval-string! (subr s7-eff (string) string)
  (lambda (text)
    (tagcase (s7-start! text "" #f)
      (bad m (string-append "Error: " m))
      (none u (letrec ((go (subr s7-eff () string)
                         (lambda ()
                           (tagcase (s7-continue! 100000)
                             (running u (go))
                             (done v (string-append (s7-take-output!) (if (s7-shown? v) (s7-show v #t) "")))
                             (failed m (string-append (s7-take-output!) "Error: " m))))))
                (go))))))

"The interpreter made ready: the special forms and the procedures written
in FX-26, then the prelude (prelude.fx) run. \"\", or what went wrong."
(define* s7-init! (subr s7-eff () string)
  (lambda ()
    (begin
      (s7-define-specials! s7-special-names)
      (s7-init-prims!)
      (tagcase (s7-start! s7-prelude "prelude.scm" #f)
        (bad m m)
        (none u (letrec ((go (subr s7-eff () string)
                           (lambda ()
                             (tagcase (s7-continue! 1000000)
                               (running u (go))
                               (done v (begin (s7-take-output!) ""))
                               (failed m (string-append "prelude: " m))))))
                  (go)))))))
