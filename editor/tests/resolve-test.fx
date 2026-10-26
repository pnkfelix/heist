;;; resolve.fx: uses resolved to binders, scope by scope.
;;; needs: base.fx buffer.fx resolve.fx syntax.fx
(define sample string
  "(define x 1)\n(define* f (subr pure (int) int)\n  (lambda (x) (let ((y x)) (+ y x))))\n(define* g (subr pure () int) (lambda () (letrec ((h (subr pure () int) (lambda () (h)))) x)))\n(tagcase v (some (a b) a) (else z 'x))\n(foo x)")
(define* syntax-of (subr (maxeff reader-eff spin) (string) (listof syn acyclic))
  (lambda (s) (eager-state-syntax (eager-feed (eager-feed-string (eager-start-fx26) s) #\newline))))
"Each reference as `name@start->binder` (binder -1 if none)."
(define* show-refs (subr spin (string references) string)
  (lambda (s rs)
    (if (null? rs) ""
        (let ((r (car rs)))
          (string-append (substring s (extract r start) (extract r end)) "@" (int->string (extract r start))
                         "->" (int->string (extract r binder-start)) " " (show-refs s (cdr rs)))))))
(define want string
  (string-append
   ;; f: its parameter's type names are from elsewhere; x is the parameter
   ;; (57), not the global (8); y is the let's.
   "subr@25->-1 pure@30->-1 int@36->-1 int@41->-1 x@69->57 +@74->-1 y@76->67 x@78->57 "
   ;; g: h in its own letrec; x the global, there being no parameter.
   "subr@96->-1 pure@101->-1 int@109->-1 subr@138->-1 pure@143->-1 int@151->-1 h@168->135 x@174->8 "
   ;; tagcase: the arm's a; neither the tag, else's name, nor 'x is a use.
   "v@188->-1 a@202->197 "
   "foo@219->-1 x@223->8 "))
(define* resolve-test (subr (maxeff reader-eff spin (io stdout) (read @globals)) () unit)
  (lambda ()
    (let ((got (show-refs sample (resolve-text (syntax-of sample)))))
      (if (string=? got want) #u (begin (write-out (string-append "FAIL got " got "\n")) #u)))))
(resolve-test)
