;; Option 2 through a session: forms as a rewriter would write them, each a
;; procedure of a region and a log in it. A command's body is user code, so
;; the `poly` is within its own type: refused (a substitution into the nested
;; copy) until Fixpt's d144eeb5. Runs at dd369934, `log` exported to staged code.
(define-effect turn-eff (maxeff spin nondet (read @globals) (read @ed) (alloc @ed)))
(define-type (log (r region)) (ref (listof request acyclic) r))
(define-type user-code
  (productof (code (poly ((r region)) (subr (maxeff turn-eff (read r) (write r) (alloc r)) ((log r)) unit)))))
(define-type request (sumof (insert string) (message string) (command (productof (name string) (body user-code)))))
(define-type requests (listof request acyclic))
(define-type api-type
  (moduleof (desc log (dlambda ((r region)) (ref (listof request acyclic) r)))
            (val insert (poly ((r region)) (subr (maxeff (read r) (write r)) ((log r) string) unit)))
            (val message (poly ((r region)) (subr (maxeff (read r) (write r)) ((log r) string) unit)))
            (val define-command (poly ((r region)) (subr (maxeff (read r) (write r)) ((log r) string user-code) unit)))))
(define api api-type
  (module
    (define-type (log (r region)) (ref (listof request acyclic) r))
    (define insert (poly ((r region)) (subr (maxeff (read r) (write r)) ((log r) string) unit))
      (plambda ((r region)) (lambda ((l (log r)) (s string)) (set l (cons (sum insert s) (get l))))))
    (define message (poly ((r region)) (subr (maxeff (read r) (write r)) ((log r) string) unit))
      (plambda ((r region)) (lambda ((l (log r)) (s string)) (set l (cons (sum message s) (get l))))))
    (define define-command (poly ((r region)) (subr (maxeff (read r) (write r)) ((log r) string user-code) unit))
      (plambda ((r region)) (lambda ((l (log r)) (n string) (b user-code)) (set l (cons (sum command (product (name n) (body b))) (get l))))))))
(define s (sessionof api-type @ed) (make-session api))
(define-effect sess (maxeff stage spin turn-eff (read @ed) (write @ed) (alloc @ed)))
(define commands (ref (listof user-code acyclic) @ed) (new nil))
(define run (subr turn-eff (user-code) requests)
  (lambda (u) (letregion r (let ((l (the (log r) (new nil)))) (begin ((proj (extract u code) r) l) (reverse (get l)))))))
(define shown (subr (maxeff (read @globals) spin) (requests) string)
  (lambda (rs) (if (null? rs) ""
                   (string-append (tagcase (car rs) (insert s (string-append "insert " s)) (message s (string-append "message " s))
                                    (command c (string-append "command " (extract c name))))
                                  "; " (shown (cdr rs))))))
;; A form: checked as user code, run in an `attempt` (a turn), its requests
;; shown; a command's body kept.
(define form (subr (maxeff sess (read @globals)) (datum) string)
  (lambda (code)
    (session-check s turn-eff user-code code
      (c (tagcase c
           (expression p
             (let ((u (p)))
               (tagcase (attempt (the (sumof (ok requests) (lost string)) (sum ok (run u)))
                                 (lambda ((why string)) (the (sumof (ok requests) (lost string)) (sum lost why))))
                 (ok rs (begin (letrec ((keep (subr (maxeff (read @ed) (write @ed) (read @globals) spin) (requests) unit)
                                          (lambda (rs) (if (null? rs) #u
                                                           (begin (tagcase (car rs) (command c (set commands (cons (extract c body) (get commands)))) (insert x #u) (message x #u))
                                                                  (keep (cdr rs)))))))
                                 (keep rs))
                               (shown rs)))
                 (lost m (string-append "fault: " m)))))
           (definition d (tagcase (session-commit! s d (sum rerun #u))
                           (defined n (string-append "defined " n))
                           (failed why (string-append "not defined: " (extract why message)))))))
      (why (string-append "refused: " (extract why message))))))
(define line (subr (io stdout) (string) unit) (lambda (x) (begin (write-out (string-append x "\n")) #u)))
(define main (subr (maxeff sess (io stdout) (read @globals)) () int)
  (lambda ()
    (begin
      ;; (begin (insert "a") (message "b"))
      (line (form '(product (code (plambda ((r region)) (lambda ((%log (log r))) (begin ((proj insert r) %log "a") ((proj message r) %log "b"))))))))
      ;; (define greet (lambda ((who string)) (message (string-append "hi " who))))
      (line (form '(define greet (product (code (plambda ((r region)) (lambda ((%log (log r)) (who string)) ((proj message r) %log (string-append "hi " who)))))))))
      ;; (define-command "hello" (lambda () (begin (insert "x") (greet "you"))))
      (line (form '(product (code (plambda ((r region)) (lambda ((%log (log r)))
                     ((proj define-command r) %log "hello"
                       (product (code (plambda ((r2 region)) (lambda ((%log (log r2)))
                         (begin ((proj insert r2) %log "x") ((proj (extract greet code) r2) %log "you")))))))))))))
      ;; the command run, as M-x would
      (line (shown (run (car (get commands)))))
      ;; (begin (insert "y") (car nil)): a fault, nothing done
      (line (form '(product (code (plambda ((r region)) (lambda ((%log (log r)))
                     (begin ((proj insert r) %log "y") (car (the (listof int acyclic) nil)) #u)))))))
      0)))
