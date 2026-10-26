;;; core.fx: turns, sends between actors, and a failing turn rolled back.
(define core ((proj (load-module "../core.fx") @ed (io stdout))))
(import core spawn-actor tell tell-latest set-class! display tell! run-turns! actor-state same reply-with on-turn-failure! turns-run
        (type actor msg reply cmd cmds) (effect turn-eff cmd-eff))

(define log (ref (listof string acyclic) @ed) (new nil))
(on-turn-failure! (lambda ((who string) (why string))
                    (set log (cons (string-append who ": " why) (get log)))))

(define counter (actor int) (spawn-actor "counter" 0))
(define total (actor int) (spawn-actor "total" 100))

;; Add n: a message, run in the counter's turn.
(define* add (subr pure (int) (msg int))
  (lambda (n) (lambda ((st int)) (same (+ st n)))))
;; Add n, and tell `total` the same: a send, done only if the turn ends well.
(define* add-and-tell (subr (read (globals total add)) (int) (msg int))
  (lambda (n) (lambda ((st int)) (reply-with (+ st n) (list (tell total (add n)))))))
;; Half-way through, a fault: neither the state nor the send may happen.
(define* bad (subr (read (globals total add)) () (msg int))
  (lambda () (lambda ((st int)) (reply-with (+ st (car (the (listof int acyclic) nil))) (list (tell total (add 1000)))))))

(tell! counter (add 1))
(tell! counter (add-and-tell 10))
(tell! counter (bad))
(tell! counter (add 5))
(run-turns! -1)
;; The failing turn changed nothing and sent nothing: 1 + 10 + 5, and
;; 100 + 10; four turns of the counter's and one of total's.
(define* expect (subr (io stdout) (string bool) unit)
  (lambda (what ok) (if ok #u (begin (write-out (string-append "FAIL " what "\n")) #u))))
(expect "counter" (= (actor-state counter) 16))
(expect "total" (= (actor-state total) 110))
(expect "turns" (= (turns-run) 5))
(expect "failure reported" (and (pair? (get log)) (string=? (car (get log)) "counter: car or cdr of a non-pair")))
;; Classes and keys: three snapshots told to a display actor with one key,
;; and an interactive message after them. The interactive one runs first,
;; and the display actor takes only the last snapshot, in one turn.
(define order (ref (listof string acyclic) @ed) (new nil))
(define shower (actor int) (spawn-actor "shower" 0))
(set-class! shower display)
(define* note (subr pure (string) cmd)
  (lambda (what) (lambda () (set order (cons what (get order))))))
(define* snap (subr pure (int) (msg int))
  (lambda (n) (lambda ((st int)) (reply-with n (list (note (string-append "show " (int->string n))))))))
(define before int (turns-run))
(define poke cmd (tell counter (lambda ((st int)) (reply-with st (list (note "key"))))))
((tell-latest shower "snap" (snap 1)))
((tell-latest shower "snap" (snap 2)))
((tell-latest shower "snap" (snap 3)))
(poke)
(run-turns! -1)
(expect "latest only" (= (actor-state shower) 3))
(expect "one turn each" (= (- (turns-run) before) 2))
(expect "interactive first" (and (pair? (get order)) (string=? (car (get order)) "show 3")
                                 (pair? (cdr (get order))) (string=? (car (cdr (get order))) "key")))
