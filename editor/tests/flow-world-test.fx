;;; flow.fx on the editor itself: its files analysed together; every call
;;; known, `(c b)` in in-buffer reaching the commands buffer.fx makes,
;;; and the analysis well under a second.
;;; needs: base.fx buffer.fx resolve.fx syntax.fx flow.fx
(define* text-of2 (subr (maxeff (io fs-read) spin) (string) string)
  (lambda (f) (tagcase (read-file f) (data d (tagcase (utf8->string d) (text s s) (else y ""))) (else y ""))))
(define read-files (->* ((listof string @a)) program-files)
  (lambda (fs) (if (null? fs) nil
                   (let ((s (text-of2 (car fs))))
                     (cons (product (file (car fs)) (forms (eager-state-syntax (eager-feed (eager-feed-string (eager-start-fx26) s) #\newline))))
                           (read-files (cdr fs)))))))
(define expect (->* (string bool) unit)
  (lambda (what ok) (if ok #u (begin (write-out (string-append "FAIL " what "\n")) #u))))
(define world-test (->* () unit)
  (lambda ()
    (let* ((files (read-files (the (listof string @a)
                                   (list "core.fx" "rope.fx" "keys.fx" "screen.fx" "base.fx" "buffer.fx" "resolve.fx"
                                         "syntax.fx" "flow.fx" "index.fx" "view.fx" "frame.fx" "calls.fx" "main.fx"))))
           (t0 (clock))
           (passes (analyze-flow files))
           (ms (i64->int (i64-quotient (i64- (clock) t0) (int->i64 1000000))))
           (cs (flow-calls))
           (frame-text (text-of2 "frame.fx"))
           (in-buffer-call (letrec ((go (->* ((listof call-result acyclic)) (listof call-result acyclic))
                                       (lambda (l) (cond ((null? l) nil)
                                                         ((and (string=? (extract (extract (car l) span) file) "frame.fx")
                                                               (string=? (substring frame-text (extract (extract (car l) span) start)
                                                                                    (extract (extract (car l) span) end))
                                                                         "(c b)"))
                                                          (list (car l)))
                                                         (else (go (cdr l))))))))
                             (go cs))))
      (begin
        (expect "no call may reach code not known"
                (letrec ((none (->* ((listof call-result acyclic)) bool)
                           (lambda (l) (or (null? l) (and (not (extract (car l) unknown)) (none (cdr l)))))))
                  (none cs)))
        (expect "(c b) found" (pair? in-buffer-call))
        (expect "(c b) reaches the commands"
                (and (pair? in-buffer-call) (>= (length (extract (car in-buffer-call) callees)) 28)))
        (expect (string-append "fast (" (int->string ms) " ms)") (< ms 500))))))
(world-test)
