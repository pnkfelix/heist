;;; Reading from checkpoints gives what reading the whole text gives: the
;;; needs: base.fx buffer.fx resolve.fx syntax.fx
;;; args: ../frame.fx
;;; text read, an edit made at several places, each read both ways and
;;; compared. Run after base.fx, buffer.fx and syntax.fx, given a file:
;;;   fixpt run base.fx buffer.fx syntax.fx tests/syntax-incremental-test.fx -- FILE
(define* same-faces? (subr spin (text-faces text-faces) bool)
  (lambda (a b)
    (cond ((null? a) (null? b))
          ((null? b) #f)
          (else (and (= (extract (car a) start) (extract (car b) start))
                     (= (extract (car a) end) (extract (car b) end))
                     (symbol=? (extract (car a) face) (extract (car b) face))
                     (same-faces? (cdr a) (cdr b)))))))
(define* same-definitions? (subr spin (definitions definitions) bool)
  (lambda (a b)
    (cond ((null? a) (null? b))
          ((null? b) #f)
          (else (and (string=? (extract (car a) name) (extract (car b) name))
                     (= (extract (car a) start) (extract (car b) start))
                     (same-definitions? (cdr a) (cdr b)))))))
(define* text-of (subr (maxeff (io fs-read) spin) (string) string)
  (lambda (f) (tagcase (read-file f) (data d (tagcase (utf8->string d) (text s s) (else y ""))) (else y ""))))
(define* test-main (subr (maxeff reader-eff spin (io stdout) (io clock) (io fs-read) (io args) (alloc @a) (read @globals)) () int)
  (lambda ()
    (let* ((s (text-of (car (the (listof string @a) (args)))))
           (n (string-length s))
           (first (analyze-incremental s 1 no-memory))
           (us (lambda ((t i64)) (i64->int (i64-quotient (i64- (clock) t) (int->i64 1000))))))
      (letrec ((try (subr (maxeff reader-eff spin (io stdout) (io clock) (read @globals)) (int string) unit)
                 (lambda (at edit)
                   (let* ((s2 (string-append (substring s 0 at) edit (substring s at n)))
                          (t0 (clock))
                          (inc (analyze-incremental s2 2 (extract first memory)))
                          (t-inc (us t0))
                          (t1 (clock))
                          (whole (analyze s2 2))
                          (t-whole (us t1))
                          (a (extract inc annotation)))
                     (begin
                       (if (and (same-faces? (extract a faces) (extract whole faces))
                                (same-definitions? (extract a definitions) (extract whole definitions))
                                (string=? (extract a problem) (extract whole problem))
                                (= (extract a problem-at) (extract whole problem-at)))
                           #u
                           (begin (write-out (string-append "FAIL at " (int->string at) " edit [" edit "]\n")) #u))
                       (write-out (string-append "edit at " (int->string (quotient (* 100 at) n)) "%: "
                                                 (int->string t-inc) " us from checkpoints, "
                                                 (int->string t-whole) " us whole\n"))
                       #u)))))
        (begin
          (try (quotient n 10) "x")
          (try (quotient n 2) "(")
          (try (quotient (* 9 n) 10) "\"")
          (try (- n 2) ")")
          0)))))
(define main test-main)
