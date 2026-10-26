;;; syntax.fx's analysis of a small FX-26 text. Run after base.fx,
;;; needs: base.fx buffer.fx syntax.fx
;;; buffer.fx and syntax.fx (tests/run.sh does).
(define sample string
  "; a comment\n(define* f (subr pure (int) int) (lambda (x) \"s;\" x))\n(define-type t int)\n(f")
(define* show-face (subr spin (string text-faces) string)
  (lambda (s fs)
    (if (null? fs) ""
        (let ((x (car fs)))
          (string-append (symbol->string (extract x face)) ":" (substring s (extract x start) (extract x end)) " "
                         (show-face s (cdr fs)))))))
(define* show-defs (subr spin (definitions) string)
  (lambda (ds) (if (null? ds) "" (string-append (extract (car ds) name) " " (show-defs (cdr ds))))))
(define* expect (subr (io stdout) (string string string) unit)
  (lambda (what want got)
    (if (string=? want got) #u (begin (write-out (string-append "FAIL " what ": want [" want "] got [" got "]\n")) #u))))
(define* test (subr (maxeff reader-eff spin (io stdout) (read @globals)) () unit)
  (lambda ()
    (let ((a (analyze sample 7)))
      (begin
        (expect "faces"
                "comment:; a comment keyword:define* function-name:f type:subr keyword:lambda string:\"s;\" keyword:define-type function-name:t error:( "
                (show-face sample (extract a faces)))
        (expect "definitions" "f t " (show-defs (extract a definitions)))
        (expect "problem" "a form is not closed" (extract a problem))))))
(test)
