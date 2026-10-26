;;; screen.fx: rows fitted, and updates that redraw only what changed.
(define sc (load-module "../screen.fx"))
(import sc no-screen make-row face-row blank-row make-screen screen-update (type row rows screen span spans face))

(define* show (subr spin (string) string)
  (lambda (s)
    ;; Escapes made visible: ESC as `^`.
    (list->string (letrec ((go (subr spin (int (listof char acyclic)) (listof char acyclic))
                              (lambda (i acc)
                                (if (< i 0) acc
                                    (go (- i 1) (cons (if (char=? (string-ref s i) (integer->char 27)) #\^ (string-ref s i)) acc))))))
                    (go (- (string-length s) 1) nil)))))

(define r1 row (make-row 10 "hello\tworld, long" (list (product (start 0) (end 5) (face 'keyword)))))
(write-out (string-append "[" (extract r1 text) "]\n"))
(define s1 screen (make-screen 3 10 (list r1 (blank-row 10) (face-row 10 "mode" 'mode-line)) 0 5))
(write-out (string-append "first: " (show (screen-update no-screen s1)) "\n"))
(define s2 screen (make-screen 3 10 (list r1 (make-row 10 "x" nil) (face-row 10 "mode" 'mode-line)) 1 1))
(write-out (string-append "second: " (show (screen-update s1 s2)) "\n"))
(write-out (string-append "same: [" (show (screen-update s2 s2)) "]\n"))
