; Output to files (in /tmp: s7st cannot delete them), and the clock.
(call-with-output-file "/tmp/s7st-test-1.txt" (lambda (p) (write '(a "b" 1/2) p) (newline p)))
(with-output-to-file "/tmp/s7st-test-2.txt" (lambda () (display "line one") (newline) (display "line two")))
(define p (open-output-file "/tmp/s7st-test-3.txt"))
(display "never closed" p)
(display (call-with-input-file "/tmp/s7st-test-1.txt" read)) (newline)
(display (with-input-from-file "/tmp/s7st-test-2.txt" (lambda () (list (read-line) (read-line))))) (newline)
(define t0 (current-jiffy))
(display (and (exact-integer? t0) (>= (current-jiffy) t0) (= (jiffies-per-second) 1000000000) (real? (current-second)))) (newline)
(display (guard (e ((file-error? e) "file error")) (open-input-file "no-such-file"))) (newline)
; Not yet written: a port's file is written when it is flushed (or closed,
; or the run ends).
(display (call-with-input-file "/tmp/s7st-test-3.txt" read-line)) (newline)
(flush-output-port p)
(display (call-with-input-file "/tmp/s7st-test-3.txt" read-line)) (newline)
