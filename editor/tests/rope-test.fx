;;; rope.fx against plain strings: each edit done to both, compared.
(define r (load-module "../rope.fx"))
(import r empty-rope string->rope rope->string rope-length rope-insert rope-delete
        rope-ref rope-substring rope-line-start rope-line-end rope-line-of rope-line-count
        rope-height (type rope))

(define* check (subr (io stdout) (string bool) unit)
  (lambda (what ok) (if ok #u (begin (write-out (string-append "FAIL " what "\n")) #u))))

;; A long text of numbered lines.
(define* lines (subr spin (int (listof string acyclic)) (listof string acyclic))
  (lambda (n acc) (if (= n 0) acc (lines (- n 1) (cons (string-append "line " (int->string n) "\n") acc)))))
(define text string (apply string-append (lines 2000 nil)))
(define t0 rope (string->rope text))
(check "round trip" (string=? (rope->string t0) text))
(check "length" (= (rope-length t0) (string-length text)))

;; Many inserts and deletes at scattered places, mirrored on a string.
(define* step (subr spin (int rope string) (productof (r rope) (s string)))
  (lambda (i r s)
    (if (= i 0)
        (product (r r) (s s))
        (let* ((pos (remainder (* i 7919) (+ 1 (string-length s))))
               (r2 (if (= (remainder i 3) 0)
                       (rope-delete r pos (min (string-length s) (+ pos 5)))
                       (rope-insert r pos "ab\ncd")))
               (s2 (if (= (remainder i 3) 0)
                       (string-append (substring s 0 pos) (substring s (min (string-length s) (+ pos 5)) (string-length s)))
                       (string-append (substring s 0 pos) "ab\ncd" (substring s pos (string-length s))))))
          (step (- i 1) r2 s2)))))
(define after (step 3000 t0 text))
(define r1 rope (extract after r))
(define s1 string (extract after s))
(check "after edits" (string=? (rope->string r1) s1))
(check "ref" (char=? (rope-ref r1 1234) (string-ref s1 1234)))
(check "substring" (string=? (rope-substring r1 100 4000) (substring s1 100 4000)))
(check "balanced" (< (rope-height r1) 30))

;; Lines: line 5's start is just after the 5th newline.
(define* nth-newline (subr spin (string int int) int)
  (lambda (s i n) (if (char=? (string-ref s i) #\newline) (if (= n 1) (+ i 1) (nth-newline s (+ i 1) (- n 1))) (nth-newline s (+ i 1) n))))
(check "line-start" (= (rope-line-start r1 5) (nth-newline s1 0 5)))
(check "line-of" (= (rope-line-of r1 (rope-line-start r1 77)) 77))
(check "line-end" (= (+ 1 (rope-line-end r1 77)) (rope-line-start r1 78)))
(check "empty" (string=? (rope->string (rope-insert empty-rope 0 "x")) "x"))
(write-out (string-append "rope ok, height " (int->string (rope-height r1)) ", lines " (int->string (rope-line-count r1)) "\n"))
