;; => read error: `...` follows the part it repeats, last in a list
;; R7RS 4.3.2 allows P ... Pk (a tail after the ellipsis).
(define-syntax string-case
  (syntax-rules (else)
    ((_ s (k e) ... (else d)) (let ((v s)) (cond ((string=? v k) e) ... (else d))))))
(write-out (string-case "b" ("a" "A") ("b" "B") (else "?")))
