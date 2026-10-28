;;; notes.fx: what the analysis found, said at places of a file -- at each
;;; use of a variable, what can reach it; at each call's operator, what it
;;; can call, where that is more than one primitive -- each a note `start
;;; end text`, in the order of the file.

(define-type cf-note (productof (start int) (end int) (text string)))
(define-type cf-notes (listof cf-note acyclic))

(define* cf-concat (subr spin (strings string) string)
  (lambda (l sep) (cond ((null? l) "") ((null? (cdr l)) (car l)) (else (string-append (car l) sep (cf-concat (cdr l) sep))))))

"One abstract value, said."
(define* cf-say-val (subr cf-eff (int) string)
  (lambda (v)
    (cond ((= v cf-unknown) "?")
          ((closure-val? v)
           (let ((name (extract (array-ref (get cf-lambda-array) (closure-lambda (quotient v 4))) name)))
             (if (string=? name "") "λ" name)))
          ((site-val? v)
           (let ((info (array-ref (get cf-site-array) (quotient v 4))))
             (cond ((string=? (extract info kind) "sum") (string-append "(" (extract info tag) ")"))
                   (else (extract info kind)))))
          ((kind-val? v) (cf-kind-name (quotient v 4)))
          (else (prim-name v)))))
"Values `s`, said: each once (a lambda made in several contours is one)."
(define* cf-say (subr cf-eff (vals) string)
  (lambda (s)
    (letrec ((go (subr cf-eff (vals strings) strings)
               (lambda (s acc) (if (null? s) (reverse acc)
                                   (let ((t (cf-say-val (car s)))) (go (cdr s) (if (cf-member? t acc) acc (cons t acc))))))))
      (cf-concat (go s nil) " | "))))

(define* note< (subr pure (cf-note cf-note) bool)
  (lambda (a b) (or (< (extract a start) (extract b start))
                    (and (= (extract a start) (extract b start)) (< (extract a end) (extract b end))))))
(define* insert-note (subr spin (cf-note cf-notes) cf-notes)
  (lambda (n l) (if (or (null? l) (note< n (car l))) (cons n l) (cons (car l) (insert-note n (cdr l))))))
(define* sort-notes (subr spin (cf-notes) cf-notes)
  (lambda (l) (letrec ((go (subr spin (cf-notes cf-notes) cf-notes) (lambda (l acc) (if (null? l) acc (go (cdr l) (insert-note (car l) acc))))))
                (go l nil))))

"Variable `v`'s values (in the empty contour), said for an effect: its
name if none reach it."
(define* cf-say-var (subr cf-eff (int string) string)
  (lambda (v name) (let ((s (table-ref (get cf-cells) (var-key v 0) nil))) (if (null? s) name (cf-say s)))))
"The effect lambda `l` declares, said (\"\": none declared)."
(define* cf-say-effect (subr cf-eff (int) string)
  (lambda (l)
    (letrec ((find (subr spin ((listof cf-effect acyclic)) (listof cf-token acyclic))
               (lambda (es) (cond ((null? es) nil) ((= (extract (car es) lambda) l) (extract (car es) tokens)) (else (find (cdr es))))))
             (say (subr cf-eff ((listof cf-token acyclic)) strings)
               (lambda (ts) (if (null? ts) nil
                                (cons (tagcase (car ts) (t-text (s) s) (t-var (v n) (cf-say-var v n))) (say (cdr ts)))))))
      (cf-concat (say (find (get cf-effects))) ""))))
"The effects of the lambdas in callees `s`, each once, said."
(define* cf-say-effects (subr cf-eff (vals) string)
  (lambda (s)
    (letrec ((go (subr cf-eff (vals strings) strings)
               (lambda (s acc) (cond ((null? s) (reverse acc))
                                     ((closure-val? (car s))
                                      (let ((e (cf-say-effect (closure-lambda (quotient (car s) 4)))))
                                        (go (cdr s) (if (or (string=? e "") (cf-member? e acc)) acc (cons e acc)))))
                                     (else (go (cdr s) acc))))))
      (cf-concat (go s nil) " | "))))

"Whether calls with callees `s` are worth a note: one may be a lambda, or
code not known, or there is more than one."
(define* cf-calls-worth? (subr pure (vals) bool)
  (lambda (s) (and (pair? s) (or (pair? (cdr s)) (closure-val? (car s)) (= (car s) cf-unknown)))))

"The notes of file `file` (its number in the world), as the analysis has
them now."
(define* cf-file-notes (subr cf-eff (int) cf-notes)
  (lambda (file)
    (let ((acc (the (ref cf-notes @cf) (new nil)))
          (operators (the (ref (listof cf-span acyclic) @cf) (new nil))))
      (begin
        ;; Calls' operators: a reference there is said by its call's note.
        (letrec ((go (subr cf-eff ((listof call-info acyclic) int) unit)
                   (lambda (cs i)
                     (if (null? cs) #u
                         (begin (if (cf-calls-worth? (table-ref (get cf-callees) i nil))
                                    (set operators (cons (extract (car cs) operator) (get operators))) #u)
                           (go (cdr cs) (- i 1)))))))
          (go (get cf-calls) (- (length (get cf-calls)) 1)))
        ;; References, numbered newest first in `cf-refs`.
        (letrec ((go (subr cf-eff ((listof ref-info acyclic) int) unit)
                   (lambda (rs i)
                     (if (null? rs) #u
                         (let ((sp (extract (car rs) span)) (s (table-ref (get cf-ref-vals) i nil)))
                           (begin
                             (if (and (= (extract sp file) file) (pair? s)
                                      (not (letrec ((at (subr spin ((listof cf-span acyclic)) bool)
                                                          (lambda (l) (and (pair? l) (or (and (= (extract (car l) file) file) (= (extract (car l) start) (extract sp start))
                                                                                                (= (extract (car l) end) (extract sp end)))
                                                                                           (at (cdr l)))))))
                                             (at (get operators)))))
                                 (set acc (cons (product (start (extract sp start)) (end (extract sp end))
                                                         (text (string-append (extract (car rs) name) ": " (cf-say s))))
                                                (get acc)))
                                 #u)
                             (go (cdr rs) (- i 1))))))))
          (go (get cf-refs) (- (length (get cf-refs)) 1)))
        (letrec ((go (subr cf-eff ((listof call-info acyclic) int) unit)
                   (lambda (cs i)
                     (if (null? cs) #u
                         (let ((sp (extract (car cs) operator)) (s (table-ref (get cf-callees) i nil)))
                           (begin
                             (if (and (= (extract sp file) file) (cf-calls-worth? s))
                                 (set acc (cons (product (start (extract sp start)) (end (extract sp end))
                                                         (text (let ((e (cf-say-effects s)))
                                                                 (string-append "calls " (cf-say s) (if (string=? e "") "" (string-append "; effect " e))))))
                                                (get acc)))
                                 #u)
                             (go (cdr cs) (- i 1))))))))
          (go (get cf-calls) (- (length (get cf-calls)) 1)))
        (sort-notes (get acc))))))
