;;; value.fx: the values of symbolically evaluated programs -- unions,
;;; symbol choices, merging, Scheme truth: shakedown's `(shakedown value)`.
;;;
;;; A value (core.fx's `rf-value`) is a concrete Scheme value; several
;;; values, as `values` returns them (but for one); a term, an Int- or
;;; Bool-sorted symbolic value; a symbol choice, one of several symbols, as
;;; an Int term over their indexes; or a union, a value that is one of
;;; several others, each under a guard (a Bool term). A union's guards are
;;; disjoint, and its members are not unions, nor two of them mergeable.
;;;
;;; Merging (after Rosette's symbolic virtual machine): where two paths of
;;; evaluation join, a value that is a on one and b on the other becomes
;;; (merge g a b). Values of the same shape merge into one -- integers and
;;; booleans into ite terms, symbols into a symbol choice, pairs car by car
;;; and cdr by cdr, several values one by one -- and values of different
;;; shapes into a union. Pairs merge as if immutable, unless the program
;;; can mutate them (it names set-car! or set-cdr!): then they are only put
;;; in unions, as vectors and records are.

(module-parameters ((m-core (load-moduleof "core.fx")) (m-term (load-moduleof "term.fx" m-core))))

(define make-union (subr rf-st (rf-members) rf-value) (lambda (ms) (sum union ms)))
(define union-members (subr rf-st (rf-value) rf-members) (lambda (v) (tagcase v (union ms ms) (else x nil))))
(define member (subr rf-st (rf-value rf-value) rf-member) (lambda (g v) (product (g g) (v v))))

(define procedure-value? (subr rf-st (rf-value) bool)
  (lambda (v) (tagcase v (closure c #t) (prim p #t) (else x #f))))

"Record types, and instances of them."
(define make-record-type (subr rf-st (symbol symbols) rf-rtd)
  (lambda (name fields) (product (name name) (fields fields) (id (new #u)))))
(define make-instance (subr rf-st (rf-rtd rf-slots) rf-value)
  (lambda (rtd fields) (sum inst (product (rtd rtd) (fields fields)))))
(define instance-rtd (subr rf-st (rf-value) rf-rtd)
  (lambda (v) (tagcase v (inst i (extract i rtd)) (else x error-object-type))))
(define instance-fields (subr rf-st (rf-value) rf-slots)
  (lambda (v) (tagcase v (inst i (extract i fields)) (else x no-slots))))
(define same-rtd? (subr rf-st (rf-rtd rf-rtd) bool) (lambda (a b) (eq? (extract a id) (extract b id))))

"Error objects, as (error message irritant …) makes and as the primitives
raise: records of a type the program cannot name. `label` is what a
failure says if it is not caught."
(define error-object-type rf-rtd (product (name 'error-object) (fields (list 'message 'irritants 'label)) (id (new #u))))
(define make-error-value (subr rf-st (rf-value rf-value rf-value) rf-value)
  (lambda (message irritants label)
    (let ((v (the rf-slots (make-array 3 message))))
      (begin (array-set! v 1 irritants) (array-set! v 2 label)
             (make-instance error-object-type v)))))
(define error-value? (subr rf-st (rf-value) bool)
  (lambda (v) (tagcase v (inst i (same-rtd? (extract i rtd) error-object-type)) (else x #f))))
(define error-value-label (subr rf-st (rf-value) rf-value)
  (lambda (v) (array-ref (instance-fields v) 2)))

;;; ------------------------------------------------------------ symbols and their choices
;;;
;;; Symbols have indexes, in the order they are first merged or compared
;;; with a symbol choice. A symbol choice is an Int term whose cases are
;;; indexes; it is never a single index (that is the symbol itself).

(define symbol-indexes (ref (table symbol int @rf) @rf) (new (the (table symbol int @rf) (make-table symbol-hash symbol=?))))
(define indexed-symbols (ref (arrayof symbol @rf) @rf) (new (the (arrayof symbol @rf) (make-array 64 '||))))
(define symbol-count (ref int @rf) (new 0))

(define symbol-index (subr rf-st (symbol) int)
  (lambda (s)
    (let ((known (table-ref (get symbol-indexes) s -1)))
      (if (>= known 0) known
          (let ((i (get symbol-count)))
            (begin
              (if (= i (array-length (get indexed-symbols)))
                  (let ((v (the (arrayof symbol @rf) (make-array (* 2 i) '||))))
                    (letrec ((copy (subr rf-st (int) unit)
                               (lambda (j) (if (>= j i) #u (begin (array-set! v j (array-ref (get indexed-symbols) j)) (copy (+ j 1)))))))
                      (begin (copy 0) (set indexed-symbols v))))
                  #u)
              (array-set! (get indexed-symbols) i s)
              (table-set! (get symbol-indexes) s i)
              (set symbol-count (+ i 1))
              i))))))

(define symbol-like? (subr rf-st (rf-value) bool)
  (lambda (v) (tagcase v (sym s #t) (choice t #t) (else x #f))))

"The index of a symbol (as an integer value), or the term of a choice."
(define symbol-term (subr rf-st (rf-value) rf-value)
  (lambda (v) (tagcase v (sym s (rf-int (symbol-index s))) (choice t (sum term t)) (else x v))))
(define term->symbol (subr rf-st (rf-value) rf-value)
  (lambda (t) (tagcase t (int i (rf-sym (array-ref (get indexed-symbols) i))) (term u (sum choice u)) (else x t))))

"A choice's members as a union's are, (guard . symbol); none if it has too
many to list."
(define symbol-choice-members (subr rf-st (rf-value) (sumof (none unit) (some rf-members)))
  (lambda (v)
    (tagcase (integer-cases (tagcase v (choice t (sum term t)) (else x v)))
      (none u (sum none #u))
      (some cs (sum some (map (lambda ((c a-case)) (member (extract c cond) (rf-sym (array-ref (get indexed-symbols) (extract c value)))))
                              cs))))))

"Whether the program can mutate pairs."
(define pairs-mutable? (ref bool @rf) (new #f))
(define set-pairs-mutable! (subr rf-st (bool) unit) (lambda (b) (set pairs-mutable? b)))

"Forget the symbols' indexes (a new program's check)."
(define reset-symbols! (subr rf-st () unit)
  (lambda ()
    (begin (set symbol-indexes (the (table symbol int @rf) (make-table symbol-hash symbol=?)))
           (set indexed-symbols (the (arrayof symbol @rf) (make-array 64 '||)))
           (set symbol-count 0))))

;;; ------------------------------------------------------------ merging

"The members of v, each with guard g put in front of its own."
(define guarded-members (subr rf-st (rf-value rf-value) rf-members)
  (lambda (g v)
    (tagcase v
      (union ms
        (letrec ((loop (subr rf-st (rf-members rf-members) rf-members)
                   (lambda (ms acc)
                     (if (null? ms) (the rf-members (reverse acc))
                         (let ((g2 (t-and g (extract (car ms) g))))
                           (loop (cdr ms) (if (rf-false? g2) acc (the rf-members (cons (member g2 (extract (car ms) v)) acc)))))))))
          (loop ms nil)))
      (else x (the rf-members (list (member g v)))))))

"Which values merge into one: those of the same shape (see the top)."
(define same-kind? (subr rf-st (rf-value rf-value) bool)
  (lambda (a b)
    (cond ((int-like? a) (int-like? b))
          ((bool-like? a) (bool-like? b))
          ((symbol-like? a) (symbol-like? b))
          (else
           (tagcase a
             (pair p (and (rf-pair? b) (not (get pairs-mutable?))
                          (same-shape? (rf-car a) (rf-car b)) (same-shape? (rf-cdr a) (rf-cdr b))))
             (multiple vs (tagcase b (multiple ws (same-kind-vals? vs ws)) (else x #f)))
             (str s (tagcase b (str t (string=? s t)) (else x #f)))
             (else x (rf-eqv? a b)))))))
"As same-kind? of two lists, which several values are in shakedown."
(define same-kind-vals? (subr rf-st (rf-vals rf-vals) bool)
  (lambda (a b)
    (cond ((null? a) (null? b))
          ((null? b) #f)
          (else (and (not (get pairs-mutable?)) (same-shape? (car a) (car b)) (same-shape-vals? (cdr a) (cdr b)))))))
(define same-shape-vals? (subr rf-st (rf-vals rf-vals) bool)
  (lambda (a b) (same-kind-vals? a b)))

(define same-shape? (subr rf-st (rf-value rf-value) bool)
  (lambda (a b)
    (or (rf-union? a) (rf-union? b)
        (if (symbol-like? a)
            (and (symbol-like? b) (rf-eqv? (symbol-term a) (symbol-term b)))
            (same-kind? a b)))))

"if g then a else b."
(define merge (subr rf-st (rf-value rf-value rf-value) rf-value)
  (lambda (g a b)
    (cond ((rf-true? g) a)
          ((rf-false? g) b)
          ((rf-eqv? a b) a)
          ((or (rf-union? a) (rf-union? b))
           (let* ((as (guarded-members g a))
                  (bs (guarded-members (t-not g) b)))
             (merge-members (the rf-members (append as bs)))))
          ((same-kind? a b) (merge-same g a b))
          (else (let* ((m1 (member g a)) (ng (t-not g))) (make-union (the rf-members (list m1 (member ng b)))))))))

(define merge-same (subr rf-st (rf-value rf-value rf-value) rf-value)
  (lambda (g a b)
    (cond ((rf-eqv? a b) a)
          ((or (int-like? a) (bool-like? a)) (t-ite g a b))
          ((symbol-like? a) (term->symbol (t-ite g (symbol-term a) (symbol-term b))))
          (else
           (tagcase a
             (pair p
               ;; shakedown's (let ((x …car…) (y …cdr…)) …): the cdr first.
               (let* ((y (merge g (rf-cdr a) (rf-cdr b)))
                      (x (merge g (rf-car a) (rf-car b))))
                 (if (and (rf-eqv? x (rf-car a)) (rf-eqv? y (rf-cdr a))) a (rf-cons x y))))
             (multiple vs
               (tagcase b
                 (multiple ws (let ((r (merge-vals g vs ws))) (if (eq? r vs) a (sum multiple r))))
                 (else x a)))
             (else x a))))))
"Two lists merged as shakedown merges them as pairs: each tail before its
head; the list itself if nothing changed."
(define merge-vals (subr rf-st (rf-value rf-vals rf-vals) rf-vals)
  (lambda (g a b)
    (if (or (null? a) (null? b)) a
        (let* ((y (merge-vals g (cdr a) (cdr b)))
               (x (merge g (car a) (car b))))
          (if (and (rf-eqv? x (car a)) (eq? y (cdr a))) a (the rf-vals (cons x y)))))))

"One value from (guard . value)s with disjoint guards: members of the same
kind are merged, and if more than one kind is left they make a union."
(define merge-members (subr rf-st (rf-members) rf-value)
  (lambda (members)
    (letrec ((loop (subr rf-st (rf-members rf-members) rf-value)
               (lambda (ms groups)
                 (if (null? ms)
                     (let ((groups (the rf-members (reverse groups))))
                       (cond ((null? groups) rf-unspecified)
                             ((null? (cdr groups)) (extract (car groups) v))
                             (else (make-union groups))))
                     (let* ((m (car ms)) (g (extract m g)) (v (extract m v)))
                       (cond ((rf-false? g) (loop (cdr ms) groups))
                             ((rf-union? v) (loop (the rf-members (append (guarded-members g v) (cdr ms))) groups))
                             (else
                              (letrec ((find (subr rf-st (rf-members rf-members) rf-value)
                                         (lambda (gs before)
                                           (cond ((null? gs) (loop (cdr ms) (the rf-members (cons m groups))))
                                                 ((same-kind? (extract (car gs) v) v)
                                                  (let* ((g1 (extract (car gs) g))
                                                         (gor (t-or g1 g))
                                                         (mv (merge-same g1 (extract (car gs) v) v)))
                                                    (loop (cdr ms) (the rf-members (append (reverse before) (cons (member gor mv) (cdr gs)))))))
                                                 (else (find (cdr gs) (the rf-members (cons (car gs) before))))))))
                                (find groups nil)))))))))
      (loop members nil))))

"When v counts as true, as a Bool term or boolean: Scheme's rule, that
everything but #f is true."
(define truth (subr rf-st (rf-value) rf-value)
  (lambda (v)
    (cond ((rf-false? v) rf-false)
          ((bool-term? v) v)
          (else
           (tagcase v
             (union ms (t-or* (map (lambda ((m rf-member)) (t-and (extract m g) (truth (extract m v)))) ms)))
             (else x rf-true))))))
