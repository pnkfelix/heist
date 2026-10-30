;;; lists.fx: kit's list procedures -- R7RS's and SRFI 1's, as FX-26 has
;;; none of its own (`append`, `reverse`, `list-length` and `list` are
;;; Fixpt's).
;;;
;;; A list given is frozen and acyclic, `(listof a (acyclic p))` at any
;;; place `p` (the heap's `acyclic` included), so that walking it ends and
;;; no procedure here says `spin`: each is usable in `pure` code. Reading it
;;; is `(read (acyclic p))`, nothing at the heap. A list made is at a region
;;; `r` the caller chooses: `acyclic` (no procedure here writes `r`, so the
;;; checker allows it) or a writable one. A procedure given is of any effect
;;; `e`, which the call has too.
;;;
;;; What is not found is #f, as in R7RS: an index is a `(union false nat)`,
;;; taken apart by `bool?`; an element, of a type variable, which no union
;;; may hold, is `none` or `(some x)`; `member` gives the tail from the
;;; element found, so nil when there is none.
;;; Equality is given, as R7RS's `member` and `assoc` take it.
;;;
;;; A module file of no state: (define lists (load-module "kit/lists.fx")).

"(f x) of each element, in order."
(define map
  (poly ((p place) (a type) (b type) (e effect) (r region))
    (subr (maxeff e (read (acyclic p)) (alloc r)) ((subr e (a) b) (listof a (acyclic p))) (listof b r)))
  (plambda ((p place) (a type) (b type) (e effect) (r region))
    (lambda (f l)
      (letrec ((go (subr (maxeff e (read (acyclic p)) (alloc r)) ((listof a (acyclic p))) (listof b r))
                 (lambda (l) (if (null? l) nil (let ((y (f (car l)))) (cons y (go (cdr l))))))))
        (go l)))))

"(f x y) of the elements of two lists, pairwise, in order, as long as the
shorter."
(define map2
  (poly ((p place) (q place) (a type) (b type) (c type) (e effect) (r region))
    (subr (maxeff e (read (acyclic p)) (read (acyclic q)) (alloc r))
          ((subr e (a b) c) (listof a (acyclic p)) (listof b (acyclic q))) (listof c r)))
  (plambda ((p place) (q place) (a type) (b type) (c type) (e effect) (r region))
    (lambda (f l m)
      (letrec ((go (subr (maxeff e (read (acyclic p)) (read (acyclic q)) (alloc r)) ((listof a (acyclic p)) (listof b (acyclic q))) (listof c r))
                 (lambda (l m) (if (or (null? l) (null? m)) nil (let ((z (f (car l) (car m)))) (cons z (go (cdr l) (cdr m))))))))
        (go l m)))))

"(f x) of each element, in order, for its effect."
(define for-each
  (poly ((p place) (a type) (e effect))
    (subr (maxeff e (read (acyclic p))) ((subr e (a) unit) (listof a (acyclic p))) unit))
  (plambda ((p place) (a type) (e effect))
    (lambda (f l)
      (letrec ((go (subr (maxeff e (read (acyclic p))) ((listof a (acyclic p))) unit)
                 (lambda (l) (if (null? l) #u (begin (f (car l)) (go (cdr l)))))))
        (go l)))))

"(f x y) of the elements of two lists, pairwise, in order, as long as the
shorter."
(define for-each2
  (poly ((p place) (q place) (a type) (b type) (e effect))
    (subr (maxeff e (read (acyclic p)) (read (acyclic q))) ((subr e (a b) unit) (listof a (acyclic p)) (listof b (acyclic q))) unit))
  (plambda ((p place) (q place) (a type) (b type) (e effect))
    (lambda (f l m)
      (letrec ((go (subr (maxeff e (read (acyclic p)) (read (acyclic q))) ((listof a (acyclic p)) (listof b (acyclic q))) unit)
                 (lambda (l m) (if (or (null? l) (null? m)) #u (begin (f (car l) (car m)) (go (cdr l) (cdr m)))))))
        (go l m)))))

"The elements `keep?` is true of, in order."
(define filter
  (poly ((p place) (a type) (e effect) (r region))
    (subr (maxeff e (read (acyclic p)) (alloc r)) ((subr e (a) bool) (listof a (acyclic p))) (listof a r)))
  (plambda ((p place) (a type) (e effect) (r region))
    (lambda (keep? l)
      (letrec ((go (subr (maxeff e (read (acyclic p)) (alloc r)) ((listof a (acyclic p))) (listof a r))
                 (lambda (l) (cond ((null? l) nil)
                                   ((keep? (car l)) (cons (car l) (go (cdr l))))
                                   (else (go (cdr l)))))))
        (go l)))))

"The elements `drop?` is false of, in order."
(define remove
  (poly ((p place) (a type) (e effect) (r region))
    (subr (maxeff e (read (acyclic p)) (alloc r)) ((subr e (a) bool) (listof a (acyclic p))) (listof a r)))
  (plambda ((p place) (a type) (e effect) (r region))
    (lambda (drop? l)
      (letrec ((go (subr (maxeff e (read (acyclic p)) (alloc r)) ((listof a (acyclic p))) (listof a r))
                 (lambda (l) (cond ((null? l) nil)
                                   ((drop? (car l)) (go (cdr l)))
                                   (else (cons (car l) (go (cdr l))))))))
        (go l)))))

"SRFI 1's fold: (kons x acc) of each element in order, from `knil`."
(define fold
  (poly ((p place) (a type) (s type) (e effect))
    (subr (maxeff e (read (acyclic p))) ((subr e (a s) s) s (listof a (acyclic p))) s))
  (plambda ((p place) (a type) (s type) (e effect))
    (lambda (kons knil l)
      (letrec ((go (subr (maxeff e (read (acyclic p))) ((listof a (acyclic p)) s) s)
                 (lambda (l acc) (if (null? l) acc (go (cdr l) (kons (car l) acc))))))
        (go l knil)))))

"SRFI 1's fold-right: (kons x (fold-right kons knil rest)), so the last
element's first."
(define fold-right
  (poly ((p place) (a type) (s type) (e effect))
    (subr (maxeff e (read (acyclic p))) ((subr e (a s) s) s (listof a (acyclic p))) s))
  (plambda ((p place) (a type) (s type) (e effect))
    (lambda (kons knil l)
      (letrec ((go (subr (maxeff e (read (acyclic p))) ((listof a (acyclic p))) s)
                 (lambda (l) (if (null? l) knil (let ((rest (go (cdr l)))) (kons (car l) rest))))))
        (go l)))))

"SRFI 1's reduce: `ridentity` for the empty list, else the fold of `f`
from the first element over the rest."
(define reduce
  (poly ((p place) (a type) (e effect))
    (subr (maxeff e (read (acyclic p))) ((subr e (a a) a) a (listof a (acyclic p))) a))
  (plambda ((p place) (a type) (e effect))
    (lambda (f ridentity l) (if (null? l) ridentity (fold f (car l) (cdr l))))))

"Whether `pred` is true of some element, trying them in order."
(define any
  (poly ((p place) (a type) (e effect))
    (subr (maxeff e (read (acyclic p))) ((subr e (a) bool) (listof a (acyclic p))) bool))
  (plambda ((p place) (a type) (e effect))
    (lambda (pred l)
      (letrec ((go (subr (maxeff e (read (acyclic p))) ((listof a (acyclic p))) bool)
                 (lambda (l) (if (null? l) #f (if (pred (car l)) #t (go (cdr l)))))))
        (go l)))))

"Whether `pred` is true of every element, trying them in order."
(define every
  (poly ((p place) (a type) (e effect))
    (subr (maxeff e (read (acyclic p))) ((subr e (a) bool) (listof a (acyclic p))) bool))
  (plambda ((p place) (a type) (e effect))
    (lambda (pred l)
      (letrec ((go (subr (maxeff e (read (acyclic p))) ((listof a (acyclic p))) bool)
                 (lambda (l) (if (null? l) #t (if (pred (car l)) (go (cdr l)) #f)))))
        (go l)))))

"The first element `pred` is true of, if one is."
(define find
  (poly ((p place) (a type) (e effect))
    (subr (maxeff e (read (acyclic p))) ((subr e (a) bool) (listof a (acyclic p))) (sumof (none unit) (some a))))
  (plambda ((p place) (a type) (e effect))
    (lambda (pred l)
      (letrec ((go (subr (maxeff e (read (acyclic p))) ((listof a (acyclic p))) (sumof (none unit) (some a)))
                 (lambda (l) (cond ((null? l) (sum none #u))
                                   ((pred (car l)) (sum some (car l)))
                                   (else (go (cdr l)))))))
        (go l)))))

"SRFI 1's filter-map: of each element in order, `f`'s value where it is
`(some y)`; none where it is `none`."
(define filter-map
  (poly ((p place) (a type) (b type) (e effect) (r region))
    (subr (maxeff e (read (acyclic p)) (alloc r)) ((subr e (a) (sumof (none unit) (some b))) (listof a (acyclic p))) (listof b r)))
  (plambda ((p place) (a type) (b type) (e effect) (r region))
    (lambda (f l)
      (letrec ((go (subr (maxeff e (read (acyclic p)) (alloc r)) ((listof a (acyclic p))) (listof b r))
                 (lambda (l) (if (null? l) nil
                                 (tagcase (f (car l))
                                   (some y (cons y (go (cdr l))))
                                   (none u (go (cdr l))))))))
        (go l)))))

"The index of the first element `pred` is true of, or #f."
(define list-index
  (poly ((p place) (a type) (e effect))
    (subr (maxeff e (read (acyclic p))) ((subr e (a) bool) (listof a (acyclic p))) (union false nat)))
  (plambda ((p place) (a type) (e effect))
    (lambda (pred l)
      (letrec ((go (subr (maxeff e (read (acyclic p))) ((listof a (acyclic p)) nat) (union false nat))
                 (lambda (l i) (cond ((null? l) #f) ((pred (car l)) i) (else (go (cdr l) (+ i 1)))))))
        (go l 0)))))

"The tail of `l` from the first element `same?` to `x`, or nil (R7RS's
member, whose #f is nil: a tail found is never empty)."
(define member
  (poly ((p place) (a type) (e effect))
    (subr (maxeff e (read (acyclic p))) (a (listof a (acyclic p)) (subr e (a a) bool)) (listof a (acyclic p))))
  (plambda ((p place) (a type) (e effect))
    (lambda (x l same?)
      (letrec ((go (subr (maxeff e (read (acyclic p))) ((listof a (acyclic p))) (listof a (acyclic p)))
                 (lambda (l) (cond ((null? l) nil) ((same? x (car l)) l) (else (go (cdr l)))))))
        (go l)))))

"Whether an element of `l` is `same?` to `x`."
(define member?
  (poly ((p place) (a type) (e effect))
    (subr (maxeff e (read (acyclic p))) (a (listof a (acyclic p)) (subr e (a a) bool)) bool))
  (plambda ((p place) (a type) (e effect))
    (lambda (x l same?) (not (null? (member x l same?))))))

"The elements of `l` not `same?` to `x`, in order (SRFI 1's delete)."
(define delete
  (poly ((p place) (a type) (e effect) (r region))
    (subr (maxeff e (read (acyclic p)) (alloc r)) (a (listof a (acyclic p)) (subr e (a a) bool)) (listof a r)))
  (plambda ((p place) (a type) (e effect) (r region))
    (lambda (x l same?) (remove (lambda ((y a)) (same? x y)) l))))

"Element `k` of `l` (from 0); an error unless 0 <= k < its length."
(define list-ref
  (poly ((p place) (a type))
    (subr (read (acyclic p)) ((listof a (acyclic p)) int) a))
  (plambda ((p place) (a type))
    (lambda (l k)
      (letrec ((go (subr (read (acyclic p)) ((listof a (acyclic p)) int) a)
                 (lambda (l k) (cond ((null? l) (error "list-ref: index out of range"))
                                     ((<= k 0) (car l))
                                     (else (go (cdr l) (- k 1)))))))
        (if (< k 0) (error "list-ref: index out of range") (go l k))))))

"`l` after its first `k` elements; an error if it has fewer (R7RS's
list-tail)."
(define list-tail
  (poly ((p place) (a type))
    (subr (read (acyclic p)) ((listof a (acyclic p)) int) (listof a (acyclic p))))
  (plambda ((p place) (a type))
    (lambda (l k)
      (letrec ((go (subr (read (acyclic p)) ((listof a (acyclic p)) int) (listof a (acyclic p)))
                 (lambda (l k) (cond ((<= k 0) l)
                                     ((null? l) (error "list-tail: list too short"))
                                     (else (go (cdr l) (- k 1)))))))
        (go l k)))))

"The first `k` elements of `l`; an error if it has fewer (SRFI 1's take)."
(define take
  (poly ((p place) (a type) (r region))
    (subr (maxeff (read (acyclic p)) (alloc r)) ((listof a (acyclic p)) int) (listof a r)))
  (plambda ((p place) (a type) (r region))
    (lambda (l k)
      (letrec ((go (subr (maxeff (read (acyclic p)) (alloc r)) ((listof a (acyclic p)) int) (listof a r))
                 (lambda (l k) (cond ((<= k 0) nil)
                                     ((null? l) (error "take: list too short"))
                                     (else (cons (car l) (go (cdr l) (- k 1))))))))
        (go l k)))))

"The last element of `l`; an error if it is empty (SRFI 1's last)."
(define last
  (poly ((p place) (a type))
    (subr (read (acyclic p)) ((listof a (acyclic p))) a))
  (plambda ((p place) (a type))
    (lambda (l)
      (letrec ((go (subr (read (acyclic p)) ((listof a (acyclic p))) a)
                 (lambda (l) (if (null? (cdr l)) (car l) (go (cdr l))))))
        (if (null? l) (error "last: empty list") (go l))))))

"The elements of `l` but those `same?` to one before them, in order (SRFI
1's delete-duplicates: the first of each kept). Quadratic."
(define delete-duplicates
  (poly ((p place) (a type) (e effect) (r region))
    (subr (maxeff e (read (acyclic p)) (alloc r)) ((listof a (acyclic p)) (subr e (a a) bool)) (listof a r)))
  (plambda ((p place) (a type) (e effect) (r region))
    (lambda (l same?)
      (letrec ((go (subr (maxeff e (read (acyclic p))) ((listof a (acyclic p)) (listof a acyclic)) (listof a acyclic))
                 ;; `seen`, the elements kept, last first.
                 (lambda (l seen) (cond ((null? l) seen)
                                        ((member? (car l) seen same?) (go (cdr l) seen))
                                        (else (go (cdr l) (cons (car l) seen)))))))
        (reverse (go l nil))))))

"Elements `start` to `end` (not included) of array `v`, as a list (R7RS's
vector->list, of an FX-26 array); an error unless 0 <= start <= end <=
its length."
(define vector->list
  (poly ((q region) (a type) (r region))
    (subr (maxeff (read q) (alloc r)) ((arrayof a q) int int) (listof a r)))
  (plambda ((q region) (a type) (r region))
    (lambda (v start end)
      (letrec ((go (subr (maxeff (read q) (alloc r)) (int (listof a r)) (listof a r))
                 ;; From the end, so that the list comes out in order.
                 (lambda (i acc) (if (< i start) acc (go (- i 1) (cons (array-ref v i) acc))))))
        (if (and (<= 0 start) (<= start end) (<= end (array-length v)))
            (go (- end 1) nil)
            (error "vector->list: range out of bounds"))))))

"The lists of `ls`, one after another (SRFI 1's concatenate)."
(define concatenate
  (poly ((p place) (q place) (a type) (r region))
    (subr (maxeff (read (acyclic p)) (read (acyclic q)) (alloc r)) ((listof (listof a (acyclic p)) (acyclic q))) (listof a r)))
  (plambda ((p place) (q place) (a type) (r region))
    (lambda (ls)
      (letrec ((outer (subr (maxeff (read (acyclic p)) (read (acyclic q)) (alloc r)) ((listof (listof a (acyclic p)) (acyclic q))) (listof a r))
                 (lambda (ls) (if (null? ls) nil (inner (car ls) (cdr ls)))))
               (inner (subr (maxeff (read (acyclic p)) (read (acyclic q)) (alloc r)) ((listof a (acyclic p)) (listof (listof a (acyclic p)) (acyclic q))) (listof a r))
                 (lambda (l ls) (if (null? l) (outer ls) (cons (car l) (inner (cdr l) ls))))))
        (outer ls)))))

"Whether two lists are of one length and `same?` element by element (SRFI
1's list=, of two lists)."
(define list=?
  (poly ((p place) (q place) (a type) (e effect))
    (subr (maxeff e (read (acyclic p)) (read (acyclic q))) ((subr e (a a) bool) (listof a (acyclic p)) (listof a (acyclic q))) bool))
  (plambda ((p place) (q place) (a type) (e effect))
    (lambda (same? l m)
      (letrec ((go (subr (maxeff e (read (acyclic p)) (read (acyclic q))) ((listof a (acyclic p)) (listof a (acyclic q))) bool)
                 (lambda (l m) (cond ((null? l) (null? m))
                                     ((null? m) #f)
                                     ((same? (car l) (car m)) (go (cdr l) (cdr m)))
                                     (else #f)))))
        (go l m)))))

"`l` sorted by `less?`, stably (SRFI 132's list-sort): a merge sort. Its
runs are made at `acyclic`, so that merging them is a walk that ends; its
depth is bounded by the length, which is passed down as fuel."
(define list-sort
  (poly ((p place) (a type) (e effect) (r region))
    (subr (maxeff e (read (acyclic p)) (alloc r)) ((subr e (a a) bool) (listof a (acyclic p))) (listof a r)))
  (plambda ((p place) (a type) (e effect) (r region))
    (lambda (less? l)
      (letrec ((merge (subr e ((listof a acyclic) (listof a acyclic)) (listof a acyclic))
                 ;; Stable: from `x` while `y`'s head is not less.
                 (lambda (x y)
                   (cond ((null? x) y)
                         ((null? y) x)
                         ((less? (car y) (car x)) (cons (car y) (merge x (cdr y))))
                         (else (cons (car x) (merge (cdr x) y))))))
               ;; The first `n` elements of `l`, sorted, and `l` after them.
               (sort (subr (maxeff e (read (acyclic p))) ((listof a (acyclic p)) int int)
                           (productof (sorted (listof a acyclic)) (rest (listof a (acyclic p)))))
                 (lambda (l n fuel)
                   (cond ((or (<= n 0) (null? l)) (product (sorted nil) (rest l)))
                         ((or (= n 1) (<= fuel 0)) (product (sorted (cons (car l) nil)) (rest (cdr l))))
                         (else
                          (let* ((h (quotient n 2))
                                 (left (sort l h (- fuel 1)))
                                 (right (sort (extract left rest) (- n h) (- fuel 1))))
                            (product (sorted (merge (extract left sorted) (extract right sorted)))
                                     (rest (extract right rest))))))))
               (copy (subr (alloc r) ((listof a acyclic)) (listof a r))
                 (lambda (l) (if (null? l) nil (cons (car l) (copy (cdr l)))))))
        (let ((n (list-length l)))
          (copy (extract (sort l n n) sorted)))))))
