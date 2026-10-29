;;; kit/lists.fx: each procedure's answers, and that a caller of them has
;;; no effect but reading kit's bindings (imported, they are the program's
;;; globals): no `spin`; at the heap's `acyclic` and at an arena's place.

(define lists (load-module "../lists.fx"))
(import lists map map2 for-each for-each2 filter remove fold fold-right reduce any every find
        list-index member member? delete list-ref list-tail take concatenate list=? list-sort)

(define ints= (subr (read (globals list=?)) ((listof int acyclic) (listof int acyclic)) bool)
  (lambda (a b) (list=? = a b)))
(define xs (listof int acyclic) (list 3 1 4 1 5 9 2 6))
(define none (listof int acyclic) nil)

"A caller, pure but for kit's bindings: the sum of the squares of the odd
elements."
(define odd-squares (subr (read (globals fold map filter)) ((listof int acyclic)) int)
  (lambda (l) (fold + 0 (the (listof int acyclic) (map (lambda ((x int)) (* x x)) (the (listof int acyclic) (filter (lambda ((x int)) (= (remainder x 2) 1)) l)))))))

(define* check (subr pure () unit)
  (lambda ()
    (begin
      (assert (ints= (map (lambda ((x int)) (+ x 1)) xs) (list 4 2 5 2 6 10 3 7)))
      (assert (ints= (map2 + xs (the (listof int acyclic) (list 10 20 30))) (list 13 21 34)))
      (let ((total (the (ref int @heap) (new 0))))
        (begin (for-each (lambda ((x int)) (set total (+ (get total) x))) xs)
               (for-each2 (lambda ((x int) (y int)) (set total (+ (get total) (* x y)))) xs (the (listof int acyclic) (list 1 1)))
               (assert (= (get total) 35))))
      (assert (ints= (filter (lambda ((x int)) (> x 3)) xs) (list 4 5 9 6)))
      (assert (ints= (remove (lambda ((x int)) (> x 3)) xs) (list 3 1 1 2)))
      (assert (ints= (fold (lambda ((x int) (acc (listof int acyclic))) (the (listof int acyclic) (cons x acc))) none xs)
                     (list 6 2 9 5 1 4 1 3)))
      (assert (ints= (fold-right (lambda ((x int) (acc (listof int acyclic))) (the (listof int acyclic) (cons x acc))) none xs) xs))
      (assert (= (reduce max 0 xs) 9))
      (assert (= (reduce max 0 none) 0))
      (assert (any (lambda ((x int)) (= x 9)) xs))
      (assert (not (any (lambda ((x int)) (= x 7)) xs)))
      (assert (every (lambda ((x int)) (> x 0)) xs))
      (assert (every (lambda ((x int)) (> x 100)) none))
      (assert (tagcase (find (lambda ((x int)) (> x 4)) xs) (some x (= x 5)) (none u #f)))
      (assert (tagcase (find (lambda ((x int)) (> x 40)) xs) (some x #f) (none u #t)))
      (assert (let ((i (list-index (lambda ((x int)) (= x 5)) xs))) (and (not (bool? i)) (= i 4))))
      (assert (bool? (list-index (lambda ((x int)) (= x 7)) xs)))
      (assert (ints= (member 5 xs =) (list 5 9 2 6)))
      (assert (null? (member 7 xs =)))
      (assert (member? 1 xs =))
      (assert (ints= (delete 1 xs =) (list 3 4 5 9 2 6)))
      (assert (= (list-ref xs 0) 3))
      (assert (= (list-ref xs 7) 6))
      (assert (ints= (list-tail xs 6) (list 2 6)))
      (assert (ints= (take xs 3) (list 3 1 4)))
      (assert (ints= (concatenate (the (listof (listof int acyclic) acyclic) (list (list 1 2) nil (list 3)))) (list 1 2 3)))
      (assert (not (list=? = xs (the (listof int acyclic) (list 3 1 4)))))
      (assert (ints= (list-sort < xs) (list 1 1 2 3 4 5 6 9)))
      (assert (ints= (list-sort > xs) (list 9 6 5 4 3 2 1 1)))
      (assert (ints= (list-sort < none) none))
      ;; Stable: pairs sorted by their first, ties kept in order.
      (assert (let ((sorted (the (listof (productof (k int) (v int)) acyclic)
                                 (list-sort (lambda ((a (productof (k int) (v int))) (b (productof (k int) (v int)))) (< (extract a k) (extract b k)))
                                            (the (listof (productof (k int) (v int)) acyclic)
                                                 (list (product (k 2) (v 1)) (product (k 1) (v 2)) (product (k 2) (v 3)) (product (k 1) (v 4))))))))
                (ints= (map (lambda ((p (productof (k int) (v int)))) (extract p v)) sorted) (list 2 4 1 3))))
      (assert (= (odd-squares xs) 117))
      ;; At an arena's place: a list built there, mapped and folded.
      (assert (= 9 (letrena q
                     (let ((l (the (listof int (acyclic q)) (rcons q 2 (the (listof int (acyclic q)) (rcons q 1 nil))))))
                       (fold + 0 (the (listof int acyclic) (map (lambda ((x int)) (* x 3)) l))))))))))

(check)
(write-out "lists: ok\n")
