;;; prelude.fx: procedures of checked programs written in Scheme, evaluated
;;; symbolically like the program's own: shakedown's `(shakedown prelude)`
;;; -- those that call procedures they are given, or compare with eqv? and
;;; equal?, which may give symbolic answers. The text is shakedown's, read
;;; as data (no places noted, as shakedown's are quoted data).

(module-parameters ((m-core (load-moduleof "core.fx")) (m-numbers (load-moduleof "numbers.fx" m-core))
                    (m-reader (load-moduleof "reader.fx" m-core m-numbers))))

(hide (define kit-lists (load-module "../kit/lists.fx"))
      (import kit-lists map for-each filter))

(define prelude-text string
  "(define (map f l . ls)
          (if (null? ls)
              (let map1 ((l l))
                (if (null? l) '() (cons (f (car l)) (map1 (cdr l)))))
              (let mapn ((ls (cons l ls)))
                (if (memq '() ls)
                    '()
                    (cons (apply f (map car ls)) (mapn (map cdr ls)))))))

        (define (for-each f l . ls)
          (if (null? ls)
              (let loop ((l l))
                (if (null? l) (if #f #f) (begin (f (car l)) (loop (cdr l)))))
              (let loop ((ls (cons l ls)))
                (if (memq '() ls)
                    (if #f #f)
                    (begin (apply f (map car ls)) (loop (map cdr ls)))))))

        (define (filter keep? l)
          (cond ((null? l) '())
                ((keep? (car l)) (cons (car l) (filter keep? (cdr l))))
                (else (filter keep? (cdr l)))))

        (define (remove drop? l)
          (filter (lambda (x) (not (drop? x))) l))

        (define (fold-left f acc l)
          (if (null? l) acc (fold-left f (f acc (car l)) (cdr l))))

        (define (fold-right f acc l)
          (if (null? l) acc (f (car l) (fold-right f acc (cdr l)))))

        (define (fold f acc l)
          (if (null? l) acc (fold f (f (car l) acc) (cdr l))))

        (define (reduce f default l)
          (if (null? l) default (fold f (car l) (cdr l))))

        (define (any pred l)
          (and (pair? l) (or (pred (car l)) (any pred (cdr l)))))

        (define (every pred l)
          (or (null? l)
              (if (null? (cdr l))
                  (pred (car l))
                  (and (pred (car l)) (every pred (cdr l))))))

        (define (member x l . compare)
          (let ((same? (if (pair? compare) (car compare) equal?)))
            (let loop ((l l))
              (cond ((null? l) #f)
                    ((same? x (car l)) l)
                    (else (loop (cdr l)))))))
        (define (memv x l) (member x l eqv?))
        (define (memq x l) (member x l eq?))

        (define (assoc x l . compare)
          (let ((same? (if (pair? compare) (car compare) equal?)))
            (let loop ((l l))
              (cond ((null? l) #f)
                    ((same? x (car (car l))) (car l))
                    (else (loop (cdr l)))))))
        (define (assv x l) (assoc x l eqv?))
        (define (assq x l) (assoc x l eq?))

        (define (delete x l . compare)
          (let ((same? (if (pair? compare) (car compare) equal?)))
            (remove (lambda (y) (same? x y)) l)))

        (define (last-pair l)
          (if (pair? (cdr l)) (last-pair (cdr l)) l))

        (define (list-index pred l)
          (let loop ((l l) (i 0))
            (cond ((null? l) #f)
                  ((pred (car l)) i)
                  (else (loop (cdr l) (+ i 1))))))

        (define (iota n . start)
          (let ((s (if (pair? start) (car start) 0)))
            (let loop ((i (- n 1)) (acc '()))
              (if (< i 0) acc (loop (- i 1) (cons (+ s i) acc))))))

        (define (make-list n . fill)
          (let ((x (if (pair? fill) (car fill) #f)))
            (let loop ((i 0) (acc '()))
              (if (< i n) (loop (+ i 1) (cons x acc)) acc))))

        (define (vector-map f v) (list->vector (map f (vector->list v))))
        (define (vector-for-each f v) (for-each f (vector->list v)))

        ;; (rnrs sorting): merge sorts, stable, calling less? as shakedown
        ;; evaluates them.
        (define (list-sort less? l)
          (define (merge a b)
            (cond ((null? a) b)
                  ((null? b) a)
                  ((less? (car b) (car a)) (cons (car b) (merge a (cdr b))))
                  (else (cons (car a) (merge (cdr a) b)))))
          (let sort ((l l) (n (length l)))
            (if (< n 2)
                (if (= n 0) '() (list (car l)))
                (let ((half (quotient n 2)))
                  (merge (sort l half) (sort (list-tail l half) (- n half)))))))
        (define (vector-sort less? v) (list->vector (list-sort less? (vector->list v))))
        (define (vector-sort! less? v)
          (let loop ((i 0) (l (list-sort less? (vector->list v))))
            (unless (null? l)
              (vector-set! v i (car l))
              (loop (+ i 1) (cdr l)))))")

(define prelude-cache (ref (sumof (none unit) (some rf-vals)) @rf) (new (sum none #u)))
"The prelude's forms (read once: the same forms each time)."
(define prelude-forms (subr rf-eff () rf-vals)
  (lambda ()
    (tagcase (get prelude-cache)
      (some fs fs)
      (none u (let ((fs (read-text* prelude-text "prelude" #f #f)))
                (begin (set prelude-cache (sum some fs)) fs))))))
