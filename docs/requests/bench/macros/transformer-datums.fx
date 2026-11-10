;; Works (=> 7), but only with dmap and sym written out: the input is a
;; `datum`, and
;;   ,@fields             a (listof datum acyclic) is expected, this is a datum
;;   (map f fields)       likewise
;;   (symbol->string (car f))   argument 1 is a datum, where a symbol is expected
;; each refused at 3:5, the transformer, not where the call is.
(define-syntax define-record
  (er-macro-transformer
    (lambda (form rename compare)
      (letrec ((dmap (subr spin ((subr spin (datum) datum) datum) (listof datum acyclic))
                 (lambda (f l) (if (pair? l) (cons (f (car l)) (dmap f (cdr l))) nil)))
               (sym (subr spin (datum) symbol) (lambda (d) (typecase d (symbol s s) (else e 'bad)))))
        (let* ((name (car (cdr form))) (fields (cdr (cdr form))))
          `(begin
             (define-type ,name (productof ,@(dmap (lambda ((f datum)) f) fields)))
             ,@(dmap (lambda ((f datum))
                       (let ((fname (car f)))
                         `(define ,(string->symbol (string-append "with-" (symbol->string (sym fname))))
                            (subr pure (,name ,(car (cdr f))) ,name)
                            (lambda (s v)
                              (product ,@(dmap (lambda ((g datum))
                                                 (let ((k (symbol->keyword (sym (car g)))))
                                                   (if (eq? (car g) fname) `(,k v) `(,k (extract s ,k)))))
                                               fields))))))
                     fields)))))))
(define-record settings (instances int) (count bool))
(define s0 settings (product (instances 0) (count #f)))
(write-out (int->string (extract (with-instances s0 7) instances)))
