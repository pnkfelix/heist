;; (nestof L): a proper list whose elements are leaves (L) or nests
(define-type (nestof (l type)) (mu n (listof (oneof l n) acyclic)))
(define-type atom (oneof int f64 char bool string symbol keyword))
(define-type form (nestof atom))
(define* fmap (subr spin ((subr spin ((oneof atom form)) datum) form) (listof datum acyclic))
  (lambda (f l) (if (null? l) nil (cons (f (car l)) (fmap f (cdr l))))))
;; the transformer's body, form a nest: no narrowing to take it apart
(define* rec (subr spin (form) datum)
  (lambda (form)
    (let ((fields (cdr (cdr form))))
      `(begin (fields ,@fields) (count ,(list-length fields))
              ,@(fmap (lambda ((f (oneof atom form))) (if (pair? f) `(with ,(car f)) f)) fields)))))
;; subtyping: a flat list is a nest, a nest is a datum
(define flat (listof symbol acyclic) (list 'a 'b))
(define as-nest form flat)
(define as-datum datum as-nest)
(define out datum (rec (list 'define-record 'settings (list 'instances 'int) (list 'count 'bool))))
(write-out (if (pair? out) "ok" "no"))
