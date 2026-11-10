;; a datum with no dotted pairs: its one compound is a proper list
(define-type sexp (mu s (oneof int f64 char bool string symbol keyword (listof s acyclic))))
(define-type sexps (listof sexp acyclic))
(define* smap (subr spin ((subr spin (sexp) datum) sexps) (listof datum acyclic))
  (lambda (f l) (if (null? l) nil (cons (f (car l)) (smap f (cdr l))))))
;; the transformer's body, as an ordinary procedure over sexp
(define* rec (subr spin (datum) datum)
  (lambda (form)
    (let ((fields (cdr (cdr form))))            ; a list, statically?
      `(begin (fields ,@fields) (count ,(list-length fields))
              ,@(smap (lambda ((f sexp)) `(with ,(car f))) fields)))))
(define out datum (rec (list 'define-record 'settings (list 'instances 'int) (list 'count 'bool))))
(write-out (typecase out (symbol s "sym") (else e (if (pair? out) "a list" "other"))))
