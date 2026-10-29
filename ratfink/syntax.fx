;;; syntax.fx: syntax-rules, with renaming for hygiene: shakedown's
;;; `(shakedown syntax)`.
;;;
;;; Expanding a macro use puts each symbol that the template brings in (one
;;; that is not a pattern variable) through renaming: it becomes a fresh
;;; symbol, an alias, which remembers the symbol it stands for and the
;;; environments the macro was defined in. An alias that the expansion
;;; binds is a new variable, so it cannot capture the user's variables of
;;; the same name; one it does not bind means what its symbol means where
;;; the macro was defined. The compiler (eval.fx) does that lookup; here
;;; aliases are made and the forms transcribed. strip turns aliases back
;;; into the symbols they stand for, for quoted data and for showing forms.

(module-parameters ((m-core (load-moduleof "core.fx")) (m-print (load-moduleof "print.fx" m-core))))

;;; ------------------------------------------------------------ aliases

(define-type alias-info (productof (sym symbol) (cenv rf-cenv) (genv rf-genv)))
(define aliases (ref (table symbol alias-info @rf) @rf)
  (new (the (table symbol alias-info @rf) (make-table symbol-hash symbol=?))))
(define alias-counter (ref int @rf) (new 0))

"Forget the aliases (a new program's check)."
(define reset-aliases! (subr rf-st () unit)
  (lambda () (begin (set aliases (the (table symbol alias-info @rf) (make-table symbol-hash symbol=?)))
                    (set alias-counter 0))))

(define make-alias (subr rf-st (symbol rf-cenv rf-genv) symbol)
  (lambda (sym cenv genv)
    (begin
      (set alias-counter (+ (get alias-counter) 1))
      (let ((a (string->symbol (string-append (symbol->string (strip-name sym)) "~" (int->string (get alias-counter))))))
        (begin (table-set! (get aliases) a (product (sym sym) (cenv cenv) (genv genv)))
               a)))))

(define alias? (subr rf-st (symbol) bool) (lambda (x) (table-has? (get aliases) x)))
(define alias-info-of (subr rf-st (symbol) alias-info)
  (lambda (a) (table-ref (get aliases) a (product (sym a) (cenv nil) (genv no-genv)))))
(define no-genv rf-genv
  (product (cells (the (table symbol rf-slots @rf) (make-table symbol-hash symbol=?)))
           (macros (the (table symbol rf-maybe-macro @rf) (make-table symbol-hash symbol=?)))
           (parent (sum none #u))))
(define alias-symbol (subr rf-st (symbol) symbol) (lambda (a) (extract (alias-info-of a) sym)))
(define alias-cenv (subr rf-st (symbol) rf-cenv) (lambda (a) (extract (alias-info-of a) cenv)))
(define alias-genv (subr rf-st (symbol) rf-genv) (lambda (a) (extract (alias-info-of a) genv)))
(define value-alias? (subr rf-st (rf-value) bool) (lambda (v) (tagcase v (sym s (alias? s)) (else x #f))))

"The symbol an alias stands for, at the end of the chain (a macro can make
a macro)."
(define strip-name (subr rf-st (symbol) symbol)
  (lambda (x) (if (alias? x) (strip-name (alias-symbol x)) x)))
"strip-name of a value that is a symbol (any other value as it is)."
(define strip-name-value (subr rf-st (rf-value) rf-value)
  (lambda (v) (tagcase v (sym s (rf-sym (strip-name s))) (else x v))))

"A datum with its aliases replaced by their symbols: the datum itself where
it has none."
(define strip (subr rf-st (rf-value) rf-value)
  (lambda (x)
    (tagcase x
      (sym s (if (alias? s) (rf-sym (strip-name s)) x))
      (pair p
        (let* ((a (strip (array-ref p 0)))
               (d (strip (array-ref p 1))))
          (if (and (rf-eqv? a (array-ref p 0)) (rf-eqv? d (array-ref p 1))) x (rf-cons a d))))
      (vec v (sum vec (list->array (map (lambda ((e rf-value)) (strip e)) (array->list v)))))
      (else y x))))

"Whether x is the keyword name, perhaps renamed. Keywords like else and =>
are compared by name (not by binding)."
(define keyword? (subr rf-st (rf-value symbol) bool)
  (lambda (x name) (tagcase x (sym s (eq? (strip-name s) name)) (else y #f))))

"A datum as Larceny's write writes it, its aliases stripped."
(define datum->string (subr rf-eff (rf-value) string)
  (lambda (x) (datum-text (strip x) #f #t (lambda ((v rf-value)) (tagcase v (unspec u "#!unspecified") (else y "#<value>"))))))

;;; ------------------------------------------------------------ syntax-rules

"Signals a syntax error: a message and the form (shakedown's `error`)."
(define-type syntax-error-proc (subr rf-eff (string rf-value) void))

(define every-symbol? (subr rf-st (rf-value) bool)
  (lambda (l) (tagcase l (null u #t) (pair p (and (rf-symbol? (array-ref p 0)) (every-symbol? (array-ref p 1)))) (else x #f))))

"A macro from (syntax-rules [ellipsis] (literal …) (pattern template) …),
defined in environments cenv and genv."
(define make-syntax-rules (subr rf-eff (rf-value rf-cenv rf-genv syntax-error-proc) rf-macro)
  (lambda (spec cenv genv error)
    (begin
      (if (not (and (rf-list? spec) (rf-pair? spec) (keyword? (rf-car spec) 'syntax-rules) (rf-pair? (rf-cdr spec))))
          (error "expected (syntax-rules (literal ...) (pattern template) ...)" spec)
          #u)
      (let* ((custom? (rf-symbol? (rf-cadr spec)))
             (ellipsis (if custom? (rf-sym-of (rf-cadr spec)) '...))
             (literals (if custom? (rf-caddr spec) (rf-cadr spec)))
             (rules (if custom? (rf-cdddr spec) (rf-cddr spec))))
        (begin
          (if (not (and (rf-list? literals) (every-symbol? literals))) (error "bad syntax-rules literals" spec) #u)
          (for-each (lambda ((r rf-value))
                      (if (not (and (rf-list? r) (= (rf-length r) 2) (rf-pair? (rf-car r))))
                          (error "bad syntax-rules rule" r)
                          #u))
                    (rf-elements rules))
          (product (ellipsis ellipsis)
                   (literals (map (lambda ((l rf-value)) (rf-sym-of l)) (rf-elements literals)))
                   (rules (map (lambda ((r rf-value)) (product (pattern (rf-cdr (rf-car r))) (template (rf-cadr r))))
                               (rf-elements rules)))
                   (cenv cenv) (genv genv)))))))

"Bindings: pattern variables to what they matched; under an ellipsis, to
one binding for each match."
(define-type mbind (sumof (one rf-value) (many (listof mbind acyclic))))
(define-type mbinding (productof (var symbol) (b mbind)))
(define-type mbindings (listof mbinding acyclic))
(define-type maybe-mbindings (sumof (none unit) (some mbindings)))
(define mb-assq (subr rf-st (symbol mbindings) (sumof (none unit) (some mbind)))
  (lambda (v l) (cond ((null? l) (sum none #u)) ((eq? v (extract (car l) var)) (sum some (extract (car l) b))) (else (mb-assq v (cdr l))))))

"The expansion of form x, a use of macro m."
(define expand-macro (subr rf-eff (rf-macro rf-value syntax-error-proc) rf-value)
  (lambda (m x error)
    (letrec ((loop (subr rf-eff ((listof rf-rule acyclic)) rf-value)
               (lambda (rules)
                 (if (null? rules)
                     (error "no syntax-rules pattern matches" (strip x))
                     (tagcase (match m (extract (car rules) pattern) (rf-cdr x) nil)
                       (some b (transcribe m (extract (car rules) template) b
                                           (the (table symbol symbol @rf) (make-table symbol-hash symbol=?)) error))
                       (none u (loop (cdr rules))))))))
      (loop (extract m rules)))))

(define ellipsis? (subr rf-st (rf-macro rf-value) bool)
  (lambda (m x) (tagcase x (sym s (eq? (strip-name s) (strip-name (extract m ellipsis)))) (else y #f))))
(define literal? (subr rf-st (rf-macro rf-value) bool)
  (lambda (m x)
    (tagcase x
      (sym s (symbols-member? (strip-name s) (map (lambda ((l symbol)) (strip-name l)) (extract m literals))))
      (else y #f))))

"The bindings b extended by matching pattern p against form f, or none."
(define match (subr rf-eff (rf-macro rf-value rf-value mbindings) maybe-mbindings)
  (lambda (m p f b)
    (cond ((rf-symbol? p)
           (cond ((literal? m p) (if (and (rf-symbol? f) (eq? (strip-name (rf-sym-of f)) (strip-name (rf-sym-of p)))) (sum some b) (sum none #u)))
                 ((keyword? p '_) (sum some b))
                 (else (sum some (the mbindings (cons (product (var (rf-sym-of p)) (b (sum one f))) b))))))
          ((and (rf-pair? p) (rf-pair? (rf-cdr p)) (ellipsis? m (rf-cadr p)))
           (let* ((after (rf-cddr p))
                  (min-after (rf-length after))
                  (available (rf-length f)))
             (if (< available min-after) (sum none #u)
                 (letrec ((collect (subr rf-eff (rf-value int (listof mbindings acyclic)) maybe-mbindings)
                            (lambda (f k matches)
                              (if (= k 0)
                                  (tagcase (match m after f b)
                                    (none u (sum none #u))
                                    (some b2
                                      (sum some
                                           (the mbindings
                                             (append (map (lambda ((v symbol))
                                                            (product (var v)
                                                                     (b (sum many (map (lambda ((mb mbindings))
                                                                                         (tagcase (mb-assq v mb) (some x x) (none u (sum one rf-nil))))
                                                                                       (reverse matches))))))
                                                          (pattern-vars m (rf-car p)))
                                                     b2)))))
                                  (tagcase (match m (rf-car p) (rf-car f) nil)
                                    (none u (sum none #u))
                                    (some mb (collect (rf-cdr f) (- k 1) (the (listof mbindings acyclic) (cons mb matches)))))))))
                   (collect f (- available min-after) nil)))))
          ((rf-pair? p)
           (if (not (rf-pair? f)) (sum none #u)
               (tagcase (match m (rf-car p) (rf-car f) b)
                 (none u (sum none #u))
                 (some b2 (match m (rf-cdr p) (rf-cdr f) b2)))))
          ((rf-null? p) (if (rf-null? f) (sum some b) (sum none #u)))
          ((rf-vector? p)
           (if (rf-vector? f)
               (match m (rf-list (array->list (rf-slots-of p))) (rf-list (array->list (rf-slots-of f))) b)
               (sum none #u)))
          (else (if (equal-datum? p f) (sum some b) (sum none #u))))))

"equal? of two data (as a pattern's literal datum is compared)."
(define equal-datum? (subr rf-st (rf-value rf-value) bool)
  (lambda (a b)
    (tagcase a
      (pair p (and (rf-pair? b) (equal-datum? (array-ref p 0) (rf-car b)) (equal-datum? (array-ref p 1) (rf-cdr b))))
      (str s (tagcase b (str t (string=? s t)) (else x #f)))
      (vec v (tagcase b (vec w (and (= (array-length v) (array-length w)) (equal-datum? (rf-list (array->list v)) (rf-list (array->list w))))) (else x #f)))
      (else x (rf-eqv? a b)))))

(define pattern-vars (subr rf-st (rf-macro rf-value) symbols)
  (lambda (m p)
    (tagcase p
      (sym s (if (or (literal? m p) (ellipsis? m p) (keyword? p '_)) nil (list s)))
      (pair a (append (pattern-vars m (array-ref a 0)) (pattern-vars m (array-ref a 1))))
      (vec v (pattern-vars m (rf-list (array->list v))))
      (else x nil))))

"Template t with bindings b; renamed holds this expansion's aliases."
(define transcribe (subr rf-eff (rf-macro rf-value mbindings (table symbol symbol @rf) syntax-error-proc) rf-value)
  (lambda (m t b renamed error)
    (letrec ((walk (subr rf-eff (rf-value mbindings bool) rf-value)
               (lambda (t b escaped?)
                 (cond ((rf-symbol? t)
                        (let ((s (rf-sym-of t)))
                          (tagcase (mb-assq s b)
                            (none u
                              (if (table-has? renamed s)
                                  (rf-sym (table-ref renamed s s))
                                  (let ((a (make-alias s (extract m cenv) (extract m genv))))
                                    (begin (table-set! renamed s a) (rf-sym a)))))
                            (some mb
                              (tagcase mb
                                (many items (error "pattern variable used without its ellipsis" (strip t)))
                                (one v v))))))
                       ;; (... template): the ellipsis taken literally.
                       ((and (not escaped?) (rf-pair? t) (ellipsis? m (rf-car t)) (rf-pair? (rf-cdr t)))
                        (walk (rf-cadr t) b #t))
                       ((and (not escaped?) (rf-pair? t) (rf-pair? (rf-cdr t)) (ellipsis? m (rf-cadr t)))
                        (letrec ((count (subr rf-eff (rf-value int) rf-value)
                                   (lambda (rest depth)
                                     (if (and (rf-pair? rest) (ellipsis? m (rf-car rest)))
                                         (count (rf-cdr rest) (+ depth 1))
                                         (let* ((repeated (repeat (rf-car t) b depth))
                                                (after (walk rest b escaped?)))
                                           (rf-append2 repeated after))))))
                          (count (rf-cddr t) 1)))
                       ((rf-pair? t)
                        (let* ((a (walk (rf-car t) b escaped?))
                               (d (walk (rf-cdr t) b escaped?)))
                          (rf-cons a d)))
                       ((rf-vector? t) (sum vec (list->array (rf-elements (walk (rf-list (array->list (rf-slots-of t))) b escaped?)))))
                       (else t))))
             ;; The forms of sub-template sub under depth ellipses, as a list.
             (repeat (subr rf-eff (rf-value mbindings int) rf-value)
               (lambda (sub b depth)
                 (let* ((vars (filter (lambda ((v symbol)) (tagcase (mb-assq v b) (some mb (tagcase mb (many i #t) (one x #f))) (none u #f)))
                                      (pattern-vars m sub)))
                        (lengths (map (lambda ((v symbol)) (list-length (items-of (mb-assq v b)))) vars)))
                   (begin
                     (if (null? vars) (error "ellipsis after a template with no pattern variable under one" (strip t)) #u)
                     (if (not (all-equal? lengths)) (error "pattern variables under one ellipsis matched different numbers of forms" (strip t)) #u)
                     (letrec ((each (subr rf-eff (int rf-value) rf-value)
                                (lambda (i acc)
                                  (if (= i (car lengths))
                                      (rf-reverse-append acc)
                                      (let* ((bi (the mbindings
                                                   (append (map (lambda ((v symbol))
                                                                  (product (var v) (b (list-ref-mbind (items-of (mb-assq v b)) i))))
                                                                vars)
                                                           b)))
                                             (part (if (= depth 1) (rf-list1 (walk sub bi #f)) (repeat sub bi (- depth 1)))))
                                        (each (+ i 1) (rf-cons part acc)))))))
                       (each 0 rf-nil)))))))
      (walk t b #f))))
(define items-of (subr rf-st ((sumof (none unit) (some mbind))) (listof mbind acyclic))
  (lambda (x) (tagcase x (some mb (tagcase mb (many items items) (one v nil))) (none u nil))))
(define list-ref-mbind (subr rf-st ((listof mbind acyclic) int) mbind)
  (lambda (l i) (cond ((null? l) (sum one rf-nil)) ((= i 0) (car l)) (else (list-ref-mbind (cdr l) (- i 1))))))
(define all-equal? (subr rf-st (ints) bool)
  (lambda (l) (or (null? l) (null? (cdr l)) (and (= (car l) (car (cdr l))) (all-equal? (cdr l))))))
"acc is a list of lists, last first: them appended, first first."
(define rf-reverse-append (subr rf-st (rf-value) rf-value)
  (lambda (acc)
    (letrec ((go (subr rf-st (rf-value rf-value) rf-value)
               (lambda (acc result) (if (rf-pair? acc) (go (rf-cdr acc) (rf-append2 (rf-car acc) result)) result))))
      (go acc rf-nil))))
