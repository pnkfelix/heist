;;; model.fx: casing's models, what they mean, and their commands: a
;;; model's forms read into sigs, fields, facts, predicates and commands;
;;; a command's scope made into bounds; its formula translated, state by
;;; state over a lasso of states, into circuits (circuit.fx) over matrices
;;; (matrix.fx); and what the solver finds shown. docs/casing.md says what
;;; the language is and where it follows Alloy 6 (Pardinus) and where not.

(module-parameters ((m-sat (load-moduleof "../combo/sat.fx"))
                    (m-circuit (load-moduleof "circuit.fx" m-sat))
                    (m-matrix (load-moduleof "matrix.fx" m-sat m-circuit))))
(hide (define kit-strings (load-module "../kit/strings.fx"))
      (import kit-strings string-join))

(define-type datums (listof datum acyclic))
"What the reading of a model does: it may loop, and reads the module's globals."
(define-effect ro (maxeff spin (read @globals)))

;;; ------------------------------------------------------------ data read

(define sym? (subr ro (datum string) bool)
  (lambda (d name) (and (symbol? d) (string=? (symbol->string d) name))))
"A list's head, if a symbol, else \"\"."
(define head (subr ro (datum) string)
  (lambda (d) (if (pair? d) (let ((h (car d))) (if (symbol? h) (symbol->string h) "")) "")))
(define items (subr ro (datum) datums)
  (lambda (d) (if (pair? d) (cons (car d) (items (cdr d))) nil)))
(define name-of (subr ro (datum) string)
  (lambda (d) (if (symbol? d) (symbol->string d) (error (string-append "casing: a name is expected, not " (shown d))))))
(define nth (subr ro (datum int) datum)
  (lambda (d i) (if (pair? d) (if (= i 0) (car d) (nth (cdr d) (- i 1))) (error (string-append "casing: too short: " (shown d))))))
(define len (subr ro (datum) int) (lambda (d) (if (pair? d) (+ 1 (len (cdr d))) 0)))
"A datum written, for messages."
(define shown (subr ro (datum) string)
  (lambda (d)
    (cond ((symbol? d) (symbol->string d))
          ((datum-int? d) (int->string d))
          ((bool? d) (if d "#t" "#f"))
          ((null? d) "()")
          ((pair? d) (string-append "(" (string-append (string-join (shown-all (items d)) " ") ")")))
          (else "?"))))
(define shown-all (subr ro (datums) strings)
  (lambda (l) (if (null? l) nil (cons (shown (car l)) (shown-all (cdr l))))))
(define sym (subr ro (string) datum) (lambda (s) (string->symbol s)))
"Whether a name is a region's, `@r`."
(define region-name? (subr ro (string) bool)
  (lambda (n) (and (> (string-length n) 1) (char=? (string-ref n 0) #\@))))
(define region? (subr ro (datum) bool) (lambda (d) (and (symbol? d) (region-name? (name-of d)))))
(define member-string? (subr ro (string strings) bool)
  (lambda (s l) (and (pair? l) (or (string=? s (car l)) (member-string? s (cdr l))))))

;;; ------------------------------------------------------------ models

"A sig: its parent (\"\" if none), whether it is a subset (`in`) of the
parent, rather than a part of it (`extends`); abstract; its multiplicity
(\"set\", \"one\", \"lone\", \"some\"); whether it changes from state to
state, and the region it changes in (\"\" if none)."
(define-type sig-info (productof (name string) (parent string) (subset bool) (abstract bool) (mult string) (var bool) (region string)))
"A field of `owner`: the columns after the owner's (expressions, sig
names most often), the multiplicity of the last, whether it changes, and
the region it changes in (\"\" if none)."
(define-type field-info (productof (name string) (owner string) (cols datums) (mult string) (var bool) (region string)))
"A predicate, function or event: its declarations `((x T) …)`, its body;
an event's relations and regions (`@r`) it writes (the rest are unchanged)."
(define-type def-info (productof (name string) (params datums) (body datum) (fun bool) (event bool) (writes strings)))
(define-type named (productof (name string) (body datum)))
(define-type model
  (productof (sigs (listof sig-info acyclic)) (fields (listof field-info acyclic)) (facts datums)
             (defs (listof def-info acyclic)) (asserts (listof named acyclic)) (commands datums)))

(define empty-model model (product (sigs nil) (fields nil) (facts nil) (defs nil) (asserts nil) (commands nil)))

"A field's type `T`, `(m T)` or `(-> T U …)`: its multiplicity and columns."
(define field-type (subr ro (datum) (productof (mult string) (cols datums)))
  (lambda (t)
    (let ((h (head t)))
      (cond ((or (string=? h "lone") (string=? h "one") (string=? h "some") (string=? h "set"))
             (let ((inner (nth t 1)))
               (if (string=? (head inner) "->")
                   (product (mult h) (cols (cdr (items inner))))
                   (product (mult h) (cols (list inner))))))
            ((string=? h "->") (product (mult "set") (cols (cdr (items t)))))
            (else (product (mult "one") (cols (list t))))))))

"A conjunction of a body's forms."
(define conj (subr ro (datums) datum)
  (lambda (fs) (if (and (pair? fs) (null? (cdr fs))) (car fs) (the datum (cons (sym "and") fs)))))

"One top-level form added to `m`."
(define add-form (subr ro (model datum) model)
  (lambda (m d)
    (let ((h (head d)) (xs (if (pair? d) (cdr (items d)) nil)))
      (cond
        ((string=? h "sig")
         (let* ((name (name-of (car xs)))
                (opts (cdr xs)))
           (letrec ((go (subr ro (datums sig-info (listof field-info acyclic)) model)
                      (lambda (os s fs)
                        (if (null? os)
                            (product (sigs (cons s (extract m sigs))) (fields (append fs (extract m fields)))
                                     (facts (extract m facts)) (defs (extract m defs)) (asserts (extract m asserts)) (commands (extract m commands)))
                            (let* ((o (car os)) (oh (head o)))
                              (cond
                                ((sym? o "abstract") (go (cdr os) (product (name name) (parent (extract s parent)) (subset (extract s subset)) (abstract #t) (mult (extract s mult)) (var (extract s var)) (region (extract s region))) fs))
                                ((sym? o "var")           ; var, or var @r: the sig changes (in r)
                                 (let ((r (if (and (pair? (cdr os)) (region? (car (cdr os)))) (name-of (car (cdr os))) "")))
                                   (go (if (string=? r "") (cdr os) (cdr (cdr os)))
                                       (product (name name) (parent (extract s parent)) (subset (extract s subset)) (abstract (extract s abstract)) (mult (extract s mult)) (var #t) (region r)) fs)))
                                ((or (sym? o "one") (sym? o "lone") (sym? o "some"))
                                 (go (cdr os) (product (name name) (parent (extract s parent)) (subset (extract s subset)) (abstract (extract s abstract)) (mult (name-of o)) (var (extract s var)) (region (extract s region))) fs))
                                ((or (string=? oh "extends") (string=? oh "in"))
                                 (go (cdr os) (product (name name) (parent (name-of (nth o 1))) (subset (string=? oh "in")) (abstract (extract s abstract)) (mult (extract s mult)) (var (extract s var)) (region (extract s region))) fs))
                                ((string=? oh "var")       ; (var f T) or (var @r f T): a field that changes (in r)
                                 (let* ((r (if (region? (nth o 1)) (name-of (nth o 1)) ""))
                                        (j (if (string=? r "") 1 2))
                                        (t (field-type (nth o (+ j 1)))))
                                   (go (cdr os) s (cons (product (name (name-of (nth o j))) (owner name) (cols (extract t cols)) (mult (extract t mult)) (var #t) (region r)) fs))))
                                ((pair? o)                 ; (f T): a field
                                 (let ((t (field-type (nth o 1))))
                                   (go (cdr os) s (cons (product (name (name-of (car o))) (owner name) (cols (extract t cols)) (mult (extract t mult)) (var #f) (region "")) fs))))
                                (else (error (string-append "casing: what is this in a sig? " (shown o))))))))))
             (go opts (product (name name) (parent "") (subset #f) (abstract #f) (mult "set") (var #f) (region "")) nil))))
        ((string=? h "fact")
         (let ((body (if (and (pair? xs) (symbol? (car xs)) (pair? (cdr xs))) (cdr xs) xs)))
           (product (sigs (extract m sigs)) (fields (extract m fields)) (facts (cons (conj body) (extract m facts)))
                    (defs (extract m defs)) (asserts (extract m asserts)) (commands (extract m commands)))))
        ((or (string=? h "pred") (string=? h "fun") (string=? h "event"))
         (let* ((sig (car xs)) (name (name-of (car sig))) (params (cdr (items sig)))
                (event (string=? h "event"))
                (writes (if (and event (pair? (cdr xs)) (string=? (head (car (cdr xs))) "writes"))
                            (letrec ((names (subr ro (datums) strings) (lambda (l) (if (null? l) nil (cons (name-of (car l)) (names (cdr l)))))))
                              (names (cdr (items (car (cdr xs))))))
                            nil))
                (body (if (and event (pair? (cdr xs)) (string=? (head (car (cdr xs))) "writes")) (cdr (cdr xs)) (cdr xs))))
           (product (sigs (extract m sigs)) (fields (extract m fields)) (facts (extract m facts))
                    (defs (cons (product (name name) (params params) (body (if (string=? h "fun") (car body) (conj body)))
                                         (fun (string=? h "fun")) (event event) (writes writes))
                                (extract m defs)))
                    (asserts (extract m asserts)) (commands (extract m commands)))))
        ((string=? h "assert")
         (product (sigs (extract m sigs)) (fields (extract m fields)) (facts (extract m facts)) (defs (extract m defs))
                  (asserts (cons (product (name (name-of (car xs))) (body (conj (cdr xs)))) (extract m asserts)))
                  (commands (extract m commands))))
        ((or (string=? h "run") (string=? h "check"))
         (product (sigs (extract m sigs)) (fields (extract m fields)) (facts (extract m facts)) (defs (extract m defs))
                  (asserts (extract m asserts)) (commands (cons d (extract m commands)))))
        (else (error (string-append "casing: not a form of a model: " (shown d))))))))

"A model of forms, in order."
(define read-model (subr ro (datums) model)
  (lambda (ds)
    (letrec ((go (subr ro (datums model) model) (lambda (l m) (if (null? l) m (go (cdr l) (add-form m (car l)))))))
      (let ((m (go ds empty-model)))
        (product (sigs (reverse (extract m sigs))) (fields (reverse (extract m fields))) (facts (reverse (extract m facts)))
                 (defs (extract m defs)) (asserts (extract m asserts)) (commands (reverse (extract m commands))))))))

(define find-sig (subr ro (model string) (sumof (none unit) (some sig-info)))
  (lambda (m n) (letrec ((go (subr ro ((listof sig-info acyclic)) (sumof (none unit) (some sig-info)))
                           (lambda (l) (cond ((null? l) (sum none #u)) ((string=? (extract (car l) name) n) (sum some (car l))) (else (go (cdr l)))))))
                  (go (extract m sigs)))))
(define find-def (subr ro (model string) (sumof (none unit) (some def-info)))
  (lambda (m n) (letrec ((go (subr ro ((listof def-info acyclic)) (sumof (none unit) (some def-info)))
                           (lambda (l) (cond ((null? l) (sum none #u)) ((string=? (extract (car l) name) n) (sum some (car l))) (else (go (cdr l)))))))
                  (go (extract m defs)))))
(define any-var? (subr ro (model) bool)
  (lambda (m) (or (letrec ((go (subr ro ((listof sig-info acyclic)) bool) (lambda (l) (and (pair? l) (or (extract (car l) var) (go (cdr l)))))))
                    (go (extract m sigs)))
                  (letrec ((go (subr ro ((listof field-info acyclic)) bool) (lambda (l) (and (pair? l) (or (extract (car l) var) (go (cdr l)))))))
                    (go (extract m fields))))))
"The names of the relations that change."
(define var-names (subr ro (model) strings)
  (lambda (m) (append (letrec ((go (subr ro ((listof sig-info acyclic)) strings)
                                 (lambda (l) (cond ((null? l) nil) ((extract (car l) var) (cons (extract (car l) name) (go (cdr l)))) (else (go (cdr l)))))))
                        (go (extract m sigs)))
                      (letrec ((go (subr ro ((listof field-info acyclic)) strings)
                                 (lambda (l) (cond ((null? l) nil) ((extract (car l) var) (cons (extract (car l) name) (go (cdr l)))) (else (go (cdr l)))))))
                        (go (extract m fields))))))

"The names of the relations that change in region `r`."
(define region-names (subr ro (model string) strings)
  (lambda (m r) (append (letrec ((go (subr ro ((listof sig-info acyclic)) strings)
                                   (lambda (l) (cond ((null? l) nil) ((string=? (extract (car l) region) r) (cons (extract (car l) name) (go (cdr l)))) (else (go (cdr l)))))))
                          (go (extract m sigs)))
                        (letrec ((go (subr ro ((listof field-info acyclic)) strings)
                                   (lambda (l) (cond ((null? l) nil) ((string=? (extract (car l) region) r) (cons (extract (car l) name) (go (cdr l)))) (else (go (cdr l)))))))
                          (go (extract m fields))))))
"The relations an event's `writes` names: a relation that changes names
itself, and a region `@r` every relation that changes in it."
(define written (subr ro (model strings) strings)
  (lambda (m ns)
    (if (null? ns) nil
        (let ((n (car ns)) (rest (written m (cdr ns))))
          (cond ((region-name? n)
                 (let ((rs (region-names m n)))
                   (if (null? rs) (error (string-append "casing: no relation changes in region " n)) (append rs rest))))
                ((member-string? n (var-names m)) (cons n rest))
                (else (error (string-append "casing: written, but it does not change: " n))))))))

;;; ------------------------------------------------------------ scopes and bounds

"A command's scope: the default, each sig's (and whether exactly), and
the steps of a trace, at least and at most."
(define-type scope-entry (productof (name string) (count int) (exact bool)))
(define-type scope (productof (default int) (sigs (listof scope-entry acyclic)) (min-steps int) (max-steps int)))

(define read-scope (subr ro (model datums) scope)
  (lambda (m specs)
    (letrec ((go (subr ro (datums scope) scope)
               (lambda (l s)
                 (if (null? l) s
                     (let ((d (car l)) (rest (cdr l)))
                       (cond ((datum-int? d) (go rest (product (default d) (sigs (extract s sigs)) (min-steps (extract s min-steps)) (max-steps (extract s max-steps)))))
                             ((string=? (head d) "steps")
                              (let ((a (nth d 1)) (b (if (= (len d) 3) (nth d 2) (nth d 1))))
                                (if (and (datum-int? a) (datum-int? b))
                                    (go rest (product (default (extract s default)) (sigs (extract s sigs)) (min-steps (if (= (len d) 3) a 1)) (max-steps b)))
                                    (error "casing: (steps N) or (steps MIN MAX)"))))
                             ((string=? (head d) "exactly")
                              (let ((c (nth d 2)))
                                (if (datum-int? c)
                                    (go rest (product (default (extract s default)) (sigs (cons (product (name (name-of (nth d 1))) (count c) (exact #t)) (extract s sigs)))
                                                      (min-steps (extract s min-steps)) (max-steps (extract s max-steps))))
                                    (error "casing: (exactly SIG N)"))))
                             ((and (pair? d) (symbol? (car d)))
                              (let ((c (nth d 1)))
                                (if (datum-int? c)
                                    (go rest (product (default (extract s default)) (sigs (cons (product (name (name-of (car d))) (count c) (exact #f)) (extract s sigs)))
                                                      (min-steps (extract s min-steps)) (max-steps (extract s max-steps))))
                                    (error "casing: (SIG N)"))))
                             (else (error (string-append "casing: not a scope: " (shown d))))))))))
      (go specs (product (default 3) (sigs nil) (min-steps 1) (max-steps (if (any-var? m) 10 1)))))))

(define scope-of (subr ro (scope string) (sumof (none unit) (some scope-entry)))
  (lambda (s n) (letrec ((go (subr ro ((listof scope-entry acyclic)) (sumof (none unit) (some scope-entry)))
                           (lambda (l) (cond ((null? l) (sum none #u)) ((string=? (extract (car l) name) n) (sum some (car l))) (else (go (cdr l)))))))
                  (go (extract s sigs)))))

"A sig's atoms: those it may have (upper), those it must (lower)."
(define-type sig-bound (productof (name string) (lower ints) (upper ints)))
(define-type universe (productof (names strings) (bounds (listof sig-bound acyclic)) (facts datums)))

(define bound-of (subr ro (universe string) (sumof (none unit) (some sig-bound)))
  (lambda (u n) (letrec ((go (subr ro ((listof sig-bound acyclic)) (sumof (none unit) (some sig-bound)))
                           (lambda (l) (cond ((null? l) (sum none #u)) ((string=? (extract (car l) name) n) (sum some (car l))) (else (go (cdr l)))))))
                  (go (extract u bounds)))))
(define ints-minus (subr ro (ints ints) ints)
  (lambda (a b) (cond ((null? a) nil) ((letrec ((in? (subr ro (ints) bool) (lambda (l) (and (pair? l) (or (= (car l) (car a)) (in? (cdr l))))))) (in? b))
                       (ints-minus (cdr a) b))
                      (else (cons (car a) (ints-minus (cdr a) b))))))
(define range (subr ro (int int) ints) (lambda (from to) (if (>= from to) nil (cons from (range (+ from 1) to)))))

"The universe a scope gives: each top-level sig's atoms, named after it;
a `one` sig extending another gets one of its parent's, its own; other
children may have any of what is left. And the facts the bounds alone do
not say: a scope smaller than the atoms a sig may have."
(define make-universe (subr ro (model scope) universe)
  (lambda (m s)
    (letrec ((count-for (subr ro (sig-info) int)
               (lambda (g) (if (or (string=? (extract g mult) "one") (string=? (extract g mult) "lone")) 1
                               (tagcase (scope-of s (extract g name)) (none u (extract s default)) (some e (extract e count))))))
             (exact? (subr ro (sig-info) bool)
               (lambda (g) (or (and (string=? (extract g mult) "one") (string=? (extract g parent) ""))
                               (tagcase (scope-of s (extract g name)) (none u #f) (some e (and (extract e exact) (string=? (extract g parent) "")))))))
             (children (subr ro (string (listof sig-info acyclic)) (listof sig-info acyclic))
               (lambda (p l) (cond ((null? l) nil) ((string=? (extract (car l) parent) p) (cons (car l) (children p (cdr l)))) (else (children p (cdr l))))))
             ;; a sig's children placed in atoms `avail`, and theirs
             (place (subr ro (sig-info ints strings (listof sig-bound acyclic) datums) universe)
               (lambda (p avail names bounds facts)
                 (letrec ((ones (subr ro ((listof sig-info acyclic) ints strings (listof sig-bound acyclic) datums) universe)
                            ;; `one` parts first, an atom each, named after them
                            (lambda (cs avail names bounds facts)
                              (cond ((null? cs) (rest (children (extract p name) (extract m sigs)) avail names bounds facts))
                                    ((and (string=? (extract (car cs) mult) "one") (not (extract (car cs) subset)) (pair? avail))
                                     (let* ((a (car avail)) (g (car cs))
                                            (names (set-name names a (string-append (extract g name) "$0"))))
                                       (let ((u (place g (list a) names (cons (product (name (extract g name)) (lower (list a)) (upper (list a))) bounds) facts)))
                                         (ones (cdr cs) (cdr avail) (extract u names) (extract u bounds) (extract u facts)))))
                                    (else (ones (cdr cs) avail names bounds facts)))))
                          (rest (subr ro ((listof sig-info acyclic) ints strings (listof sig-bound acyclic) datums) universe)
                            (lambda (cs avail names bounds facts)
                              (cond ((null? cs) (product (names names) (bounds bounds) (facts facts)))
                                    ((and (string=? (extract (car cs) mult) "one") (not (extract (car cs) subset))) (rest (cdr cs) avail names bounds facts))
                                    (else
                                     (let* ((g (car cs))
                                            (up (if (extract g subset)
                                                    (tagcase (bound-of (product (names names) (bounds bounds) (facts facts)) (extract g parent)) (none u avail) (some b (extract b upper)))
                                                    avail))
                                            (facts (tagcase (scope-of s (extract g name))
                                                     (none u facts)
                                                     (some e (cons (the datum (list (sym (if (extract e exact) "=" "<=")) (list (sym "size") (sym (extract g name))) (extract e count))) facts))))
                                            (u (place g up names (cons (product (name (extract g name)) (lower nil) (upper up)) bounds) facts)))
                                       (rest (cdr cs) avail (extract u names) (extract u bounds) (extract u facts)))))))
                          (set-name (subr ro (strings int string) strings)
                            (lambda (l i x) (cond ((null? l) nil) ((= i 0) (cons x (cdr l))) (else (cons (car l) (set-name (cdr l) (- i 1) x)))))))
                   (ones (children (extract p name) (extract m sigs)) (ints-minus avail nil) names bounds facts))))
             (tops (subr ro ((listof sig-info acyclic) strings (listof sig-bound acyclic) datums) universe)
               (lambda (l names bounds facts)
                 (cond ((null? l) (product (names names) (bounds bounds) (facts facts)))
                       ((not (string=? (extract (car l) parent) "")) (tops (cdr l) names bounds facts))
                       (else
                        (let* ((g (car l)) (k (count-for g)) (base (list-length names))
                               (atoms (range base (+ base k)))
                               (names (append names (letrec ((nm (subr ro (int) strings)
                                                                 (lambda (i) (if (>= i k) nil (cons (string-append (extract g name) (string-append "$" (int->string i))) (nm (+ i 1)))))))
                                                      (nm 0))))
                               (u (place g atoms names (cons (product (name (extract g name)) (lower (if (exact? g) atoms nil)) (upper atoms)) bounds) facts)))
                          (tops (cdr l) (extract u names) (extract u bounds) (extract u facts))))))))
      (tops (extract m sigs) nil nil nil))))

;;; ------------------------------------------------------------ translation

"A relation of the problem: its matrix in each state (one, if it does
not change)."
(define-type rel (productof (name string) (arity int) (var bool) (mats (arrayof matrix @cb))))
"A problem: its circuit, atoms, states, unrolls of the loop, the loop's
inputs (one each state it may go back to), relations, model and atoms'
names. Formulas are evaluated at positions of the trace, p = j·k + s:
state s in copy j of the states. Copy 0 is the trace from its start;
copy 1 on, the loop again, so its states from the loop's; the loop goes
back from the last copy's last state. A past formula nested d deep needs
d+1 copies to say at copy d what it says at every later pass
(Pardinus's unrolling; Latvala et al., \"Simple is better\", 2005)."
(define-type ctx (productof (c circuit) (n int) (k int) (u int) (loops ivec) (rels (listof rel acyclic)) (model model) (universe universe)))

"What a name is bound to: a value now, or an expression evaluated where
it is used (a predicate's argument, a `let`'s), in its own scope."
(define-type binding (productof (name string) (now bool) (val matrix) (code datum) (scope env)))
(define-type env (listof binding acyclic))

(define bind-now (subr ro (string matrix env) env)
  (lambda (n v e) (cons (product (name n) (now #t) (val v) (code (the datum #f)) (scope nil)) e)))
(define lookup (subr ro (env string) (sumof (none unit) (some binding)))
  (lambda (e n) (cond ((null? e) (sum none #u)) ((string=? (extract (car e) name) n) (sum some (car e))) (else (lookup (cdr e) n)))))
(define find-rel (subr ro (ctx string) (sumof (none unit) (some rel)))
  (lambda (x n) (letrec ((go (subr ro ((listof rel acyclic)) (sumof (none unit) (some rel)))
                           (lambda (l) (cond ((null? l) (sum none #u)) ((string=? (extract (car l) name) n) (sum some (car l))) (else (go (cdr l)))))))
                  (go (extract x rels)))))
(define rel-at (subr (read @cb) (rel int) matrix)
  (lambda (r i) (array-ref (extract r mats) (if (extract r var) i 0))))
"A relation at position p: as in its state."
(define rel-at-pos (subr cb-eff (ctx rel int) matrix)
  (lambda (x r p) (rel-at r (modulo p (extract x k)))))

(define cx (subr ro (ctx) circuit) (lambda (x) (extract x c)))
(define loop-at (subr (read @cb) (ctx int) int) (lambda (x l) (array-ref (extract x loops) l)))
"The positions of a trace from p on, in order, if the loop goes back to
state l: the rest of p's copy, the later copies from l, and, from the
last copy, its states from l up to p."
(define future-seq (subr cb-eff (ctx int int) ints)
  (lambda (x p l)
    (let* ((k (extract x k)) (u (extract x u)) (j (quotient p k)) (s (modulo p k)))
      (append (range p (+ (* j k) k))
              (append (letrec ((go (subr cb-eff (int) ints)
                                 (lambda (c) (if (>= c u) nil (append (range (+ (* c k) l) (+ (* c k) k)) (go (+ c 1)))))))
                        (go (+ j 1)))
                      (if (= j (- u 1)) (range (+ (* j k) l) p) nil))))))
"The positions of a trace up to p, in order, if the loop goes back to l
(none if p is not on that trace)."
(define past-seq (subr cb-eff (ctx int int) ints)
  (lambda (x p l)
    (let* ((k (extract x k)) (j (quotient p k)) (s (modulo p k)))
      (cond ((= j 0) (range 0 (+ s 1)))
            ((< s l) nil)
            (else (append (range 0 k)
                          (append (letrec ((go (subr cb-eff (int) ints)
                                             (lambda (c) (if (>= c j) nil (append (range (+ (* c k) l) (+ (* c k) k)) (go (+ c 1)))))))
                                    (go 1))
                                  (range (+ (* j k) l) (+ p 1)))))))))
"g's for the loop there is."
(define per-loop (subr cb-eff (ctx (subr cb-eff (int) int)) int)
  (lambda (x g)
    (c-or (cx x) (letrec ((go (subr cb-eff (int ints) ints)
                            (lambda (l acc) (if (>= l (extract x k)) acc (go (+ l 1) (cons (c-and2 (cx x) (loop-at x l) (g l)) acc))))))
                   (go 0 nil)))))
(define each-form (subr cb-eff ((subr cb-eff (int) int) ints) ints)
  (lambda (f ps) (if (null? ps) nil (cons (f (car ps)) (each-form f (cdr ps))))))

"The position after p: the next, or, from a copy's last state, the loop's
state in the next copy (the last copy's own, from the last)."
(define after-form (subr cb-eff (ctx int (subr cb-eff (int) int)) int)
  (lambda (x p f)
    (let* ((k (extract x k)) (j (quotient p k)) (s (modulo p k)) (j2 (min (+ j 1) (- (extract x u) 1))))
      (if (< s (- k 1)) (f (+ p 1))
          (per-loop x (lambda ((l int)) (f (+ (* j2 k) l))))))))
(define after-expr (subr cb-eff (ctx int (subr cb-eff (int) matrix)) matrix)
  (lambda (x p f)
    (let* ((k (extract x k)) (j (quotient p k)) (s (modulo p k)) (j2 (min (+ j 1) (- (extract x u) 1))))
      (if (< s (- k 1)) (f (+ p 1))
          (letrec ((go (subr cb-eff (int matrix) matrix)
                     (lambda (l acc) (if (< l 0) acc (go (- l 1) (m-ite (cx x) (loop-at x l) (f (+ (* j2 k) l)) acc))))))
            (go (- k 2) (f (+ (* j2 k) (- k 1)))))))))

"f until g along positions ps: g somewhere, f at every position before."
(define until-along (subr cb-eff (circuit (subr cb-eff (int) int) (subr cb-eff (int) int) ints) int)
  (lambda (c f g ps)
    (letrec ((go (subr cb-eff (ints int ints) ints)
               (lambda (l before acc)
                 (if (null? l) acc
                     (go (cdr l) (c-and2 c before (f (car l))) (cons (c-and2 c before (g (car l))) acc))))))
      (c-or c (go ps c-true nil)))))

(define arity-error (subr ro (datum string) void)
  (lambda (d why) (error (string-append "casing: " (string-append why (string-append ": " (shown d)))))))

"Expression `d` in state `i`."
(define expr (subr cb-eff (ctx datum int env) matrix)
  (lambda (x d i e)
    (let ((c (cx x)) (n (extract x n)))
      (if (symbol? d)
          (let ((s (symbol->string d)))
            (tagcase (lookup e s)
              (some b (if (extract b now) (extract b val) (expr x (extract b code) i (extract b scope))))
              (none u
                (tagcase (find-rel x s)
                  (some r (rel-at-pos x r i))
                  (none u
                    (cond ((string=? s "univ") (m-univ n))
                          ((string=? s "iden") (m-iden n))
                          ((string=? s "none") (m-none n 1))
                          (else (tagcase (find-def (extract x model) s)
                                  (some f (if (and (extract f fun) (null? (extract f params))) (expr x (extract f body) i nil)
                                              (arity-error d "not a relation")))
                                  (none u (arity-error d "unknown name"))))))))))
          (let* ((h (head d)) (args (if (pair? d) (cdr (items d)) nil)))
            (letrec ((all (subr cb-eff (datums) (listof matrix acyclic))
                       (lambda (l) (if (null? l) nil (cons (expr x (car l) i e) (all (cdr l))))))
                     (fold (subr cb-eff ((subr cb-eff (matrix matrix) matrix) (listof matrix acyclic)) matrix)
                       (lambda (f ms) (letrec ((go (subr cb-eff (matrix (listof matrix acyclic)) matrix)
                                                 (lambda (a l) (if (null? l) a (go (f a (car l)) (cdr l))))))
                                        (if (null? ms) (arity-error d "no operands") (go (car ms) (cdr ms))))))
                     (same (subr cb-eff ((subr cb-eff (matrix matrix) matrix)) matrix)
                       (lambda (f) (fold (lambda ((a matrix) (b matrix))
                                           (if (= (m-arity a) (m-arity b)) (f a b) (arity-error d "operands of different arities")))
                                         (all args))))
                     (binary (subr cb-eff () matrix)
                       (lambda () (let ((a (expr x (car args) i e))) (if (= (m-arity a) 2) a (arity-error d "a binary relation is expected"))))))
              (cond
                ((string=? h "join")
                 (fold (lambda ((a matrix) (b matrix))
                         (if (> (+ (m-arity a) (m-arity b)) 2) (m-join c n a b) (arity-error d "a join of two sets")))
                       (all args)))
                ((string=? h "->") (fold (lambda ((a matrix) (b matrix)) (m-product c n a b)) (all args)))
                ((string=? h "union") (same (lambda ((a matrix) (b matrix)) (m-union c a b))))
                ((string=? h "inter") (same (lambda ((a matrix) (b matrix)) (m-inter c a b))))
                ((string=? h "diff") (same (lambda ((a matrix) (b matrix)) (m-diff c a b))))
                ((string=? h "++") (same (lambda ((a matrix) (b matrix)) (m-override c n a b))))
                ((string=? h "<:") (let ((s (expr x (nth d 1) i e)) (r (expr x (nth d 2) i e)))
                                     (if (= (m-arity s) 1) (m-dom-restrict c n s r) (arity-error d "a set is expected first"))))
                ((string=? h ":>") (let ((r (expr x (nth d 1) i e)) (s (expr x (nth d 2) i e)))
                                     (if (= (m-arity s) 1) (m-range-restrict c n r s) (arity-error d "a set is expected last"))))
                ((string=? h "~") (m-transpose n (binary)))
                ((string=? h "^") (m-closure c n (binary)))
                ((string=? h "*") (m-rclosure c n (binary)))
                ((string=? h "if") (let ((a (expr x (nth d 2) i e)) (b (expr x (nth d 3) i e)))
                                     (if (= (m-arity a) (m-arity b)) (m-ite c (form x (nth d 1) i e) a b)
                                         (arity-error d "branches of different arities"))))
                ((or (string=? h "prime") (string=? h "quote"))
                 (after-expr x i (lambda ((j int)) (expr x (nth d 1) j e))))
                ((string=? h "let") (expr x (nth d 2) i (let-env x (items (nth d 1)) e)))
                ((string=? h "set") (comprehension x (items (nth d 1)) (nth d 2) i e))
                ((string=? h "") (arity-error d "not an expression"))
                (else
                 (tagcase (find-def (extract x model) h)
                   (some f (if (extract f fun) (expr x (extract f body) i (call-env x f args i e))
                               (arity-error d "a predicate, not a function")))
                   (none u (arity-error d "unknown operator")))))))))))

"`let`'s bindings, each evaluated where it is used."
(define let-env (subr cb-eff (ctx datums env) env)
  (lambda (x bs e)
    (if (null? bs) e
        (let-env x (cdr bs)
                 (cons (product (name (name-of (nth (car bs) 0))) (now #f) (val (m-none 1 1)) (code (nth (car bs) 1)) (scope e)) e)))))

"A call's scope: each parameter bound to its argument, by name."
(define call-env (subr cb-eff (ctx def-info datums int env) env)
  (lambda (x f args i e)
    (letrec ((names (subr ro (datums strings) strings)
               ;; ((x y T) (z U)): x y z
               (lambda (ds acc) (if (null? ds) (reverse acc)
                                    (names (cdr ds) (letrec ((go (subr ro (datums strings) strings)
                                                               (lambda (l acc) (if (null? (cdr l)) acc (go (cdr l) (cons (name-of (car l)) acc))))))
                                                      (go (items (car ds)) acc))))))
             (bind (subr cb-eff (strings datums env) env)
               (lambda (ps as acc)
                 (cond ((and (null? ps) (null? as)) acc)
                       ((or (null? ps) (null? as)) (error (string-append "casing: wrong number of arguments to " (extract f name))))
                       (else (bind (cdr ps) (cdr as) (cons (product (name (car ps)) (now #f) (val (m-none 1 1)) (code (car as)) (scope e)) acc)))))))
      (bind (names (extract f params) nil) args nil))))

"Every binding of declarations `((x y T) …)`, each later one's type in
the scope of those before: the bindings and when each holds."
(define-type grounding (productof (guard int) (scope env) (atoms ints)))
(define ground (subr cb-eff (ctx datums int env) (listof grounding acyclic))
  (lambda (x decls i e)
    (letrec ((names-type (subr ro (datums strings) (productof (names strings) (type datum)))
               (lambda (l acc) (if (null? (cdr l)) (product (names (reverse acc)) (type (car l))) (names-type (cdr l) (cons (name-of (car l)) acc)))))
             ;; flatten ((x y T)) into (x T) (y T)
             (flat (subr ro (datums) (listof (productof (name string) (type datum)) acyclic))
               (lambda (ds) (if (null? ds) nil
                                (let ((nt (names-type (items (car ds)) nil)))
                                  (append (letrec ((go (subr ro (strings) (listof (productof (name string) (type datum)) acyclic))
                                                         (lambda (ns) (if (null? ns) nil (cons (product (name (car ns)) (type (extract nt type))) (go (cdr ns)))))))
                                            (go (extract nt names)))
                                          (flat (cdr ds)))))))
             (go (subr cb-eff ((listof (productof (name string) (type datum)) acyclic) grounding) (listof grounding acyclic))
               (lambda (ds g)
                 (if (null? ds) (list g)
                     (let* ((m (expr x (extract (car ds) type) i (extract g scope))) (k (m-arity m)))
                       (letrec ((each (subr cb-eff (int) (listof grounding acyclic))
                                  (lambda (t)
                                    (if (>= t (m-size m)) nil
                                        (let ((b (m-ref m t)))
                                          (if (= b c-false) (each (+ t 1))
                                              (append (go (cdr ds) (product (guard (c-and2 (cx x) (extract g guard) b))
                                                                            (scope (bind-now (extract (car ds) name) (m-tuple (extract x n) k t) (extract g scope)))
                                                                            (atoms (cons t (extract g atoms)))))
                                                      (each (+ t 1)))))))))
                         (each 0)))))))
      (go (flat decls) (product (guard c-true) (scope e) (atoms nil))))))

"{decls | f}: of unary declarations, a relation of their atoms."
(define comprehension (subr cb-eff (ctx datums datum int env) matrix)
  (lambda (x decls f i e)
    (let* ((gs (ground x decls i e)) (n (extract x n))
           (k (if (null? gs) (list-length decls) (list-length (extract (car gs) atoms))))
           (v (the ivec (make-array (power n k) c-false))))
      (letrec ((index (subr ro (ints int) int) (lambda (as acc) (if (null? as) acc (index (cdr as) (+ (* acc n) (car as))))))
               (go (subr cb-eff ((listof grounding acyclic)) matrix)
                 (lambda (l)
                   (if (null? l) (product (arity k) (cells v))
                       (let ((t (index (reverse (extract (car l) atoms)) 0)))
                         (begin (array-set! v t (c-and2 (cx x) (extract (car l) guard) (form x f i (extract (car l) scope))))
                                (go (cdr l))))))))
        (go gs)))))

"Whether `d` is an integer expression."
(define int-expr? (subr ro (datum) bool)
  (lambda (d) (or (datum-int? d) (let ((h (head d))) (or (string=? h "size") (string=? h "+") (string=? h "-"))))))

"Integer expression `d` in state `i`: a count (matrix.fx)."
(define ival (subr cb-eff (ctx datum int env) count)
  (lambda (x d i e)
    (if (datum-int? d)
        (if (>= d 0) (count-const d) (arity-error d "casing's integers are not negative"))
        (let ((h (head d)))
          (cond ((string=? h "size") (m-count (cx x) (expr x (nth d 1) i e)))
                ((string=? h "+") (count-add (cx x) (ival x (nth d 1) i e) (ival x (nth d 2) i e)))
                ((string=? h "-") (count-sub (cx x) (ival x (nth d 1) i e) (ival x (nth d 2) i e)))
                (else (arity-error d "not an integer expression")))))))

"Formula `d` in state `i`."
(define form (subr cb-eff (ctx datum int env) int)
  (lambda (x d i e)
    (let* ((c (cx x)) (h (head d)) (args (if (pair? d) (cdr (items d)) nil))
           (k (extract x k)))
      (letrec ((f1 (subr cb-eff (int) int) (lambda (j) (form x (car args) j e)))
               (f2 (subr cb-eff (int) int) (lambda (j) (form x (car (cdr args)) j e)))
               (all-forms (subr cb-eff (datums) ints) (lambda (l) (if (null? l) nil (cons (form x (car l) i e) (all-forms (cdr l))))))
               (e1 (subr cb-eff () matrix) (lambda () (expr x (car args) i e)))
               (e2 (subr cb-eff () matrix) (lambda () (expr x (car (cdr args)) i e)))
               (same2 (subr cb-eff ((subr cb-eff (matrix matrix) int)) int)
                 (lambda (g) (let ((a (e1)) (b (e2))) (if (= (m-arity a) (m-arity b)) (g a b) (arity-error d "operands of different arities")))))
               (quantified? (subr ro () bool) (lambda () (= (list-length args) 2)))
               (quant (subr cb-eff (string) int)
                 (lambda (q)
                   (let ((gs (ground x (items (car args)) i e)))
                     (letrec ((pairs (subr cb-eff ((listof grounding acyclic)) ints)
                                (lambda (l) (if (null? l) nil
                                                (cons (let ((b (form x (car (cdr args)) i (extract (car l) scope))) (g (extract (car l) guard)))
                                                        (if (string=? q "all") (c-implies c g b) (c-and2 c g b)))
                                                      (pairs (cdr l)))))))
                       (let ((ps (pairs gs)))
                         (cond ((string=? q "all") (c-and c ps))
                               ((string=? q "some") (c-or c ps))
                               ((string=? q "no") (c-not (c-or c ps)))
                               ((string=? q "lone") (c-at-most-one c ps))
                               (else (c-exactly-one c ps)))))))))
        (cond
          ((bool? d) (if d c-true c-false))
          ((sym? d "true") c-true)
          ((sym? d "false") c-false)
          ((symbol? d)
           (tagcase (find-def (extract x model) (symbol->string d))
             (some f (if (extract f fun) (arity-error d "a function, not a predicate") (call x f nil i e)))
             (none u (tagcase (lookup e (symbol->string d))
                       (some b (if (extract b now) (arity-error d "a relation, not a formula")
                                   (form x (extract b code) i (extract b scope))))
                       (none u (arity-error d "not a formula"))))))
          ((string=? h "in") (same2 (lambda ((a matrix) (b matrix)) (m-subset c a b))))
          ((string=? h "=")
           (if (or (int-expr? (car args)) (int-expr? (car (cdr args))))
               (count-eq c (ival x (car args) i e) (ival x (car (cdr args)) i e))
               (same2 (lambda ((a matrix) (b matrix)) (m-equal c a b)))))
          ((string=? h "!=") (c-not (form x (the datum (cons (sym "=") args)) i e)))
          ((string=? h "<=") (count-ge c (ival x (car (cdr args)) i e) (ival x (car args) i e)))
          ((string=? h ">=") (count-ge c (ival x (car args) i e) (ival x (car (cdr args)) i e)))
          ((string=? h "<") (c-not (count-ge c (ival x (car args) i e) (ival x (car (cdr args)) i e))))
          ((string=? h ">") (c-not (count-ge c (ival x (car (cdr args)) i e) (ival x (car args) i e))))
          ((string=? h "all") (quant "all"))
          ((string=? h "some") (if (quantified?) (quant "some") (m-some c (e1))))
          ((string=? h "no") (if (quantified?) (quant "no") (m-no c (e1))))
          ((string=? h "one") (if (quantified?) (quant "one") (m-one c (e1))))
          ((string=? h "lone") (if (quantified?) (quant "lone") (m-lone c (e1))))
          ((string=? h "not") (c-not (f1 i)))
          ((string=? h "and") (c-and c (all-forms args)))
          ((string=? h "or") (c-or c (all-forms args)))
          ((or (string=? h "implies") (string=? h "=>")) (c-implies c (f1 i) (f2 i)))
          ((string=? h "iff") (c-iff c (f1 i) (f2 i)))
          ((string=? h "if") (c-ite c (f1 i) (f2 i) (form x (nth d 3) i e)))
          ((string=? h "let") (form x (nth d 2) i (let-env x (items (nth d 1)) e)))
          ;; time
          ((string=? h "after") (after-form x i f1))
          ((string=? h "then") (c-and2 c (f1 i) (after-form x i f2)))
          ((string=? h "always") (per-loop x (lambda ((l int)) (c-and c (each-form f1 (future-seq x i l))))))
          ((string=? h "eventually") (per-loop x (lambda ((l int)) (c-or c (each-form f1 (future-seq x i l))))))
          ((string=? h "until") (per-loop x (lambda ((l int)) (until-along c f1 f2 (future-seq x i l)))))
          ((string=? h "releases")
           (c-not (per-loop x (lambda ((l int)) (until-along c (lambda ((j int)) (c-not (f1 j))) (lambda ((j int)) (c-not (f2 j))) (future-seq x i l))))))
          ((string=? h "before")
           (per-loop x (lambda ((l int)) (let ((ps (reverse (past-seq x i l)))) (if (and (pair? ps) (pair? (cdr ps))) (f1 (car (cdr ps))) c-false)))))
          ((string=? h "once") (per-loop x (lambda ((l int)) (c-or c (each-form f1 (past-seq x i l))))))
          ((string=? h "historically") (per-loop x (lambda ((l int)) (c-and c (each-form f1 (past-seq x i l))))))
          ((string=? h "since") (per-loop x (lambda ((l int)) (until-along c f1 f2 (reverse (past-seq x i l))))))
          ((string=? h "triggered")
           (c-not (per-loop x (lambda ((l int)) (until-along c (lambda ((j int)) (c-not (f1 j))) (lambda ((j int)) (c-not (f2 j))) (reverse (past-seq x i l)))))))
          ;; the relations named unchanged in the next state; a region @r
          ;; names every relation that changes in it
          ((string=? h "unchanged")
           (c-and c (letrec ((go (subr cb-eff (datums) ints)
                               (lambda (l) (cond ((null? l) nil)
                                                 ((region? (car l))
                                                  (go (append (letrec ((syms (subr ro (strings) datums) (lambda (ns) (if (null? ns) nil (cons (sym (car ns)) (syms (cdr ns)))))))
                                                                (syms (written (extract x model) (list (name-of (car l))))))
                                                              (cdr l))))
                                                 (else (cons (m-equal c (after-expr x i (lambda ((j int)) (expr x (car l) j e))) (expr x (car l) i e))
                                                             (go (cdr l))))))))
                      (go args))))
          ((string=? h "stutter")
           (form x (the datum (cons (sym "unchanged") (letrec ((go (subr ro (strings) datums) (lambda (l) (if (null? l) nil (cons (sym (car l)) (go (cdr l)))))))
                                                         (go (var-names (extract x model))))))
                 i e))
          ((string=? h "") (arity-error d "not a formula"))
          (else
           (tagcase (find-def (extract x model) h)
             (some f (if (extract f fun) (arity-error d "a function, not a predicate") (call x f args i e)))
             (none u (arity-error d "unknown predicate")))))))))

"A predicate's or event's call. An event's frame: every relation that
changes and that it does not write is unchanged. A region it writes
writes every relation that changes in it."
(define call (subr cb-eff (ctx def-info datums int env) int)
  (lambda (x f args i e)
    (let ((body (form x (extract f body) i (call-env x f args i e)))
          (writes (written (extract x model) (extract f writes))))
      (if (not (extract f event)) body
          (c-and2 (cx x) body
                  (form x (the datum (cons (sym "unchanged")
                                           (letrec ((go (subr ro (strings) datums)
                                                      (lambda (l) (cond ((null? l) nil)
                                                                        ((member-string? (car l) writes) (go (cdr l)))
                                                                        (else (cons (sym (car l)) (go (cdr l))))))))
                                             (go (var-names (extract x model))))))
                        i nil))))))

;;; ------------------------------------------------------------ the problem

"The facts the declarations give: sigs within their parents, parts
disjoint, an abstract sig its parts, multiplicities, and fields within
their columns with their last column's multiplicity."
(define declaration-facts (subr ro (model) datums)
  (lambda (m)
    (letrec ((s (subr ro (string) datum) (lambda (n) (sym n)))
             (sigs (subr ro ((listof sig-info acyclic)) datums)
               (lambda (l)
                 (if (null? l) nil
                     (let* ((g (car l)) (n (extract g name))
                            (parts (letrec ((go (subr ro ((listof sig-info acyclic)) strings)
                                              (lambda (k) (cond ((null? k) nil)
                                                                ((and (string=? (extract (car k) parent) n) (not (extract (car k) subset))) (cons (extract (car k) name) (go (cdr k))))
                                                                (else (go (cdr k)))))))
                                     (go (extract m sigs))))
                            (fs (append (if (string=? (extract g parent) "") nil (list (the datum (list (sym "in") (s n) (s (extract g parent))))))
                                        (append (if (string=? (extract g mult) "set") nil (list (the datum (list (sym (extract g mult)) (s n)))))
                                                (append (if (and (extract g abstract) (pair? parts))
                                                            (list (the datum (list (sym "in") (s n) (the datum (cons (sym "union") (names->syms parts))))))
                                                            nil)
                                                        (disjoint parts))))))
                       (append fs (sigs (cdr l)))))))
             (names->syms (subr ro (strings) datums) (lambda (l) (if (null? l) nil (cons (sym (car l)) (names->syms (cdr l))))))
             (disjoint (subr ro (strings) datums)
               (lambda (l) (if (null? l) nil
                               (append (letrec ((go (subr ro (strings) datums)
                                                  (lambda (k) (if (null? k) nil (cons (the datum (list (sym "no") (list (sym "inter") (sym (car l)) (sym (car k))))) (go (cdr k)))))))
                                         (go (cdr l)))
                                       (disjoint (cdr l))))))
             (fields (subr ro ((listof field-info acyclic)) datums)
               (lambda (l)
                 (if (null? l) nil
                     (let* ((f (car l)) (fn (sym (extract f name))) (o (sym (extract f owner)))
                            (within (the datum (list (sym "in") fn (the datum (cons (sym "->") (if (string=? (extract f owner) "") (extract f cols) (cons o (extract f cols))))))))
                            (mult (if (string=? (extract f mult) "set") nil
                                      (list (the datum (list (sym "all") (list (list (sym "%this") o))
                                                             (list (sym (extract f mult)) (list (sym "join") (sym "%this") fn))))))))
                       (cons within (append mult (fields (cdr l)))))))))
      (append (sigs (extract m sigs)) (fields (extract m fields))))))

"A relation's matrix in one state: true on its lower bound, an input on
the rest of its upper, false elsewhere."
(define bound-matrix (subr cb-eff (circuit int int (subr ro (int) int)) matrix)
  (lambda (c n k at)            ; at: 1 lower, 0 upper only, -1 neither
    (m-build n k (lambda ((t int)) (let ((w (at t))) (cond ((= w 1) c-true) ((= w 0) (c-input! c)) (else c-false)))))))

"Which of a column's atoms it may hold: a sig's upper bound, else every atom."
(define column-atoms (subr ro (universe datum int) ints)
  (lambda (u d n) (if (symbol? d) (tagcase (bound-of u (symbol->string d)) (some b (extract b upper)) (none u2 (range 0 n))) (range 0 n))))

(define in-ints? (subr ro (int ints) bool) (lambda (x l) (and (pair? l) (or (= x (car l)) (in-ints? x (cdr l))))))

"The problem's relations, `k` states of those that change, and the loop."
(define make-ctx (subr cb-eff (model universe int int) ctx)
  (lambda (m u k copies)
    (let* ((c (make-circuit)) (n (list-length (extract u names)))
           (states (lambda ((var bool) (make (subr cb-eff () matrix)))
               (let ((a (the (arrayof matrix @cb) (make-array (if var k 1) (m-none 1 1)))))
                 (letrec ((go (subr cb-eff (int) (arrayof matrix @cb))
                            (lambda (j) (if (>= j (array-length a)) a (begin (array-set! a j (make)) (go (+ j 1)))))))
                   (go 0)))))
           (sig-rels (letrec ((go (subr cb-eff ((listof sig-info acyclic)) (listof rel acyclic))
                                (lambda (l)
                                  (if (null? l) nil
                                      (let ((b (tagcase (bound-of u (extract (car l) name)) (some b b) (none u2 (the sig-bound (product (name "") (lower nil) (upper nil)))))))
                                        (cons (product (name (extract (car l) name)) (arity 1) (var (extract (car l) var))
                                                       (mats (states (extract (car l) var)
                                                                     (lambda () (bound-matrix c n 1 (lambda ((t int)) (cond ((in-ints? t (extract b lower)) 1)
                                                                                                                            ((in-ints? t (extract b upper)) 0)
                                                                                                                            (else -1))))))))
                                              (go (cdr l))))))))
                       (go (extract m sigs))))
           (field-rels (letrec ((go (subr cb-eff ((listof field-info acyclic)) (listof rel acyclic))
                                  (lambda (l)
                                    (if (null? l) nil
                                        (let* ((f (car l))
                                               (rest (letrec ((cs (subr ro (datums) (listof ints acyclic))
                                                               (lambda (ds) (if (null? ds) nil (cons (column-atoms u (car ds) n) (cs (cdr ds)))))))
                                                      (cs (extract f cols))))
                                               (cols (if (string=? (extract f owner) "") rest (cons (column-atoms u (sym (extract f owner)) n) rest)))
                                               (k2 (list-length cols))
                                               ;; tuple t's atoms each in its column's
                                               (ok? (lambda ((t int)) (letrec ((go (subr ro (int (listof ints acyclic) int) bool)
                                                                            (lambda (t cs j) (if (null? cs) #t
                                                                                                 (and (in-ints? (quotient t (power n j)) (car cs))
                                                                                                      (go (modulo t (power n j)) (cdr cs) (- j 1)))))))
                                                               (go t cols (- k2 1))))))
                                          (cons (product (name (extract f name)) (arity k2) (var (extract f var))
                                                         (mats (states (extract f var) (lambda () (bound-matrix c n k2 (lambda ((t int)) (if (ok? t) 0 -1)))))))
                                                (go (cdr l))))))))
                         (go (extract m fields))))
           (loops (the ivec (make-array k c-false))))
      (begin
        (letrec ((go (subr cb-eff (int) unit) (lambda (j) (if (>= j k) #u (begin (array-set! loops j (c-input! c)) (go (+ j 1)))))))
          (go 0))
        (c-assert! c (c-exactly-one c (letrec ((go (subr cb-eff (int) ints) (lambda (j) (if (>= j k) nil (cons (array-ref loops j) (go (+ j 1)))))))
                                        (go 0))))
        (product (c c) (n n) (k k) (u copies) (loops loops) (rels (append sig-rels field-rels)) (model m) (universe u))))))

;;; ------------------------------------------------------------ what was found

(define atom-name (subr ro (ctx int) string)
  (lambda (x a) (letrec ((go (subr ro (strings int) string) (lambda (l i) (cond ((null? l) "?") ((= i 0) (car l)) (else (go (cdr l) (- i 1)))))))
                  (go (extract (extract x universe) names) a))))
"A tuple written a->b->c."
(define tuple-shown (subr ro (ctx int int) string)
  (lambda (x k t)
    (let ((n (extract x n)))
      (letrec ((go (subr ro (int int) strings)
                 (lambda (t j) (if (< j 0) nil (cons (atom-name x (quotient t (power n j))) (go (modulo t (power n j)) (- j 1)))))))
        (string-join (go t (- k 1)) "->")))))
(define matrix-shown (subr cb-eff (ctx matrix) string)
  (lambda (x m)
    (letrec ((go (subr cb-eff (int) strings)
               (lambda (t) (if (>= t (m-size m)) nil
                               (if (c-value (cx x) (m-ref m t)) (cons (tuple-shown x (m-arity m) t) (go (+ t 1))) (go (+ t 1)))))))
      (string-append "{" (string-append (string-join (go 0) ", ") "}")))))
(define state-shown (subr cb-eff (ctx int bool) string)
  (lambda (x i changing-only)
    (letrec ((go (subr cb-eff ((listof rel acyclic)) strings)
               (lambda (l) (cond ((null? l) nil)
                                 ((or (extract (car l) var) (not changing-only))
                                  (cons (string-append "  " (string-append (extract (car l) name) (string-append " = " (matrix-shown x (rel-at (car l) i))))) (go (cdr l))))
                                 (else (go (cdr l)))))))
      (string-join (go (extract x rels)) "\n"))))
"What was found: the relations; for a trace, those that do not change,
then each state's that do, and where the loop goes back to."
(define instance-shown (subr cb-eff (ctx) string)
  (lambda (x)
    (let ((k (extract x k)))
      (if (and (= k 1) (not (any-var? (extract x model)))) (state-shown x 0 #f)
          (let ((loop (letrec ((go (subr cb-eff (int) int) (lambda (l) (if (or (>= l k) (c-value (cx x) (loop-at x l))) l (go (+ l 1))))))
                        (go 0)))
                (static (letrec ((go (subr cb-eff ((listof rel acyclic)) strings)
                                   (lambda (l) (cond ((null? l) nil)
                                                     ((extract (car l) var) (go (cdr l)))
                                                     (else (cons (string-append "  " (string-append (extract (car l) name) (string-append " = " (matrix-shown x (rel-at (car l) 0))))) (go (cdr l))))))))
                          (go (extract x rels)))))
            (string-append
             (if (null? static) "" (string-append (string-join static "\n") "\n"))
             (string-join (letrec ((go (subr cb-eff (int) strings)
                                       (lambda (i) (if (>= i k) nil
                                                       (cons (string-append "state " (string-append (int->string i)
                                                                                                    (string-append (if (= i loop) " (the loop comes back here)" "")
                                                                                                                   (string-append ":\n" (state-shown x i #t)))))
                                                             (go (+ i 1)))))))
                            (go 0))
                          "\n")))))))

;;; ------------------------------------------------------------ commands

"A command's formula: for `run`, its predicate, its parameters found
(each a fresh relation, `one` of its type); for `check`, its assertion
false."
(define command-goal (subr ro (model datum) (productof (name string) (check bool) (goal datum) (params datums)))
  (lambda (m d)
    (let ((check (string=? (head d) "check")) (target (nth d 1)))
      (if check
          (let ((a (letrec ((go (subr ro ((listof named acyclic)) datum)
                              (lambda (l) (cond ((null? l) (error (string-append "casing: no assertion " (shown target))))
                                                ((string=? (extract (car l) name) (name-of target)) (extract (car l) body))
                                                (else (go (cdr l)))))))
                     (go (extract m asserts)))))
            (product (name (name-of target)) (check #t) (goal (the datum (list (sym "not") a))) (params nil)))
          (if (symbol? target)
              (tagcase (find-def m (symbol->string target))
                (none u (error (string-append "casing: no predicate " (shown target))))
                (some f (product (name (extract f name)) (check #f)
                                 (goal (the datum (cons target (letrec ((names (subr ro (datums) datums)
                                                                          (lambda (ds) (if (null? ds) nil
                                                                                           (append (letrec ((go (subr ro (datums) datums) (lambda (l) (if (null? (cdr l)) nil (cons (car l) (go (cdr l)))))))
                                                                                                     (go (items (car ds))))
                                                                                                   (names (cdr ds)))))))
                                                                 (names (extract f params))))))
                                 (params (extract f params)))))
              (product (name "") (check #f) (goal target) (params nil)))))))

"How deep past operators nest in `d`."
(define past-depth (subr ro (datum) int)
  (lambda (d)
    (if (not (pair? d)) 0
        (let ((h (head d))
              (inner (letrec ((go (subr ro (datum int) int) (lambda (l m) (if (pair? l) (go (cdr l) (max m (past-depth (car l)))) m))))
                       (go d 0))))
          (if (or (string=? h "once") (string=? h "historically") (string=? h "before") (string=? h "since") (string=? h "triggered"))
              (+ inner 1) inner)))))
"How deep past operators nest anywhere in a model's facts, predicates,
functions, assertions, and in `goal`."
(define model-past-depth (subr ro (model datum) int)
  (lambda (m goal)
    (letrec ((ds (subr ro (datums int) int) (lambda (l k) (if (null? l) k (ds (cdr l) (max k (past-depth (car l))))))))
      (max (past-depth goal)
           (max (ds (extract m facts) 0)
                (max (letrec ((go (subr ro ((listof def-info acyclic) int) int) (lambda (l k) (if (null? l) k (go (cdr l) (max k (past-depth (extract (car l) body))))))))
                       (go (extract m defs) 0))
                     (letrec ((go (subr ro ((listof named acyclic) int) int) (lambda (l k) (if (null? l) k (go (cdr l) (max k (past-depth (extract (car l) body))))))))
                       (go (extract m asserts) 0))))))))

"A command run: what it found, said."
(define run-command (subr cb-eff (model datum) string)
  (lambda (m d)
    (let* ((g (command-goal m d))
           (sc (read-scope m (cdr (cdr (items d)))))
           (u (make-universe m sc))
           ;; a run's parameters become sigs of their own: one atom of their type
           (m2 (letrec ((go (subr ro (datums model) model)
                          (lambda (ps m)
                            (if (null? ps) m
                                (let* ((p (items (car ps))) (t (car (reverse p))))
                                  (go (cdr ps)
                                      (letrec ((each (subr ro (datums model) model)
                                                 (lambda (ns m)
                                                   (if (null? (cdr ns)) m
                                                       (each (cdr ns)
                                                             (product (sigs (extract m sigs))
                                                                      (fields (append (extract m fields)
                                                                                      (list (product (name (string-append "$" (name-of (car ns)))) (owner "")
                                                                                                     (cols (list t)) (mult "set") (var #f) (region "")))))
                                                                      (facts (cons (the datum (list (sym "one") (sym (string-append "$" (name-of (car ns)))))) (extract m facts)))
                                                                      (defs (extract m defs)) (asserts (extract m asserts)) (commands (extract m commands))))))))
                                        (each p m))))))))
                 (go (extract g params) m)))
           (goal (if (null? (extract g params)) (extract g goal)
                     ;; (p x y) with x y the fresh relations
                     (the datum (cons (car (items (extract g goal)))
                                      (letrec ((go (subr ro (datums) datums) (lambda (l) (if (null? l) nil (cons (sym (string-append "$" (name-of (car l)))) (go (cdr l)))))))
                                        (go (cdr (items (extract g goal)))))))))
           (decls (declaration-facts m2))
           (temporal (any-var? m))
           (what (string-append (if (extract g check) "check " "run ") (if (string=? (extract g name) "") (shown (nth d 1)) (extract g name)))))
      (letrec ((try (subr cb-eff (int) string)
                 (lambda (k)
                   (if (> k (extract sc max-steps))
                       (string-append what (string-append (if (extract g check) ": no counterexample found" ": no instance found")
                                                          (scope-said sc temporal)))
                       (let* ((x (make-ctx m2 u k (+ 1 (model-past-depth m2 goal)))) (c (cx x)))
                         (begin
                           (letrec ((each (subr cb-eff (datums bool) unit)
                                      (lambda (l always) (if (null? l) #u
                                                             (begin (c-assert! c (form x (if always (the datum (list (sym "always") (car l))) (car l)) 0 nil))
                                                                    (each (cdr l) always))))))
                             (begin (each decls temporal)
                                    (each (extract u facts) temporal)
                                    (each (extract m2 facts) #f)
                                    (each (list goal) #f)))
                           (if (c-solve! c nil)
                               (string-append what (string-append (if (extract g check) ": counterexample found" ": instance found")
                                                                  (string-append (scope-said sc temporal)
                                                                                 (string-append (if temporal (string-append ", " (string-append (int->string k) (if (= k 1) " state" " states"))) "")
                                                                                                (string-append "\n" (instance-shown x))))))
                               (try (+ k 1)))))))))
        (try (extract sc min-steps))))))

(define scope-said (subr ro (scope bool) string)
  (lambda (s temporal)
    (string-append " (scope " (string-append (int->string (extract s default))
                                             (string-append (string-join (letrec ((go (subr ro ((listof scope-entry acyclic)) strings)
                                                                                    (lambda (l) (if (null? l) nil
                                                                                                    (cons (string-append (if (extract (car l) exact) ", exactly " ", ")
                                                                                                                         (string-append (int->string (extract (car l) count)) (string-append " " (extract (car l) name))))
                                                                                                          (go (cdr l)))))))
                                                                           (go (reverse (extract s sigs))))
                                                                         "")
                                                            (string-append (if temporal (string-append ", steps " (string-append (int->string (extract s min-steps)) (string-append ".." (int->string (extract s max-steps))))) "")
                                                                           ")"))))))

"Every command of a model, in order, each one's answer."
(define run-model (subr cb-eff (model) strings)
  (lambda (m) (letrec ((go (subr cb-eff (datums) strings) (lambda (l) (if (null? l) nil (cons (run-command m (car l)) (go (cdr l)))))))
                (go (extract m commands)))))
