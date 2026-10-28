;;; native.fx: a loop over integers compiled to machine code -- a kernel.
;;;
;;; A lambda whose body is only `if`, integers (constants, its parameters,
;;; the free variables of lambdas around it), the built-ins `+ - *` and
;;; `= < > <= >= zero?` on them, other constants returned, and calls of
;;; itself in tail position, becomes x86_64 code: Fixpt's `seal-code` and
;;; `native-procedure` (fixpt/docs/research/declared-conventions.md), its
;;; instructions made by Fixpt's encoder written in FX-26
;;; (`fx26:x86_64.fx`). The code is a leaf: it calls no routine of the
;;; runtime and allocates nothing, so no collection can happen while it
;;; runs, and it needs no frame nor stack map.
;;;
;;; It works on raw 64-bit integers in the suffix of a scratch bloblet,
;;; whose reference it is given (rdi; the suffix at rdi - 4):
;;;   slot 0  its result, an integer          slot 1  iterations left
;;;   slot 2  rsp on entry                    slot 3… its parameters, then
;;;                                                   the free variables
;;; and returns a status: 0, the integer in slot 0; 1, given up (an
;;; overflow) or 2, its iterations spent, the parameters in their slots
;;; being those of a call of itself to make the slow way; 3 + j, its
;;; `j`th constant. Since the body changes nothing, the call made the slow
;;; way from those parameters is the call it would have made. The machine
;;; (machine.fx's `s7-try-kernel`) checks, before it runs one, that what
;;; it was compiled for holds still: the built-ins where they were, the
;;; variable it calls itself through holding it, every input an integer.
;;;
;;; Each node's shape is a fixed sequence of instructions, its slots,
;;; constants and labels filled in: copy and patch, as stencils are.

(define x86 (load-input "fx26:x86_64.fx"))
(define-type x86-ins (listof int @k))

;;; ------------------------------------------------------------ assembly

"An instruction of a kernel: its bytes; a label; or a jump to one, of a
fixed size (jcc 6 bytes, jmp 5), so that a first pass places every label."
(define-type s7-asm (sumof (op x86-ins) (label int) (jcc (productof (cc int) (to int))) (jmp int)))
(define-type s7-asms (listof s7-asm @k))
(define-type s7-places (listof (productof (label int) (at int)) @k))
(define-effect s7-asm-eff (maxeff (read @k) (alloc @k) (read @globals) spin))

"Where label `l` is in `places`; 0 if it is not placed."
(define* s7-asm-place (subr (maxeff (read @k) spin) (s7-places int) int)
  (lambda (places l)
    (cond ((null? places) 0)
          ((= (extract (car places) label) l) (extract (car places) at))
          (else (s7-asm-place (cdr places) l)))))
"The labels of `is`, placed from byte `at`."
(define* s7-asm-places (subr s7-asm-eff (s7-asms int) s7-places)
  (lambda (is at)
    (if (null? is) nil
        (tagcase (car is)
          (op bs (s7-asm-places (cdr is) (+ at (list-length bs))))
          (label l (cons (product (label l) (at at)) (s7-asm-places (cdr is) at)))
          (jcc j (s7-asm-places (cdr is) (+ at 6)))
          (jmp l (s7-asm-places (cdr is) (+ at 5)))))))
"`bs`, then `rest`."
(define* s7-asm-copy (subr s7-asm-eff (x86-ins (listof int @k)) (listof int @k))
  (lambda (bs rest) (if (null? bs) rest (cons (car bs) (s7-asm-copy (cdr bs) rest)))))
"The bytes of `is`, from byte `at`, its labels at `places`."
(define* s7-asm-bytes (subr s7-asm-eff (s7-asms int s7-places) (listof int @k))
  (lambda (is at places)
    (if (null? is) nil
        (tagcase (car is)
          (op bs (s7-asm-copy bs (s7-asm-bytes (cdr is) (+ at (list-length bs)) places)))
          (label l (s7-asm-bytes (cdr is) at places))
          (jcc j (s7-asm-copy ((with x86 x86-jcc) (extract j cc) (- (s7-asm-place places (extract j to)) (+ at 6)))
                              (s7-asm-bytes (cdr is) (+ at 6) places)))
          (jmp l (s7-asm-copy ((with x86 x86-jmp) (- (s7-asm-place places l) (+ at 5)))
                              (s7-asm-bytes (cdr is) (+ at 5) places)))))))
"The machine code of `is`."
(define* s7-assemble (subr s7-asm-eff (s7-asms) (listof int @k))
  (lambda (is) (s7-asm-bytes is 0 (s7-asm-places is 0))))
"`a` then `b`."
(define* s7-asm++ (subr s7-asm-eff (s7-asms s7-asms) s7-asms)
  (lambda (a b) (if (null? a) b (cons (car a) (s7-asm++ (cdr a) b)))))

;;; ------------------------------------------------------------ the target

"Whether kernels can be made here: native code, x86_64's."
(define s7-native? bool
  (and (native-code?) (string=? (car (the (listof string @heap) (native-convention))) "(target x86_64)")))

;; Registers, as the encoder numbers them; conditions; arithmetic.
(define s7-rax int 0)
(define s7-rcx int 1)
(define s7-rsp int 4)
(define s7-rdi int 7)
"Slot `k` of the scratch suffix, from its reference."
(define* s7-slot-at (subr pure (int) int) (lambda (k) (- (* 8 k) 4)))
(define s7-first-param int 3)
(define s7-most-slots int 64)
;; Labels every kernel has.
(define s7-top-label int 0)
(define s7-bail-label int 1)
(define s7-spent-label int 2)

;;; ------------------------------------------------------------ compiling

"What compiling one lambda has found: whether it can be a kernel still;
its parameters; the free variables read, in slot order; the variable it
calls itself through; the built-ins done in line; the constants returned;
the next label."
(define s7-kn-ok (ref bool @sc) (new #t))
(define s7-kn-required (ref int @sc) (new 0))
(define s7-kn-frees (ref (listof (productof (depth int) (index int)) acyclic) @sc) (new nil))
(define s7-kn-self (ref (sumof (none unit) (local (productof (depth int) (index int))) (global s7-global)) @sc) (new (sum none #u)))
(define s7-kn-prims (ref (listof (productof (cell s7-global) (name string)) acyclic) @sc) (new nil))
(define s7-kn-consts (ref s7-values @sc) (new nil))
(define s7-kn-labels (ref int @sc) (new 3))

"Not a kernel, then; nothing to emit."
(define* s7-kn-no (subr s7-drive-eff () s7-asms)
  (lambda () (begin (set s7-kn-ok #f) nil)))
(define* s7-kn-label (subr s7-drive-eff () int)
  (lambda () (let ((l (get s7-kn-labels))) (begin (set s7-kn-labels (+ l 1)) l))))
"The index of `x` in `l` (by depth and index), from `i`; -1 if absent."
(define* s7-kn-index (subr spin ((listof (productof (depth int) (index int)) acyclic) int int int) int)
  (lambda (l d x i)
    (cond ((null? l) -1)
          ((and (= (extract (car l) depth) d) (= (extract (car l) index) x)) i)
          (else (s7-kn-index (cdr l) d x (+ i 1))))))
(define* s7-append-frees (subr (maxeff spin (alloc @sc)) ((listof (productof (depth int) (index int)) acyclic) (productof (depth int) (index int)))
                              (listof (productof (depth int) (index int)) acyclic))
  (lambda (l x) (if (null? l) (cons x nil) (cons (car l) (s7-append-frees (cdr l) x)))))
"The slot of local `d`, `i`: a parameter, or a free variable (given one if
it has none yet); -1 if it is neither."
(define* s7-kn-var-slot (subr s7-drive-eff (int int) int)
  (lambda (d i)
    (cond ((= d 0) (if (< i (get s7-kn-required)) (+ s7-first-param i) -1))
          (else (let ((j (s7-kn-index (get s7-kn-frees) d i 0)))
                  (if (>= j 0) (+ (+ s7-first-param (get s7-kn-required)) j)
                      (let ((n (list-length (get s7-kn-frees))))
                        (begin (set s7-kn-frees (s7-append-frees (get s7-kn-frees) (product (depth d) (index i))))
                               (+ (+ s7-first-param (get s7-kn-required)) n)))))))))
"The built-in `n` names, if it is one a kernel does in line and global `g`
holds it now (noted, to be checked when the kernel runs); \"\" if not."
(define* s7-kn-prim (subr s7-drive-eff (s7-node int) string)
  (lambda (n nargs)
    (tagcase (extract n form)
      (n-global g
        (tagcase (get (extract g value))
          (prim p (let ((name (extract p name)))
                    (if (or (and (= nargs 2) (or (string=? name "+") (string=? name "-") (string=? name "*")
                                                 (string=? name "=") (string=? name "<") (string=? name ">")
                                                 (string=? name "<=") (string=? name ">=")))
                            (and (= nargs 1) (string=? name "zero?")))
                        (begin (set s7-kn-prims (cons (product (cell g) (name name)) (get s7-kn-prims))) name)
                        "")))
          (else y "")))
      (else y ""))))
"Whether `x` is an integer a 32-bit immediate holds."
(define* s7-kn-imm (subr pure (s7-node) (sumof (no unit) (yes int)))
  (lambda (x)
    (tagcase (extract x form)
      (n-const v (tagcase v (int i (if (and (>= i -2147483648) (< i 2147483648)) (sum yes i) (sum no #u))) (else y (sum no #u))))
      (else y (sum no #u)))))
"The slot `x` is read from, if it is a variable; -1 if not."
(define* s7-kn-var (subr s7-drive-eff (s7-node) int)
  (lambda (x) (tagcase (extract x form) (n-local l (s7-kn-var-slot (extract l depth) (extract l index))) (else y -1))))

"Code leaving the integer `x` is in rax: a constant, a variable, or
`+ - *` of such; an overflow given up."
(define* s7-kn-int (subr s7-drive-eff (s7-node) s7-asms)
  (lambda (x)
    (let ((op (lambda ((bs x86-ins)) (the s7-asm (sum op bs)))))
      (tagcase (extract x form)
        (n-const v (tagcase v
                     (int i (if (and (> i -1152921504606846976) (< i 1152921504606846976))
                                (the s7-asms (list (op ((with x86 x86-mov-imm) s7-rax i))))
                                (s7-kn-no)))
                     (else y (s7-kn-no))))
        (n-local l (let ((s (s7-kn-var-slot (extract l depth) (extract l index))))
                     (if (< s 0) (s7-kn-no) (the s7-asms (list (op ((with x86 x86-load) s7-rax s7-rdi (s7-slot-at s))))))))
        (n-call c
          (let ((args (extract c args)))
            (if (not (= (list-length args) 2)) (s7-kn-no)
                (let* ((name (s7-kn-prim (extract c op) 2))
                       (code (cond ((string=? name "+") 0) ((string=? name "-") 5) ((string=? name "*") -1) (else -2))))
                  (if (= code -2) (s7-kn-no)
                      (let* ((a (car args)) (b (car (cdr args)))
                             (ac (s7-kn-int a))
                             (bail (the s7-asms (list (sum jcc (product (cc 0) (to s7-bail-label))))))
                             (bv (s7-kn-var b)))
                        (cond
                          ;; `op rax, imm`
                          ((and (>= code 0) (tagcase (s7-kn-imm b) (yes i #t) (no u #f)))
                           (s7-asm++ ac (cons (op ((with x86 x86-alu-imm) code s7-rax (tagcase (s7-kn-imm b) (yes i i) (no u 0)))) bail)))
                          ;; `op rax, [slot]`
                          ((and (>= code 0) (>= bv 0))
                           (s7-asm++ ac (cons (op ((with x86 x86-alu-rm) code s7-rax s7-rdi (s7-slot-at bv))) bail)))
                          ;; `b` into rcx by the stack, then `op rax, rcx`
                          (else
                           (s7-asm++ ac
                             (cons (op ((with x86 x86-push) s7-rax))
                                   (s7-asm++ (s7-kn-int b)
                                     (cons (op ((with x86 x86-mov) s7-rcx s7-rax))
                                           (cons (op ((with x86 x86-pop) s7-rax))
                                                 (cons (op (if (< code 0) ((with x86 x86-imul) s7-rax s7-rcx)
                                                               ((with x86 x86-alu) code s7-rax s7-rcx)))
                                                       bail))))))))))))))
        (else y (s7-kn-no))))))

"Code going to label `else` unless test `x` is true: `= < > <= >=` of two
integers, or `zero?` of one."
(define* s7-kn-test (subr s7-drive-eff (s7-node int) s7-asms)
  (lambda (x else)
    (let ((op (lambda ((bs x86-ins)) (the s7-asm (sum op bs)))))
      (tagcase (extract x form)
        (n-call c
          (let* ((args (extract c args)) (nargs (list-length args)) (name (s7-kn-prim (extract c op) nargs)))
            (cond
              ((string=? name "zero?")
               (s7-asm++ (s7-kn-int (car args))
                         (the s7-asms (list (op ((with x86 x86-test) s7-rax s7-rax)) (sum jcc (product (cc 5) (to else)))))))
              ((= nargs 2)
               ;; The condition under which the test is false.
               (let ((false-cc (cond ((string=? name "=") 5) ((string=? name "<") 13) ((string=? name ">") 14)
                                     ((string=? name "<=") 15) ((string=? name ">=") 12) (else -1))))
                 (if (< false-cc 0) (s7-kn-no)
                     (let* ((a (car args)) (b (car (cdr args))) (bv (s7-kn-var b))
                            (jump (the s7-asms (list (sum jcc (product (cc false-cc) (to else)))))))
                       (cond
                         ((tagcase (s7-kn-imm b) (yes i #t) (no u #f))
                          (s7-asm++ (s7-kn-int a) (cons (op ((with x86 x86-alu-imm) 7 s7-rax (tagcase (s7-kn-imm b) (yes i i) (no u 0)))) jump)))
                         ((>= bv 0)
                          (s7-asm++ (s7-kn-int a) (cons (op ((with x86 x86-alu-rm) 7 s7-rax s7-rdi (s7-slot-at bv))) jump)))
                         (else
                          (s7-asm++ (s7-kn-int a)
                            (cons (op ((with x86 x86-push) s7-rax))
                                  (s7-asm++ (s7-kn-int b)
                                    (cons (op ((with x86 x86-mov) s7-rcx s7-rax))
                                          (cons (op ((with x86 x86-pop) s7-rax))
                                                (cons (op ((with x86 x86-alu) 7 s7-rax s7-rcx)) jump))))))))))))
              (else (s7-kn-no)))))
        (else y (s7-kn-no))))))

"Whether `op`, called with `nargs` arguments in tail position, is the
lambda calling itself: the variable it calls through noted the first
time, and the same one every time after."
(define* s7-kn-self? (subr s7-drive-eff (s7-node int) bool)
  (lambda (op nargs)
    (and (= nargs (get s7-kn-required))
         (tagcase (extract op form)
           (n-local l (and (> (extract l depth) 0)
                           (tagcase (get s7-kn-self)
                             (none u (begin (set s7-kn-self (sum local (product (depth (extract l depth)) (index (extract l index))))) #t))
                             (local m (and (= (extract m depth) (extract l depth)) (= (extract m index) (extract l index))))
                             (global g #f))))
           (n-global g (and (tagcase (get (extract g value)) (prim p #f) (else y #t))
                            (tagcase (get s7-kn-self)
                              (none u (begin (set s7-kn-self (sum global g)) #t))
                              (global h (eq? (extract g value) (extract h value)))
                              (local m #f))))
           (else y #f)))))

"`args` evaluated, pushed, then popped into the parameters' slots."
(define* s7-kn-args (subr s7-drive-eff (s7-nodes int) s7-asms)
  (lambda (args k)
    (let ((op (lambda ((bs x86-ins)) (the s7-asm (sum op bs)))))
      (if (null? args) nil
          (s7-asm++ (s7-kn-int (car args))
                    (cons (op ((with x86 x86-push) s7-rax))
                          (s7-asm++ (s7-kn-args (cdr args) (+ k 1))
                                    (the s7-asms (list (op ((with x86 x86-pop) s7-rcx))
                                          (op ((with x86 x86-store) s7-rdi (s7-slot-at (+ s7-first-param k)) s7-rcx)))))))))))

(define* s7-append-value (subr (maxeff spin (alloc @sc)) (s7-values s7-value) s7-values)
  (lambda (l v) (if (null? l) (cons v nil) (cons (car l) (s7-append-value (cdr l) v)))))
"Code for `x` in tail position: it returns, or loops."
(define* s7-kn-tail (subr s7-drive-eff (s7-node) s7-asms)
  (lambda (x)
    (let ((op (lambda ((bs x86-ins)) (the s7-asm (sum op bs))))
          (status (lambda ((s int)) (the s7-asms (list (sum op ((with x86 x86-mov-imm) s7-rax (* 8 s))) (sum op ((with x86 x86-ret))))))))
      (tagcase (extract x form)
        (n-if i (let ((else (s7-kn-label)))
                  (s7-asm++ (s7-kn-test (extract i test) else)
                            (s7-asm++ (s7-kn-tail (extract i then))
                                      (cons (sum label else) (s7-kn-tail (extract i else)))))))
        (n-call c (if (s7-kn-self? (extract c op) (list-length (extract c args)))
                      (s7-asm++ (s7-kn-args (extract c args) 0)
                                (the s7-asms (list (op ((with x86 x86-alu-mi) 5 s7-rdi (s7-slot-at 1) 1))
                                      (sum jcc (product (cc 4) (to s7-spent-label)))
                                      (sum jmp s7-top-label))))
                      (s7-asm++ (s7-kn-int x)
                                (cons (op ((with x86 x86-store) s7-rdi (s7-slot-at 0) s7-rax)) (status 0)))))
        (n-const v (tagcase v
                     (int i (s7-asm++ (s7-kn-int x) (cons (op ((with x86 x86-store) s7-rdi (s7-slot-at 0) s7-rax)) (status 0))))
                     (else y (let ((j (list-length (get s7-kn-consts))))
                               (begin (set s7-kn-consts (s7-append-value (get s7-kn-consts) v))
                                      (status (+ 3 j)))))))
        (else y (s7-asm++ (s7-kn-int x) (cons (op ((with x86 x86-store) s7-rdi (s7-slot-at 0) s7-rax)) (status 0))))))))

"Whether a call of itself is somewhere in tail position in `x`: only then
is a kernel worth making."
(define* s7-kn-loops? (subr spin (s7-node) bool)
  (lambda (x)
    (tagcase (extract x form)
      (n-if i (or (s7-kn-loops? (extract i then)) (s7-kn-loops? (extract i else))))
      (n-call c (tagcase (extract (extract c op) form) (n-local l (> (extract l depth) 0)) (n-global g #t) (else y #f)))
      (else y #f))))

"The bytes `bs` from byte `at` of `b`'s suffix."
(define* s7-kn-put (subr (maxeff (write @sc) (read @sc) (read @k) spin) (s7-scratch int (listof int @k)) unit)
  (lambda (b at bs) (if (null? bs) #u (begin (bloblet-set-byte! b at (car bs)) (s7-kn-put b (+ at 1) (cdr bs))))))

"The name of the built-in global `op` holds, if it is one a kernel does in
line with `nargs` arguments; \"\" if not. Nothing noted."
(define* s7-kn-prim-name (subr (maxeff spin (read @sc) (read @globals)) (s7-node int) string)
  (lambda (op nargs)
    (tagcase (extract op form)
      (n-global g
        (tagcase (get (extract g value))
          (prim p (let ((name (extract p name)))
                    (if (or (and (= nargs 2) (or (string=? name "+") (string=? name "-") (string=? name "*")
                                                 (string=? name "=") (string=? name "<") (string=? name ">")
                                                 (string=? name "<=") (string=? name ">=")))
                            (and (= nargs 1) (string=? name "zero?")))
                        name "")))
          (else y "")))
      (else y ""))))
"Whether every node of `x` is one a kernel can do: as `s7-kn-tail` (if
`tail?`) or `s7-kn-int` and `s7-kn-test` take them, but for the slots and
labels. Asked before a kernel is wanted, so that a lambda that cannot have
one is never made to look for it."
(define* s7-kn-fits? (subr (maxeff spin (read @sc) (read @globals)) (s7-node bool) bool)
  (lambda (x tail?)
    (letrec ((all (subr (maxeff spin (read @sc) (read @globals)) (s7-nodes) bool)
               (lambda (ns) (or (null? ns) (and (s7-kn-fits? (car ns) #f) (all (cdr ns)))))))
      (tagcase (extract x form)
        (n-const v (or tail? (tagcase v (int i #t) (else y #f))))
        (n-local l #t)
        (n-if i (and tail? (s7-kn-fits? (extract i test) #f) (s7-kn-fits? (extract i then) #t) (s7-kn-fits? (extract i else) #t)))
        (n-call c (let ((n (list-length (extract c args))))
                    (and (or (not (string=? (s7-kn-prim-name (extract c op) n) ""))
                             (and tail? (tagcase (extract (extract c op) form)
                                          (n-local l (> (extract l depth) 0))
                                          (n-global g (tagcase (get (extract g value)) (prim p #f) (else y #t)))
                                          (else y #f))))
                         (all (extract c args)))))
        (else y #f)))))

"Lambdas whose kernels are wanted, each with where its kernel goes: made
by `s7-make-kernels!` between slices, since making one is beyond what the
machine's own code may do (value.fx's `s7-drive-eff`)."
(define s7-kernels-wanted (ref (listof (productof (info s7-lambda) (into (ref (listof s7-kernel acyclic) @sc))) acyclic) @sc) (new nil))
"A kernel of `l` wanted, put in `into` once made, if it might be one:\nwhether it was."
(define* s7-want-kernel! (subr s7-eff (s7-lambda (ref (listof s7-kernel acyclic) @sc)) bool)
  (lambda (l into)
    (and s7-native? (not (extract l rest)) (> (extract l required) 0) (= (extract l size) (extract l required))
         (s7-kn-loops? (extract l body))
         (s7-kn-fits? (extract l body) #t)
         (begin (set s7-kernels-wanted (cons (product (info l) (into into)) (get s7-kernels-wanted))) #t))))
"Lambda `l` as a kernel, if it can be one."
(define* s7-kernel-of (subr s7-drive-eff (s7-lambda) (listof s7-kernel acyclic))
  (lambda (l)
    (if (or (not s7-native?) (extract l rest) (not (= (extract l size) (extract l required)))
            (not (s7-kn-loops? (extract l body))))
        nil
        (begin
          (set s7-kn-ok #t) (set s7-kn-required (extract l required)) (set s7-kn-frees nil)
          (set s7-kn-self (sum none #u)) (set s7-kn-prims nil) (set s7-kn-consts nil) (set s7-kn-labels 3)
          (let* ((op (lambda ((bs x86-ins)) (the s7-asm (sum op bs))))
                 (body (s7-kn-tail (extract l body)))
                 (slots (+ (+ s7-first-param (extract l required)) (list-length (get s7-kn-frees)))))
            (if (or (not (get s7-kn-ok)) (> slots s7-most-slots)
                    (tagcase (get s7-kn-self) (none u #t) (else y #f)))
                nil
                (let* ((is (the s7-asms (cons (op ((with x86 x86-store) s7-rdi (s7-slot-at 2) s7-rsp))
                                 (cons (sum label s7-top-label)
                                       (s7-asm++ body
                                                 (the s7-asms (list (sum label s7-bail-label)
                                                       (op ((with x86 x86-load) s7-rsp s7-rdi (s7-slot-at 2)))
                                                       (op ((with x86 x86-mov-imm) s7-rax 8))
                                                       (op ((with x86 x86-ret)))
                                                       (sum label s7-spent-label)
                                                       (op ((with x86 x86-mov-imm) s7-rax 16))
                                                       (op ((with x86 x86-ret))))))))))
                       (bs (s7-assemble is))
                       (b (the s7-scratch (make-bloblet (list-length bs)))))
                  (begin
                    (s7-kn-put b 0 bs)
                    (list (product (code (the s7-kernel-code (native-procedure (seal-code b))))
                                   (frees (get s7-kn-frees)) (self (get s7-kn-self))
                                   (prims (get s7-kn-prims)) (consts (get s7-kn-consts))))))))))))
"The kernels wanted, made."
(define* s7-make-kernels! (subr s7-drive-eff () unit)
  (lambda ()
    (let ((ws (get s7-kernels-wanted)))
      (if (null? ws) #u
          (begin (set s7-kernels-wanted nil)
                 (letrec ((go (subr s7-drive-eff ((listof (productof (info s7-lambda) (into (ref (listof s7-kernel acyclic) @sc))) acyclic)) unit)
                                (lambda (ws) (if (null? ws) #u
                                                 (begin (set (extract (car ws) into) (s7-kernel-of (extract (car ws) info)))
                                                        (go (cdr ws)))))))
                   (go ws)))))))
