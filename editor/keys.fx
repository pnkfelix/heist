;;; keys.fx: keys, their names, and decoding them from terminal input
;;; (yank's `(yank keys)`, cahoots c337e2a).
;;;
;;; A key is a character, for a plain key that inserts itself (#\a,
;;; #\space, #\λ), or a symbol naming anything else, written as Emacs
;;; writes it: C-a, M-x, C-M-f, RET, TAB, DEL, ESC, up, C-left, f5
;;; (<up>, C-<left>, <f5> in kbd notation). Meta and control combine in
;;; the order C-M-.
;;;
;;; `(kbd "C-x C-f")` turns Emacs's notation into a list of keys, and
;;; `key->string` turns one back.

(define-type key (union char symbol))
(define-type keys (listof key acyclic))
"A source of bytes: the next byte, or #f if none comes within the
milliseconds given. A terminal's, or a test's list."
(define-type (byte-source (e effect)) (subr e (int) (union false int)))

(hide
  (define symbol-append (subr pure (string string) symbol)
    (lambda (prefix name) (string->symbol (string-append prefix name))))

  ;; The length of the modifiers (C-, M-, S-) a key's name starts with.
  (define modifiers-length (subr spin (string) int)
    (lambda (name)
      (letrec ((go (subr spin (int) int)
                 (lambda (i)
                   (if (and (< (+ i 2) (string-length name))
                            (char-in? (string-ref name i) "CMS")
                            (char=? #\- (string-ref name (+ i 1))))
                       (go (+ i 2))
                       i))))
        (go 0))))

  (define bracketed? (subr pure (string) bool)
    (lambda (s)
      (let ((n (string-length s)))
        (and (> n 2) (char=? #\< (string-ref s 0)) (char=? #\> (string-ref s (- n 1)))))))

  (define name->key (subr spin (string) key)
    (lambda (name)
      (let* ((n (string-length name)) (m (modifiers-length name)) (base (substring name m n)))
        (cond ((= n 1) (string-ref name 0))
              ((string=? name "SPC") #\space)
              ((bracketed? base)
               (string->symbol (string-append (substring name 0 m)
                                              (substring base 1 (- (string-length base) 1)))))
              (else (string->symbol name))))))

  (define split-on-spaces (subr spin (string) (listof string acyclic))
    (lambda (s)
      (letrec ((go (subr spin (int int (listof string acyclic)) (listof string acyclic))
                 (lambda (i start acc)
                   (cond ((= i (string-length s))
                          (reverse (if (> i start) (the (listof string acyclic) (cons (substring s start i) acc)) acc)))
                         ((char=? #\space (string-ref s i))
                          (go (+ i 1) (+ i 1) (if (> i start) (the (listof string acyclic) (cons (substring s start i) acc)) acc)))
                         (else (go (+ i 1) start acc))))))
        (go 0 0 nil))))

  ;; How long to wait for the rest of an escape sequence.
  (define escape-timeout int 25)

  (define key-name (subr pure (key) string)
    (lambda (k)
      (typecase k
        (char c (if (char=? c #\space) "SPC" (char->string c)))
        (else y (symbol->string y)))))

  (define add-meta (subr pure (key) key)
    (lambda (k)
      (let ((name (key-name k)))
        (if (and (> (string-length name) 2) (string=? "C-" (substring name 0 2)))
            (symbol-append "C-M-" (substring name 2 (string-length name)))
            (symbol-append "M-" name)))))

  (define add-modifiers (subr pure (symbol int) key)
    (lambda (k mods)
      (string->symbol
       (string-append (if (= 1 (remainder (quotient mods 4) 2)) "C-" "")
                      (if (= 1 (remainder (quotient mods 2) 2)) "M-" "")
                      (if (= 1 (remainder mods 2)) "S-" "")
                      (symbol->string k)))))

  (define tilde-key (subr pure (int) (union false symbol))
    (lambda (n)
      (case n
        ((1 7) 'home) ((2) 'insert) ((3) 'delete) ((4 8) 'end)
        ((5) 'prior) ((6) 'next)
        ((15) 'f5) ((17) 'f6) ((18) 'f7) ((19) 'f8) ((20) 'f9)
        ((21) 'f10) ((23) 'f11) ((24) 'f12)
        (else #f))))

  ;; ESC [ params final. Params are numbers separated by semicolons; the
  ;; second, if present, holds modifiers (xterm's 1 + bits: 1 shift, 2
  ;; meta, 4 control).
  (define csi-key (subr spin (char (listof int acyclic)) key)
    (lambda (final params)
      (let ((base (the (union false symbol)
                       (case final
                         ((#\A) 'up) ((#\B) 'down) ((#\C) 'right) ((#\D) 'left)
                         ((#\H) 'home) ((#\F) 'end) ((#\Z) 'backtab)
                         ((#\~) (tilde-key (if (pair? params) (car params) 0)))
                         (else #f))))
            (mods (if (and (pair? params) (pair? (cdr params))) (- (car (cdr params)) 1) 0)))
        (typecase base
          (symbol y (add-modifiers y mods))
          (else z 'unknown))))))

"Emacs's notation as keys: \"C-x C-f\" => (C-x C-f); \"a b\" => (#\\a #\\b);
\"<up>\" => (up); \"C-<left>\" => (C-left)."
(define kbd (subr spin (string) keys)
  (lambda (s)
    (letrec ((go (subr spin ((listof string acyclic)) keys)
               (lambda (ns) (if (null? ns) nil (cons (name->key (car ns)) (go (cdr ns)))))))
      (go (split-on-spaces s)))))

"As Emacs writes a key: a function key's name in brackets, after its
modifiers (<f5>, C-<left>)."
(define key->string (subr spin (key) string)
  (lambda (k)
    (typecase k
      (char c (if (char=? c #\space) "SPC" (char->string c)))
      (else y
       (let* ((s (symbol->string y)) (m (modifiers-length s)) (base (substring s m (string-length s))))
         (if (or (= 1 (string-length base))
                 (string=? base "RET") (string=? base "TAB") (string=? base "DEL")
                 (string=? base "ESC") (string=? base "SPC"))
             s
             (string-append (substring s 0 m) "<" base ">")))))))

(define keys->string (subr spin (keys) string)
  (lambda (ks)
    (letrec ((go (subr spin (keys string) string)
               (lambda (ks acc) (if (null? ks) acc (go (cdr ks) (string-append acc " " (key->string (car ks))))))))
      (if (null? ks) "" (go (cdr ks) (key->string (car ks)))))))

(define key=? (subr pure (key key) bool)
  (lambda (a b)
    (typecase a
      (char x (typecase b (char y (char=? x y)) (else z #f)))
      (else x (typecase b (char z #f) (else y (symbol=? x y)))))))

"The Meta version of a key: x => M-x, C-f => C-M-f, up => M-up."
(define meta-key (subr pure (key) key) (lambda (k) (add-meta k)))

"The next key from `next-byte`, or #f if no input comes within `timeout`
milliseconds."
(define read-key (poly ((e effect)) (subr (maxeff e spin) ((byte-source e) int) (union false key)))
  (plambda ((e effect))
    (lambda (next-byte timeout)
      (letrec ((byte->key (subr (maxeff e spin) (int) key)
                 (lambda (b)
                   (cond ((= b 13) 'RET)
                         ((= b 9) 'TAB)
                         ((= b 127) 'DEL)
                         ((= b 27) 'ESC)
                         ((= b 0) 'C-SPC)
                         ((< b 32) (symbol-append "C-" (char->string (char-downcase (integer->char (+ b 64))))))
                         ((< b 128) (integer->char b))
                         (else (utf8 b)))))
               ;; The rest of a UTF-8 character whose first byte is `b`.
               (utf8 (subr (maxeff e spin) (int) key)
                 (lambda (b)
                   (let ((count (cond ((>= b 240) 3) ((>= b 224) 2) (else 1)))
                         (first (cond ((>= b 240) (remainder b 8)) ((>= b 224) (remainder b 16)) (else (remainder b 32)))))
                     (letrec ((go (subr (maxeff e spin) (int int) key)
                                (lambda (i cp)
                                  (if (= i count)
                                      (if (and (> cp 0) (< cp 1114112) (not (and (>= cp 55296) (< cp 57344))))
                                          (integer->char cp)
                                          'unknown)
                                      (let ((nb (next-byte escape-timeout)))
                                        (typecase nb
                                          (int v (go (+ i 1) (+ (* cp 64) (remainder v 64))))
                                          (else z 'unknown)))))))
                       (go 0 first)))))
               (escape (subr (maxeff e spin) () key)
                 (lambda ()
                   (let ((b (next-byte escape-timeout)))
                     (typecase b
                       (int v (cond ((= v 91) (csi nil -1))           ; ESC [
                                    ((= v 79) (ss3))                  ; ESC O
                                    (else (add-meta (byte->key v)))))
                       (else z 'ESC)))))
               ;; ESC O x: what some terminals send for arrows and F1-F4.
               (ss3 (subr (maxeff e spin) () key)
                 (lambda ()
                   (let ((b (next-byte escape-timeout)))
                     (typecase b
                       (int v (case (integer->char v)
                              ((#\A) 'up) ((#\B) 'down) ((#\C) 'right) ((#\D) 'left)
                              ((#\H) 'home) ((#\F) 'end)
                              ((#\P) 'f1) ((#\Q) 'f2) ((#\R) 'f3) ((#\S) 'f4)
                              (else 'M-O)))
                       (else z 'M-O)))))
               ;; Params so far, last first, and the number being read (-1: none).
               (csi (subr (maxeff e spin) ((listof int acyclic) int) key)
                 (lambda (params n)
                   (let ((b (next-byte escape-timeout)))
                     (typecase b
                       (int v (cond ((and (>= v 48) (<= v 57)) (csi params (+ (* 10 (max n 0)) (- v 48))))
                                    ((= v 59) (csi (the (listof int acyclic) (cons (max n 0) params)) -1))
                                    (else (csi-key (integer->char v) (reverse (if (>= n 0) (the (listof int acyclic) (cons n params)) params))))))
                       (else z (string->symbol "M-[")))))))
        (let ((b (next-byte timeout)))
          (typecase b
            (int v (if (= v 27) (escape) (byte->key v)))
            (else z #f)))))))
