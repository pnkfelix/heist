; A library importing another, found by its name.
(define-library (geometry shapes)
  (export circle-area count)
  (import (scheme base) (only (geometry point) dist2 origin) (prefix (geometry point) pt:))
  (begin
    (define count 0)
    (define (circle-area center edge)
      (set! count (+ count 1))
      (* 355/113 (dist2 center edge)))))
