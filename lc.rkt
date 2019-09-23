
#lang racket
(provide (all-defined-out))
(struct node(t1 t2) #:transparent)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-syntax lc
  (syntax-rules (: <- @)
    [(lc expr : var <- drawn-from) (map (lambda (var) expr) drawn-from)]
    [(lc expr : @ guard) (if guard (list expr) `())]
    [(lc expr : @ guard  qualifier ...) 
     (append* (lc (lc expr : qualifier ...) : @ guard))]
    [(lc expr : var <- drawn-from  qualifier ...) 
     (append* (lc (lc expr :  qualifier ... ) : var <- drawn-from))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(define-syntax mycond
;  (syntax-rules (> <);
;    [(mycond < bexp exp > more ...) (if bexp exp (mycond more ...))]
;    [(mycond < exp >) exp]))                                 ;
;
;(define (fact n)
;  (mycond < (= n 0) 1 >
;          < (* n (fact (- n 1))) >))
;
;
;(define (fib n)
 ; (mycond < (= n 0) 0 >
  ;        < (= n 1) 1 >
   ;       < (+ (fib (- n 1)) (fib (- n 2))) >))
  ;
;
;
;
;(define (cprod l)
 ; (cond [(null? l) '(())]
  ;      [else
   ;      (lc (cons x y) :
    ;         x <- (car l)
     ;        y <- (cprod (cdr l)))]))
;
;(define (qsort l)
 ; (cond [(null? l) '()]
  ;      [else (let ((lows (lc x : x <- (cdr l) @(<= x (car l))))
   ;                 (highs (lc x : x <- (cdr l) @(> x (car l)))))
    ;            (append (qsort lows) (list (car l))
     ;                   (qsort highs)))]))
;
;
;(define-syntax list-of-three
 ; (syntax-rules (@ <-)
  ;  [(list-of-three b @ c ... <- d) `(b d c ...)]))
;
;(define x (list-of-three  7 @  <- 5))
;
;
;(define-syntax for
 ; (syntax-rules (:)
  ;  [(for init : condition : step : statements)
   ;    (begin
    ;     init
     ;    (define (iter)
      ;     (cond [condition (begin statements
       ;                            step
        ;                           (iter))]))
         ;(iter))]))
;
;(define i 0)
;(define sum 0)
;(for (begin
 ;      (set! i 0)
  ;     (set! sum 0)) :
;  (;< i 10) :
 ; (s;et! i (+ i 1)) :
  ;(se;t! sum (+ sum i)))
;
;;(begin
;  (begin
;    (define x 0)
;    (define sum 0))
;  (define (iteefine r)
;    (cond [(< x 10) (begin
;                      (set! sum (+ sum x))
;                      (set! x (+ x 1))
;                      (iter))]))
;  (iter))

;Write a  macro  to implement  C-style  while loops  in drracket.  In
;general, the syntax of while is:
;
;   (while {boolean-expression} {one-or-more-statements})
;
;The example below illustrates the use of the while macro:
;
;    (define i 10)
;    (define y 0)
;    (while (> i 0) 
;       (set! y (+ y i))
;       (set! i (- i 1)))

(define fac
  ((lambda (f)  (lambda (n) (if (= n 0) 1 (* n ((f f) (- n 1))))))
  (lambda (f)  (lambda (n) (if (= n 0) 1 (* n ((f f) (- n 1))))))))
  
  
  