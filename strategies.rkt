#lang racket

;; You can require more modules of your choice.
(require racket/list
         (prefix-in utils: "utils.rkt")
         (prefix-in stats: "statistics.rkt")
         "lc.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                     ;;
;; Strategies                                                                          ;;
;; ==========                                                                          ;;
;; For the purpose of this assignment, just the `etai` strategy is expected, since     ;;
;; we have dictionary-closure and secret-word-enumeration to leap-frog to the right    ;;
;; key. This technique would fail for harder keys which are arbitrary permutations of  ;;
;; the alphabet. We will be forced to explore many more strategies (along with         ;;
;; dictionary-closure of course).                                                      ;;
;;                                                                                     ;;
;; Strategies to guess substitutions for the key using statistical information about   ;;
;; - the English language from utils.rkt                                               ;;
;; - the cipher text      from statistics.rkt                                          ;;
;;                                                                                     ;;
;; Follow the function signature as indicated below. Deviations will make it           ;;
;; impossible for automatic grading of your submission.                                ;;
;; Moreover, we do not expect your strategies to require any more/different            ;;
;; arguments. Note that you recieve the key as argument, so you can at the very        ;;
;; least ensure that all the substitutions are monoalphabetic wrt this key.            ;;
;;                                                                                     ;;
;; Signature:                                                                          ;;
;; ```                                                                                 ;;
;; (define (my-fundoo-strategy key)                                                    ;;
;;   ;; Make use of `utils:ciphertext`, `utils:cipher-word-list`                       ;;
;;   ...)                                                                              ;;
;; ```                                                                                 ;;
;;                                                                                     ;;
;; Substitutions                                                                       ;;
;; -------------                                                                       ;;
;; In order to extend the key incrementally, we use `utils:add-substitution` to        ;;
;; extend a given key with a substitution.                                             ;;
;;                                                                                     ;;
;; A substitution is a list of pairs, each pair mapping a plaintext char to a          ;;
;; ciphertext char. For example, to extend the key with T -> a and O -> r              ;;
;; (simultaneously), we use the substitution:                                          ;;
;; ```                                                                                 ;;
;; (list (cons #\T #\a) (cons #\O #\r))                                                ;;
;; ```                                                                                 ;;
;; For a single substitution use a singleton list (containing just one pair).          ;;
;;                                                                                     ;;
;; **CAUTION**                                                                         ;;
;; -----------                                                                         ;;
;; 1. Note that add-substitution does not do sanity checks on the substitution and use ;;
;;    of `utils:is-monoalphabetic` is recommended to ensure that you don't             ;;
;;    inadvertently create invalid keys.                                               ;;
;; 2. You must provide a list called `compositions` in this module.                    ;;
;;                                                                                     ;;
;; See docs in "utils.rkt" for more information.                                       ;;
;;                                                                                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; You must add "public" functions of this module to this list.
(provide etai
         ;; Some more suggested strategies:
         
         ;; common-words-double
         ;; bigrams
         ;; common-initial-letters
         ;; common-final-letters
         ;; common-words-triple
         ;; trigrams
         ;; common-double-letters
         ;; common-words-quadruple
         ;; quadgrams
         
         ;; lists of strategies
         composition)

;; A strategy that uses some statistical information to generate potential
;; substitutions for E, T, A and I.
;; Refer the assignment manual for tips on developing this strategy. You can
;; interact with our etai with the executable we provide.
(define (zip l1 l2)
  (match (cons l1 l2)
    [(cons '() l2) '()]
    [(cons l1 '()) '()]
    [(cons (cons a r1) (cons b r2)) (append (list (cons a b)) (zip r1 r2))]))

(define (singleton? l)
  (= 1 (length l)))

(define (perms l )
  (define (permut l)
    (if (singleton? l) (list l)
        (append* (map (lambda (x) (map (lambda (y) (cons x y)) (permut (remv x l)))) l))))
  (define (perms-help l acc)
    (if (null? l) acc
        (perms-help (cdr l) (append acc (permut (car l))))))
  (perms-help l '()))

(define lst (list #\E #\T #\A #\I))

(define (slice l a b)
  (define (till b l n acc)
    (if (= b n) (append acc (list (car l)))
        (till b (cdr l) (+ n 1) (append acc (list (car l))))))
  (if (< b a) '()
      (if (= a 1) (till b l 1 '())
          (slice (cdr l) (- a 1) (- b 1)))))

(define (combination l n)
  (cond [(= n (length l)) (list l)]
        [(= n 0) '(())]
        [else  (append  (combination (cdr l) n)
                        (map (lambda (y) (cons (car l) y))
                             (combination (cdr l) (- n 1))))]))
   
(define (change l)
  (if (null? l) l
      (append (string->list (car l)) (change (cdr l)))))

(define (check char lst)
  (define (check-help char lst acc)
    (match lst
      [(list (list (cons E e) (cons T t) (cons A a) (cons I i)) rest)
       (if (or (equal? char a) (equal? char i)) (check-help char rest (append acc (list (car lst))))
           (check-help char rest acc))]))
  (check-help char lst '()))

(define lst1 (list #\E #\T #\I))
(define lst2 (list #\E #\T #\A))

(define (kth l a)
  (define (kth-helper l a n)
    (if (= a n) (car l)
        (kth-helper (cdr l) a (+ 1 n))))
  (kth-helper l a 1))

(define (top-up etai-lst TE-lst)
  (define (top-up-iter etai-lst TE-lst a len)
    (cond [(> a len) etai-lst]
          [(utils:is-monoalphabetic? TE-lst (kth etai-lst a)) (top-up-iter (append (list (kth etai-lst a))
                                                                                   (slice etai-lst 1 (- a 1))
                                                                                   (slice etai-lst (+ 1 a) len))
                                                                           TE-lst
                                                                           a
                                                                           len)]
          [else (top-up-iter etai-lst TE-lst (+ 1 a) len)]))
  (top-up-iter etai-lst TE-lst 1 (length etai-lst)))



(define (sort-up etai-lst trigrams-lst)
  (define (sort-up-iter etai-lst tr-grams)
    (cond [(null? tr-grams) etai-lst]
          [else (sort-up-iter (top-up etai-lst (car tr-grams)) (cdr tr-grams))]))
  (sort-up-iter etai-lst trigrams-lst))

(define (etai key)
  (let* ([trigrams-subs (trigrams-helper (build-list 26 (lambda (_) #\_)))]
         [trigrams-etlist (map (lambda (x) (match x
                                             [(list (cons T t) (cons H h) (cons E e)) (list (cons E e) (cons T t))]))
                               trigrams-subs)])
  (define (etai-half key)
    (let* ([common-five (slice (stats:cipher-monograms utils:ciphertext) 1 5)]
           [common-singles (stats:cipher-common-words-single utils:cipher-word-list)])
      (define (etai-helper key)
        (cond [(null? common-singles) (map (lambda (x) (zip lst x))
                                           (perms (combination common-five 4)))]
              ;;;;;;;;;;;;;;;check-this-matter;;;;;;;;;;;;;;;;;;
             [(singleton? common-singles) (let ([et-lst1  common-five]
                                                [single-lst (change common-singles)])
                                            (append (map (lambda (x) (zip lst1 x))
                                                         (perms (combination et-lst1 3)))
                                                    (map (lambda (x) (zip lst2 x))
                                                         (perms (combination et-lst1 3)))))]
              [else (let* ([et-lst (remove* (change common-singles) common-five)]
                           [lst1 (list #\E #\T)]
                           [subs-half1 (map (lambda (x) (zip lst1 x))
                                            (perms (combination et-lst 2)))]
                           [lst2 (list #\A #\I)]
                           [subs-half2 (map (lambda (x) (zip lst2 x))
                                            (perms (list (change common-singles))))])
                      (lc (append x y) : x <- subs-half1 y <- subs-half2))]))
       (etai-helper key) ))
 (sort-up (map (lambda (x) (utils:add-substitution x key)) (etai-half '()))
          trigrams-etlist)))
;; (etai (build-list 26 (lambda (_) #\_)))

(define (trigrams-helper key)
  (let* ([common-three (slice (stats:cipher-trigrams utils:cipher-word-list) 1 5)]
         [trigram-lst (map (lambda (x) (string->list x)) common-three)])
         (map (lambda (x) (zip (list #\T #\H #\E) x))  (filter (lambda (x) (match x
                                                                             [(list t h e)
                                                                             (and (not (equal? t h))
                                                                                  (not (equal? h e))
                                                                                  (not (equal? e t)))]))
                                                               trigram-lst))))
 
(define (trigrams key)
  (map (lambda (x) (utils:add-substitution x key)) (trigrams-helper key)))

;(trigrams (build-list 26 (lambda (_) #\_)))
; (etai (build-list 26 (lambda (_) #\_)))
    

;; A suggested composition of strategies that might work well. Has not been
;; exhaustively tested by us. Be original ;)
(define composition (list etai trigrams))
                  ;; common-words-double
                  ;; bigrams
                  ;; common-initial-letters
                  ;; common-final-letters
                  ;; common-words-triple
                  ;; trigrams
                  ;; common-double-letters))
                  ;; common-words-quadruple
                  ;; quadgrams))

