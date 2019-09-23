#lang racket

;; You can require more modules of your choice.
(require racket/string
         racket/list
         (prefix-in utils: "utils.rkt"))

(provide secret-word-enumeration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                           ;;
;; Secret Word Enumeration                                                                   ;;
;; =======================                                                                   ;;
;;                                                                                           ;;
;; This step exploits the fact that all keys begin with a secret word that is a              ;;
;; proper SIX-LETTER word from the English dictionary.                                       ;;
;;                                                                                           ;;
;; Given a partial key, we can query the dictionary for a list of 6 letter words             ;;
;; that can potentially begin the key.                                                       ;;
;; We can then filter out potential candidates whose keys do not agree with our partial key. ;;
;;                                                                                           ;;
;; It is possible that given a (wrong) partial key, we discover that none of these           ;;
;; potential candidates can agree with our partial key. This really implies a                ;;
;; mistake in the choice of substitution, since dictionary-closure is completely             ;;
;; deterministic (modulo any bugs in your implementation :)                                  ;;
;;                                                                                           ;;
;; Hence, this function must return either of:                                               ;;
;; a. `#f` if there are no consistent candidates for this key.                               ;;
;; b. the original key if there are multiple consistent candidates.                          ;;
;; c. the complete key if there's only one consistent candidate!                             ;;
;;                                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;CHECK MULTIPLE POSSIBLE-WORD CONSISTENCY TOO!!!

(define (kth l a)
  (define (kth-helper l a n)
    (if (= a n) (car l)
        (kth-helper (cdr l) a (+ 1 n))))
  (kth-helper l a 1))

(define (slice l a b)
  (define (till b l n acc)
    (if (= b n) (append acc (list (car l)))
        (till b (cdr l) (+ n 1) (append acc (list (car l))))))
  (if (< b a) '()
      (if (= a 1) (till b l 1 '())
          (slice (cdr l) (- a 1) (- b 1)))))

(define (change-l-to-u word)
  (map (lambda (x) (cond [(equal? #\_ x) x]
                         [else (integer->char (- (char->integer x) 32))])) word))

;;;(change-l-to-u (string->list "abhinav"))

(define (change-u-to-l word)
  (map (lambda (x) (cond [(equal? #\_ x) x]
                         [else (integer->char (+ (char->integer x) 32))])) word))

;;;(change-u-to-l (string->list "ABHINAV"))

(define (check-mapping secret-word dict-word)
  (define (check-mapping-helper secret-word dict-word)
    (if (null? dict-word) #t
       (if (or (equal? (car secret-word) (car dict-word)) (equal? #\_ (car secret-word)))
           (check-mapping-helper (cdr secret-word) (cdr dict-word))
           #f)))
  (check-mapping-helper secret-word (string->list dict-word)))

;;;(check-mapping (list #\w #\_ #\_ #\_  #\o #\_) "wisdom")

(define (singleton? lst)
  (= 1 (length lst)))

(define (word-possible? secret-word lst)
  (define (word-possible-helper secret-word-u lst acc)
    (cond [(null? lst) (if (null? acc) #f
                           (if (singleton? acc) (change-u-to-l (string->list (car acc)))   ;;;;OUTPUT IS UPPERCASED WORD
                               secret-word))]
          [(not (= 6 (string-length (car lst)))) (word-possible-helper secret-word-u (cdr lst) acc)]
          [else (if (equal? #f (check-mapping secret-word-u (car lst)))          
                    (word-possible-helper secret-word-u (cdr lst) acc)
                    (word-possible-helper secret-word-u (cdr lst) (append acc (list (car lst)))))]))
  (word-possible-helper (change-l-to-u secret-word) lst '())) 

;;(word-possible?  (list #\w #\_ #\s #\d  #\o #\_) utils:dictionary)

(define (is-consistent? secret-word key)
  (define (loop secret-word initials a acc)
    (cond [(= 7 a) acc]
          [(equal? (kth key a) #\_) (loop secret-word initials (+ 1 a) (append acc
                                                                            (list (cons (integer->char (+ a 64))
                                                                                        (kth secret-word a)))))]
          [else (loop secret-word initials (+ 1 a) acc)]))  
  (let* ([initials (slice key 1 6)]
         [possible-subs (loop secret-word initials 1 '())])
   (if (equal? #f (utils:is-monoalphabetic? possible-subs key)) #f
       possible-subs)))

;;;(is-consistent? (list #\w #\i #\s #\d  #\o #\m) (list #\w #\_ #\_ #\_ #\o #\_ #\_ #\_ #\q #\_ #\_ #\_ #\v #\x #\y #\z #\_ #\b #\_ #\e #\_ #\_ #\_ #\_ #\_ #\_))

(define (consistent-key comp-key orig-key acc)
  (cond [(null? orig-key) acc]
        [(equal? #\_ (car orig-key)) (consistent-key (cdr comp-key) (cdr orig-key) (append acc (list (car comp-key))))]
        [(not (equal? (car orig-key) (car comp-key))) #f]
        [else (consistent-key (cdr comp-key) (cdr orig-key) (append acc (list (car comp-key))))]))

(define (search? letter lst)
  (if (null? lst) #f
      (if (equal? letter (car lst)) #t
          (search? letter (cdr lst)))))

(define (complete-key inits)
  (utils:encryption-key (list->string inits)))
;;;(complete-key (list #\w #\i #\s #\d #\o #\m))

(define (final-key mod-key orig-key)
   (consistent-key (complete-key (slice mod-key 1 6)) orig-key '()))

(define (incomplete? word)
  (cond [(null? word) #f]
        [(equal? #\_ (car word)) #t]
        [else (incomplete? (cdr word))]))
  
(define (secret-word-enumeration key-after-dictionary-closure) ;; Returns a key or false (#f)
  (let* ([partial-secret-word (slice key-after-dictionary-closure 1 6)]
        [is-word-possible (word-possible? partial-secret-word utils:dictionary)])
      (cond [(equal? #f is-word-possible) #f]
            [(and (equal? partial-secret-word is-word-possible)
                  (incomplete? partial-secret-word))
             key-after-dictionary-closure]
            [else (let ([consistency-check (is-consistent? is-word-possible key-after-dictionary-closure)])
                    (if (equal? #f consistency-check) #f
                      (final-key (utils:add-substitution consistency-check key-after-dictionary-closure)
                                    key-after-dictionary-closure)))])))
;;;;(secret-word-enumeration (list #\w #\i #\s #\d #\o #\m #\n #\p #\q #\r #\t #\u #\v #\x #\y #\z #\a #\b #\c #\e #\f #\g #\h #\j #\k #\_))
  ;;;;;;CHECK FOR SINGLE WORD???