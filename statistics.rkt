#lang racket

;; You can require more modules of your choice.
(require racket/list
         racket/string
         (prefix-in utils: "utils.rkt"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                 ;;
;; Ciphertext Statistics                                                           ;;
;; =====================                                                           ;;
;;                                                                                 ;;
;; The module should provide a bunch of functions that do statistical analysis of  ;;
;; ciphertext. The output is almost always just an ordered list (counts are        ;;
;; omitted).                                                                       ;;
;;                                                                                 ;;
;; Fill in the body for the skeletons and do not change the arguments. You can     ;;
;; define as many functions as you require, there's no special credit for          ;;
;; implementing/using all of them.                                                 ;;
;;                                                                                 ;;
;; CAUTION:                                                                        ;;
;; 1. Be mindful that bi, tri and quadgrams do not cross word boundaries. Hence,   ;;
;; you must process each word separately.                                          ;;
;;                                                                                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Analyses
(provide cipher-monograms
         cipher-bigrams
         cipher-unique-neighbourhood
         cipher-neighbourhood
         cipher-trigrams
         cipher-quadgrams
         cipher-common-words-single
         cipher-common-words-double
         cipher-common-words-triple
         cipher-common-words-quadruple
         cipher-common-initial-letters
         cipher-common-final-letters
         cipher-common-double-letters
         ;; any other functions of your design come below:

         ;; my-fundoo-analysis
         )

;; Takes ciphertext and produces a list of cipher chars sorted in decreasing
;; order of frequency.
(define (cipher-monograms ciphertext)
  (define (collect lst acc)
    (if (null? lst) acc
        (collect (cdr lst) (search-and-add (car lst) acc '()))))
  (let* ([cipherlist (remove* (list #\newline #\space #\, #\. #\? #\; #\' #\- #\: #\!) (string->list (string-join utils:cipher-word-list)))]
         [sorted-list (sort (collect cipherlist '())
                            (lambda (x y) (>= (length x) (length y))))])
    (map (lambda (x) (car x)) sorted-list)))

(define (search-and-add char lst acc)
  (if (null? lst) (append acc (list (list char)))
      (if (equal? char (caar lst)) (append acc (list (cons char (car lst))) (cdr lst))
          (search-and-add char (cdr lst) (append acc (list (car lst))) ))))
;;;(cipher-monograms utils:ciphertext)

;; Takes the cipher-word-list and produces a list of 2-letter bigram (strings)
;; sorted in decreasing order of frequency. Each element must be a string!
(define(search-and-add-ngram str lst)
  (define (add-helper str lst acc)
    (if (null? lst) (append acc (list (cons str 1)))
        (if (equal? str (caar lst)) (append acc (list (cons str (+ 1 (cdar lst)))) (cdr lst))
            (add-helper str (cdr lst) (append acc (list (car lst)))))))
  (add-helper str lst '()))

(define (ngram-adder n word acc)
  (if (= n (string-length word)) (search-and-add-ngram word acc)
      (ngram-adder n (substring word 1 (string-length word)) (search-and-add-ngram (substring word 0 n) acc))))

(define (cipher-ngrams-naive cipher-word-list n) 
  (define (ngrams-helper cipher-word-list acc)
    (cond [(null? cipher-word-list) acc]
          [(not (<= n (string-length (car cipher-word-list)))) (ngrams-helper (cdr cipher-word-list) acc)]
          [else (ngrams-helper (cdr cipher-word-list) (ngram-adder n (car cipher-word-list) acc))]))
       (ngrams-helper cipher-word-list '()))

(define (cipher-ngrams cipher-word-list n)
  (map (lambda (x) (car x)) (sort (cipher-ngrams-naive cipher-word-list n)
                                  (lambda (x y) (>= (cdr x) (cdr y))))))

(define (cipher-bigrams cipher-word-list)
  (cipher-ngrams cipher-word-list 2))

;;;(length (cipher-bigrams utils:cipher-word-list))

;;;(cipher-bigrams utils:cipher-word-list)

;; Takes the bigram frequency order (output of `cipher-bigrams`) and computes
;; the neighbourhood of each letter with every other letter. Only unique
;; neighbours are to be counted.
;; Consider the character #\o.
;;
;; Takes an argument `mode`:
;; 1. (cipher-unique-neighbourhood cipher-bigrams 'predecessor)
;;    - Count only those unique occurrences where the (given) char preceeds
;;      other char.
;;    - Patterns of the form: "o?"
;; 2. (cipher-unique-neighbourhood cipher-bigrams 'successor)
;;    - Count only those unique occurrences where the (given) char succeeds
;;      other char.
;;    - Patterns of the form: "?o"
;; 3. (cipher-unique-neighbourhood cipher-bigrams 'both)
;;    - Count all unique occurrences where the (given) char neighbours the other
;;      char.
;;    - Patterns of the form "?o" and "o?". Note that this is not sum of (1) and
;;    (2) always.
;;
;; The output is a list of pairs of cipher char and the count of it's
;; neighbours. The list must be in decreasing order of the neighbourhood count.
;(define (cipher-unique-neighbourhood cipher-bigrams-list mode)
  ;; You must match against or test (using cond) for the `mode` argument. Possibilities are:
  ;; 'predecessor, 'successor, 'both
  ;; Figure out experimentally which of these is a good indicator for E vs T.
;  '())

;; Takes the bigram frequency order (output of `cipher-bigrams`) and computes
;; the neighbourhood of each letter with every other letter, but counts each
;; occurrence distinctly. This comment contains 6 bigrams with "w", all with "i" or "h".
;; So "w" has:
;; when mode is 'both,        6 neighbours
;; when mode is 'predecessor, 6 neighbours
;; when mode is 'successor,   0 neighbours
(define (slice l a b)
  (define (till b l n acc)
    (if (= b n) (append acc (list (car l)))
        (till b (cdr l) (+ n 1) (append acc (list (car l))))))
  (if (< b a) '()
      (if (= a 1) (till b l 1 '())
          (slice (cdr l) (- a 1) (- b 1)))))

(define (subtract l1 l2 acc)
  (cond [(and (null? l1) (null? l2)) acc]
        [(null? l2) (append acc l1)]
        [(equal? (caar l1) (substring (caar l2) 0 1)) (subtract (cdr l1)
                                                                (cdr l2)
                                                                (append acc (list (cons (caar l1)
                                                                                        (- (cdar l1) (cdar l2))))))]
        [else (subtract (cdr l1) l2 (append acc (list (car l1))))]))

(define (combine l1 l2 acc)
  (cond [(and (null? l1) (null? l2)) acc]
        [(null? l1) (append acc l2)]
        [(null? l2) (append acc l1)]
        [(equal? (caar l1) (caar l2)) (combine (cdr l1) (cdr l2)
                                               (append acc (list (cons (caar l1)
                                                                       (+ (cdar l1) (cdar l2))))))]
        [(string>? (caar l1) (caar l2)) (combine l1 (cdr l2)
                                                 (append acc (list (car l2))))]
        [(string<? (caar l1) (caar l2) (combine (cdr l1) l2
                                                (append acc (list (car l1)))))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (cipher-unique-neighbourhood cipher-bigrams-list mode)
 (sort (cipher-neighbourhood-helper (map (lambda (x) (cons (car x) 1))
                                   (cipher-ngrams-naive utils:cipher-word-list 2)) mode)
       (lambda (x y) (> (cdr x) (cdr y)))))


(define (cipher-neighbourhood cipher-bigrams-list mode)
  (sort (cipher-neighbourhood-helper (cipher-ngrams-naive utils:cipher-word-list 2) mode)
        (lambda (x y) (> (cdr x) (cdr y)))))

(define (cipher-neighbourhood-helper sec-list mode)
  (cond [(equal? mode 'predecessor)
         (let ([bigram-list (sort sec-list
                                  (lambda (x y) (string<=?(car  x) (car y))))])
           (define (collect-neighbours lst acc)
             (if (null? lst) acc
                 (let ([init (substring (caar lst) 0 1)])
                   (cond [(null? acc) (collect-neighbours (cdr lst) (append acc (list (cons init (cdar lst)))))]
                         [(if (equal? init (car (last acc))) (collect-neighbours
                                                             (cdr lst)
                                                             (append (slice acc 1 (- (length acc) 1))
                                                                     (list (cons init (+ (cdar lst) (cdr (last acc)))))))
                             (collect-neighbours (cdr lst) (append acc (list (cons init 1)))))]))))
           (collect-neighbours bigram-list '()))]
        [(equal? mode 'successor)
         (let ([bigram-list (sort sec-list
                                  (lambda (x y) (string<=?(substring (car  x) 1 2)
                                                          (substring (car y) 1 2))))])
           (define (collect-neighbours lst acc)
             (if (null? lst) acc
                 (let ([end (substring (caar lst) 1 2)])
                   (cond [(null? acc) (collect-neighbours (cdr lst) (append acc (list (cons end (cdar lst)))))]
                         [(if (equal? end (car (last acc))) (collect-neighbours
                                                             (cdr lst)
                                                             (append (slice acc 1 (- (length acc) 1))
                                                                     (list (cons end (+ (cdar lst) (cdr (last acc)))))))
                             (collect-neighbours (cdr lst) (append acc (list (cons end 1)))))]))))
           (collect-neighbours bigram-list '()))]
        [else (subtract (combine (cipher-neighbourhood-helper sec-list 'predecessor)
                                 (cipher-neighbourhood-helper sec-list 'successor)
                                 '())
                        (sort (filter (lambda (x) (equal? (substring  (car x) 0 1)
                                                          (substring  (car x) 1 2)))
                                      sec-list)
                              (lambda (x y) (string<? (car x) (car y))))
                        '())]))

;(cipher-unique-neighbourhood utils:ciphertext 'both);
;(cipher-neighbourhood utils:ciphertext 'predecessor)
;(cipher-neighbourhood utils:ciphertext 'both)

                                       
  ;; You must match against or test (using cond) for the `mode` argument. Possibilities are:
  ;; 'predecessor, 'successor, 'both
  ;; Figure out experimentally which of these is a good indicator for E vs T.
  ;;'())

;; Takes the cipher-word-list and produces a list of 3-letter bigram (strings)
;; sorted in decreasing order of frequency. Each element must be a string!
(define (cipher-trigrams cipher-word-list)
  (cipher-ngrams cipher-word-list 3))
;;;;(cipher-trigrams utils:cipher-word-list)

;; Takes the cipher-word-list and produces a list of 4-letter bigram (strings)
;; sorted in decreasing order of frequency. Each element must be a string!
(define (cipher-quadgrams cipher-word-list)
  ;'()
  (cipher-ngrams cipher-word-list 4))


;; Takes the cipher word list and produces a list of single letter words, sorted
;; in decreasing order of frequency. Each element must be a string!
(define (cipher-common-words-single cipher-word-list)
  (define (cipher-single lst acc)
    (if (null? lst) acc
        (let ([first (string->list (car lst))])
          (if (not(singleton? first)) (cipher-single (cdr lst) acc)
              (cond [(null? acc) (cipher-single (cdr lst) (list (cons (car first) 1)))]
                    [(singleton? acc) (if (eq? (caar acc) (car first))
                                          (cipher-single (cdr lst) (list (cons (car first) (+ 1 (cdar acc)))))
                                          (cipher-single (cdr lst) (append acc (list (cons (car first) 1)))))]
                    [else (if (eq? (caar acc) (car first))
                              (cipher-single (cdr lst) (append (list (cons (car first) (+ 1 (cdar acc))))
                                                               (cdr acc)))
                              (cipher-single (cdr lst) (append (list (car acc))
                                                               (list (cons (car first) (+ 1 (cdadr acc)))))))])))))
  (let* ([count (cipher-single cipher-word-list '())])
    (cond [(null? count) '()]
          [(singleton? count) (list (list->string (list (caar count))))]
          [else (if (< (cdar count) (cdadr count)) (list (list->string (list (caadr count)))
                                                        (list->string (list (caar count))))
                    (list (list->string (list (caar count)))
                          (list->string (list (caadr count)))))])))

(define (singleton? lst)
   (= 1 (length lst)))
;; Takes the cipher word list and produces a list of double letter words, sorted
;; in decreasing order of frequency.

(define (search-and-add-word word lst)
  (define (search-helper word lst acc)
    (cond [(null? lst) (append acc (list (cons word 1)))]
          [(equal? word (caar lst)) (append acc (list (cons word (+ 1 (cdar lst)))) (cdr lst))]
          [else (search-helper word (cdr lst) (append acc (list (car lst))))]))
  (search-helper word lst '()))

(define (cipher-common-words-ntuple cipher-word-list n acc)
  (cond [(null? cipher-word-list) acc]
        [(= n (string-length (car cipher-word-list))) (begin (displayln acc) (cipher-common-words-ntuple (cdr cipher-word-list) n
                                                                           (search-and-add-word (car cipher-word-list) acc)))]
        [else (cipher-common-words-ntuple (cdr cipher-word-list) n acc)]))

(define (common-ntuple cipher-word-list n acc)
  (map (lambda (x) (car x))
       (sort (cipher-common-words-ntuple cipher-word-list n acc) (lambda (x y) (>= (cdr x) (cdr y))))))



(define (cipher-common-words-double cipher-word-list)
;  '())
  (common-ntuple cipher-word-list 2 '()))

;; Takes the cipher word list and produces a list of triple letter words, sorted
;; in decreasing order of frequency.
(define (cipher-common-words-triple cipher-word-list)
;  '())
  (common-ntuple cipher-word-list 3 '()))

;; Takes the cipher word list and produces a list of four letter words, sorted
;; in decreasing order of frequency.
(define (cipher-common-words-quadruple cipher-word-list)
;  '())
 (common-ntuple cipher-word-list 4 '()))

;;;;(cipher-common-words-quadruple utils:cipher-word-list)

;; Takes the cipher word list and produces a list of chars that appear at the
;; start of words, sorted in decreasing order of frequency. Each element must be
;; a char!


(define (search-and-add-char char acc)
  (define (search-helper char lst acc)
    (cond [(null? lst) (append acc (list (cons char 1)))]
          [(equal? char (caar lst)) (append acc (list (cons char (+ 1 (cdar lst)))) (cdr lst))]
          [else (search-helper char (cdr lst) (append acc (list (car lst))))]))
  (search-helper char acc '()))
  
(define (cipher-common-initial-letters cipher-word-list)
;  '())
  (define (common-initial lst acc)
    (cond [(null? lst) acc]
          [else (common-initial (cdr lst) (search-and-add-char (car (string->list (car lst))) acc))]))
  (map (lambda (x) (car x) )
       (begin (displayln (sort (common-initial cipher-word-list '()) (lambda (x y) (>= (cdr x) (cdr y)))))
         (sort (common-initial cipher-word-list '()) (lambda (x y) (>= (cdr x) (cdr y)))))))
;(cipher-common-initial-letters utils:cipher-word-list)

;; Takes the cipher word list and produces a list of chars that appear at the
;; end of words, sorted in decreasing order of frequency. Each element must be
;; a char

(define (cipher-common-final-letters cipher-word-list)
;  '())
  (define (common-final lst acc)
    (cond [(null? lst) acc]
          [else (common-final (cdr lst) (search-and-add-char (last (string->list (car lst))) acc))]))
  (map (lambda (x) (car x) )
       (begin (displayln (sort (common-final cipher-word-list '()) (lambda (x y) (>= (cdr x) (cdr y)))))
         (sort (common-final cipher-word-list '()) (lambda (x y) (>= (cdr x) (cdr y)))))))

;(cipher-common-final-letters utils:cipher-word-list)

;; Takes the cipher word list and produces a list of chars that appear as
;; consecutive double letters in some word, sorted in decreasing order of
;; frequency. Each element must thus be a char!
(define (cipher-common-double-letters cipher-word-list)
  '())
