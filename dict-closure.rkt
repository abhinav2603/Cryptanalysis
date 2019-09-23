#lang racket/base

;; You can require more modules of your choice.
(require racket/list
         racket/string
         (prefix-in utils: "utils.rkt")
         "strategies.rkt")

(provide dictionary-closure)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                  ;;
;; Dictionary Closure                                                               ;;
;; ==================                                                               ;;
;;                                                                                  ;;
;; A choice of substitution can really trigger more substitutions by looking at the ;;
;; partially decrypted text - surely there will be some words which can be uniquely ;;
;; determined using the dictionary. It is prudent to concretize this "choice" as    ;;
;; this purely deterministic (involving absolutely no guess-work). In more          ;;
;; technical terms, this is called "maintaining arc-consistency" (look it up on     ;;
;; Wikipedia).                                                                      ;;
;;                                                                                  ;;
;; This function must utilise the dictionary and the cipher-word-list. Decrypt each ;;
;; word (`utils:decrypt`) and check if the dictionary has:                          ;;
;;                                                                                  ;;
;; 1. a unique completetion!                                                        ;;
;;    - Extend your key using the information with this match. Continue exploring   ;;
;;      the words under the extended key.                                           ;;
;; 2. many completions.                                                             ;;
;;    - Do nothing, just continue exploring the words under the same key. If none   ;;
;;      of the words fall into (1), return with the key that you have built so far. ;;
;; 3. no completions!                                                               ;;
;;    - Return `#f` (false), indicating that this partial key is wrong, and we must ;;
;;      revert to the original key.                                                 ;;
;;                                                                                  ;;
;; Returns either of:                                                               ;;
;; a. a (possibly) extended-key.                                                    ;;
;; b. `#f` if this key led to case (3) for some word.                               ;;
;;                                                                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;CHECK NO MATCH IN CASE OF MULTIPLE MATCHES TOO!!

(define (match-len? s1 s2)
  (= (string-length s1) (string-length s2)))

(define (map-to char uppercase lst)
  (define (map-l-to-u char lst)
  (if (null? lst) #f
      (if (equal? (cdar lst) char) (caar lst)
          (map-l-to-u char (cdr lst)))))
  (define (map-u-to-l uppercase lst)
    (if (null? lst) #f
        (if (equal? (caar lst) uppercase) #t
            (map-u-to-l uppercase (cdr lst)))))
  (cond [(and (equal? #f (map-l-to-u char lst))
              (equal? #f (map-u-to-l uppercase lst)))
         "not-found"]
        [(and (not(equal? #f (map-l-to-u char lst)))
              (not (equal? #f (map-u-to-l uppercase lst))))
         (map-l-to-u char lst)]
        [else #f]))

(define (uppercase? char)
   (not (>= (char->integer char) 97)))

(define (singleton? lst)
  (= 1 (length lst)))


(define (map-possible part-decrypt word)
  (define (mapping-consistent part-decrypt word acc)
    (if (null? word) acc
         (let* ([decrypt-init (car part-decrypt)]
                [word-init (car word)]
                [upcase? (uppercase? decrypt-init)])
           (cond [(and upcase? (not (equal? decrypt-init word-init))) #f]
                 [(and upcase?  (eq? decrypt-init word-init))
                  (mapping-consistent (cdr part-decrypt) (cdr word) acc)]
                 [(equal? "not-found" (map-to decrypt-init word-init acc)) 
                  (mapping-consistent (cdr part-decrypt) (cdr word) (append acc (list (cons word-init decrypt-init))))]
                 [(equal? #f (map-to decrypt-init word-init acc)) #f] 
                 [else (let ([uppercase-map  (map-to decrypt-init word-init acc)])
                         (if (equal? uppercase-map word-init) (mapping-consistent (cdr part-decrypt) (cdr word) acc)
                             #f))]))))
  (mapping-consistent (string->list part-decrypt) (string->list word) '()))

;(map-possible "LITTLE" "LITTLE")

;(define (map-possible-v2 part-decrypt word)
;  (define (map-possible-help part-decrypt word acc)
;    (cond [(null? part-decrypt) acc]
;          [(uppercase? (car part-decrypt)) (map-possible-help (cdr part-decrypt) (cdr word) acc)]
;          [(utils:is-monoalphabetic? (list (cons (car word) (car part-decrypt))) acc)
;           (map-possible-help (cdr part-decrypt) (cdr word)
;                              (utils:add-substitution (list (cons (car word) (car part-decrypt))) acc))]
;          [else #f]))
;  (map-possible-help (string->list part-decrypt) (string->list word) (build-list 26 (lambda (_) #\_))))

;(map-possible-v2 "uITTuE" "LITTLE")
      

(define (check-word-loop part-decrypt word-list acc)
    (cond [(= 2 (length acc)) acc]
          [(null? word-list) acc]
          [(not (match-len? part-decrypt (car word-list))) (check-word-loop part-decrypt (cdr word-list) acc)]
          [else (let ([mapping (map-possible part-decrypt (car word-list))])
                  (if (eq? #f mapping) (check-word-loop part-decrypt (cdr word-list) acc)
                      (check-word-loop part-decrypt (cdr word-list) (append acc (list mapping)))))]))
;;;(check-word-loop "bURNWELL"  utils:dictionary '())

(define (all-uppercase? part-decrypt)
;  (define (all-uppercase?-helper lst)
;    (cond [(null? lst) #t]
;          [(<= 97 (char->integer (car lst))) (begin (displayln (car lst)) #f)]
;          [else (all-uppercase?-helper (cdr lst))]))
(andmap (lambda (x) (char-upper-case? x)) (string->list part-decrypt)))
  ;(all-uppercase?-helper (string->list part-decrypt))
;;(all-uppercase? "LITTLE")

(define (check-word part-decrypt key)
  (if (all-uppercase? part-decrypt) key
      (let ([acc (check-word-loop part-decrypt utils:dictionary '())])
        (cond [(null? acc) #f]
              [(singleton? acc) (if (utils:is-monoalphabetic? (car acc) key) (utils:add-substitution (car acc) key)
                                    #f) ]
              [else key]))))
;(check-word-loop "LITTLE" utils:dictionary '())
;(check-word "LITTLE" (utils:add-substitution (list (cons #\E  #\o) (cons #\T  #\e) (cons #\A  #\w) (cons #\I  #\q)) (build-list 26 (lambda (x) #\_))))

(define (dictionary-closure key)
  (define (cipher-loop key lst) 
    (if (null? lst) key
        (let ([word-found? (check-word (utils:decrypt key (car lst)) key)])
        (if (equal? #f word-found?) #f 
            (cipher-loop word-found? (cdr lst))))))
    (let ([mod-key (cipher-loop key utils:cipher-word-list)])
      (cond [(equal? #f mod-key)  #f]
            [(equal? mod-key key) key]
            [else (dictionary-closure mod-key)]))) 

;;(dictionary-closure (utils:add-substitution (list (cons #\E  #\o) (cons #\T  #\e) (cons #\A  #\w) (cons #\I  #\q)) (build-list 26 (lambda (x) #\_))))




;;;;;;SHOW KEY AS SOON AS FOUND
;;;;;;DO NOT FORGET TO DISPLAY WORDS



























