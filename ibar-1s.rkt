; replicator dynamics one shot

; report 6 7 delta .2 .8
; report 8 payoff 1-5-9
; report 9 payoff 3-5-7
; report 10 payoff 4 5 6
; report 11 2 5 8 lan 2
; report 14 200 rounds n bi nham, thuc ra van nhu cu
; report 15 chay lai 200 rounds
; save all data since report 5 (report 4 only saves data < 4)
; mutate based on current
; take sum (mean) method
;(require racket) ; for emacs to call REPL
(require racket/gui/base) ; to have TV
(require plot/no-gui) ; to have plot/dc
(require plot)
(require math/base) ; to have sum
;(require math) ; to have mean
(require 2htdp/batch-io) ; to import csv
(require "csv.rkt") ; to export csv
(plot-new-window? #t)

;(define N 1000) ; population

;; 0 = low
;; 1 = medium
;; 2 = high
(define-struct automaton (init-claim hh hm hl mh mm ml lh lm ll))
(define accommodator (make-automaton 1 0 1 2 0 1 2 0 1 2))
(define all-highs (make-automaton 2 2 2 2 2 2 2 2 2 2))
(define all-mediums (make-automaton 1 1 1 1 1 1 1 1 1 1))
(define all-lows (make-automaton 0 0 0 0 0 0 0 0 0 0))

(define (identify automaton)
  (map (lambda (f) (f automaton))
       (list
        automaton-init-claim
        automaton-hh
        automaton-hm
        automaton-hl
        automaton-mh
        automaton-mm
        automaton-ml
        automaton-lh
        automaton-lm
        automaton-ll)))

(define (all-highs? automaton)
  (equal? automaton all-highs))
(define (all-mediums? automaton)
  (equal? automaton all-mediums))
(define (all-lows? automaton)
  (equal? automaton all-lows))
(define (accommodator? automaton)
  (equal? automaton accommodator))
(define (identify-2-types population)
  (list
   (count all-highs? population)
   (count all-mediums? population)
    ))

;; previous-claim is a list of two claims
;; - the agent's own claim
;; - the opponent's claim
(define (next-claim automaton previous-claims)
  (let ([look-up
         (cond
          [(equal? previous-claims '(2 2)) automaton-hh]
          [(equal? previous-claims '(2 1)) automaton-hm]
          [(equal? previous-claims '(2 0)) automaton-hl]
          [(equal? previous-claims '(1 2)) automaton-mh]
          [(equal? previous-claims '(1 1)) automaton-mm]
          [(equal? previous-claims '(1 0)) automaton-ml]
          [(equal? previous-claims '(0 2)) automaton-lh]
          [(equal? previous-claims '(0 1)) automaton-lm]
          [(equal? previous-claims '(0 0)) automaton-ll])])
    (look-up automaton)))

;; each outcome (-1,0,1,2) is equivalent to payoff (0,2,5,8)
(define (payoff outcome)
  (cond [(zero? outcome) 2]
        [(= outcome 1) 5]
        [(= outcome 2) 8]
       ;[(= outcome -1) 0]
        ))

;; input: claims (l,m,h) ~ (0,1,2)
;; output: payoff (0,2,5,8)
(define (match-claims claims)
  (if (<= (sum claims) 2)
      (map payoff claims)
      (list 0 0)))

(define (match-pair* au1 au2 results previous-claims countdown)
  (if (zero? countdown)
      results
      (match-pair* au1 au2
                   (append results (list
                                    (match-claims previous-claims)))
                   (list (next-claim au1 previous-claims)
                         (next-claim au2 (reverse previous-claims)))
                   (sub1 countdown))))

;; match a pair of automaton for n rounds
;; return a list of round results
(define (match-pair automaton-pair rounds-per-match)
  (match-pair* (first automaton-pair)
               (second automaton-pair)
               '()
               (map automaton-init-claim automaton-pair)
               rounds-per-match))

;; mass production
(define (base10->base3 n)
  (~r n #:base 3 #:min-width 10 #:pad-string "0"))

(define (char->digit c)
  (case c
    ;; (map (lambda (i) (format "[(#\\~a) ~a]" i i))
    ;;      (range 0 10))
    [(#\0) 0]
    [(#\1) 1]
    [(#\2) 2]
    [(#\3) 3]
    [(#\4) 4]
    [(#\5) 5]
    [(#\6) 6]
    [(#\7) 7]
    [(#\8) 8]
    [(#\9) 9]))

(define (base3->digits a-string)
  (map char->digit (string->list a-string)))

(define (number->automaton n)
  (apply make-automaton (base3->digits (base10->base3 n))))

(define (contest automaton contestant-list)
  (map (lambda (x) (match-pair (list automaton x) 10))
       contestant-list))

(define (mass-produce p1 p2)   ; machine p1 to machine p2
  (for/list ([n (in-range p1 (add1 p2))])
    (number->automaton n)))

;; matching
(define series (list (list 0 0)))

(define (create-test-population high medium low accom)
  (set! series (list (list high medium)))
  (set! N (sum (list high medium low accom)))
  (shuffle
   (append
    (make-list high all-highs)
    (make-list medium all-mediums)
    (make-list low all-lows)
    (make-list accom accommodator))))

;; in each match, take mean of round results for each automaton
;; returns a pair of means
(define (take-sums round-results)
  (map (lambda (f) (sum  (map f round-results)))
       (list first second)))

(define (take-discounts delta round-results)
  (map (lambda (f)
         (sum
          (for/list ([i (length round-results)])
            (* (list-ref (map f round-results) i)
               (expt delta i)))))
         (list first second)))

(define (match-population population rounds-per-match)
  (for/list ([i (/ (length population)
                   2)])
    (take-sums
     (match-pair (list
                  (list-ref population (* 2 i))
                  (list-ref population (add1 (* 2 i))))
                 rounds-per-match))))

;; hmm payoff 0 may not need to be add1

(define (reductions-h f accumulated init a-list)
  (if (null? a-list)
      accumulated
      (let ((next-init (f init (first a-list))))
        (reductions-h f
                      (append accumulated (list next-init))
                      next-init
                      (rest a-list)))))
(define (reductions f init a-list)
  (if (null? a-list)
      accumulated
      (reductions-h f '() init a-list)))
(define (reductions* f a-list)
  (let ([init (first a-list)])
    (reductions-h f (list init) init (rest a-list))))

(define (accumulate a-list)
  (reductions* + (cons 0 a-list)))

(define (payoff-percentages payoff-list)
  (let ([s (sum payoff-list)])
    (for/list ([i (length payoff-list)])
      (/ (list-ref payoff-list i)
         s))))

(define (accumulated-fitness population rounds-per-match)
  (accumulate
   (payoff-percentages
    (flatten
     (match-population population rounds-per-match)))))

(define (randomise-over-fitness accumulated-payoff-percentage population speed)
  (let
      ([len (length population)])
    (for/list
        ([n speed])
      (let ([r (random)])
        (for/and ([i len])
          #:break (< r (list-ref accumulated-payoff-percentage i))
          (list-ref population i))))))

(define (randomisation-test an-accumulated-list)
  (for/list
      ([n 20])
    (let ([r (random)])
      (for/and ([i N])
        #:break (< r (list-ref an-accumulated-list i))
        i))))

;; create population
(define (random-population* n-automata-per-type types)
  (shuffle
   (flatten
    (for/list ([i types])
      (make-list n-automata-per-type i)))))

(define (random-population
         n-automata-per-type n-types)
  (random-population*
   n-automata-per-type
   (for/list ([i n-types])
     (number->automaton (random 59049)))))

(define (random-one-shot-population
         h-n-types m-n-types l-n-types)
  (shuffle
   (append
    (random-population*
     1 (for/list ([l l-n-types])
         (number->automaton (random 19683))))
    (random-population*
     1 (for/list ([m m-n-types])
         (number->automaton (+ 19683 (random 19683)))))
    (random-population*
     1 (for/list ([h h-n-types])
         (number->automaton (+ 39366 (random 19683))))))))

;; COUNT TYPES

(define (automaton->number automaton)
  (string->number
   (apply string-append (map number->string automaton))
   3))

(define (scan population)
  (foldl
   (lambda (au h)
     (hash-update h au add1 0))
   (hash)
   population))
(define (scan-identify population)
  (foldl
   (lambda (au h)
     (hash-update h (identify au) add1 0))
   (hash)
   population))

(define (scan-init population)
  (foldl
   (lambda (au h)
     (hash-update h (automaton-init-claim au) add1 0))
   (hash)
   population))


(define (hash-ref* a-hash a-key)
  (if (hash-has-key? a-hash a-key)
      (hash-ref a-hash a-key)
      0))

(define (scan-types population)
  (let ([type-list (scan-init population)])
    (list
     (hash-ref* type-list 0)
     (hash-ref* type-list 1))))

(define (scan-3-types population)
  (let ([type-list (scan-init population)])
    (list
     (hash-ref* type-list 0)
     (hash-ref* type-list 1)
     (hash-ref* type-list 2))))


(define (rank a-hash)
  (sort (hash->list a-hash) #:key cdr >))

(define (n->xn n)
  (string->symbol
   (string-append "x" (number->string n))))

(define (top t a-hash)
  (let* ([top-list (map car (take (rank a-hash) t))]
         [l (length top-list)])
    (for/list ([i l])
      (eval
       (list 'define (n->xn i)
             (list-ref top-list i))))))

(define (top-identify t a-hash)
  (let* ([top-list (map car (take (rank a-hash) t))]
         [l (length top-list)])
    (for/list ([i l])
      (eval
       (list 'define (n->xn i)
             (apply make-automaton (list-ref top-list i)))))))

(define population-mean (list 0))
(define payoff-space (list 0))
(define rank-table (list 0))
(define pure-types (list (list 0 0)))

(define (rank-payoff criterion population rounds-per-match)
  (let ([payoff-list (flatten (match-population population rounds-per-match))])
    (sort (hash->list (scan payoff-list)) #:key criterion >)))

;; mutate on current
(define (mutate-population population)
  (let ([chosen-one (list->vector
                     (identify (list-ref
                                population
                                (random (length population)))))])
    (vector-set! chosen-one (random 10) (random 3))
    (apply make-automaton (vector->list chosen-one))))

(define (mutate-random population)
  (let ([n (random 19683)])
    (number->-automaton
     (if (zero? (random 2)) n (+ 39366 n)))))

(define (mutate-random* population)
  (number->automaton (random 59049)))

(define (evolve population cycles speed per-type mutants rounds-per-match file-mean file-rank file-type)
  (let* ([l (length population)]
         [types-scanned (scan-types population)]
         [mutant-amount (* per-type mutants)]
         [round-results (match-population population rounds-per-match)]
         [average-payoff (exact->inexact (/ (sum (flatten round-results))
                                            (* l rounds-per-match)))]
         [accum-fitness (accumulate (payoff-percentages (flatten round-results)))]
         [survivors (drop population (+ speed mutant-amount))]
         [successors
          (randomise-over-fitness accum-fitness population speed)]
         [mutation
          (flatten (make-list per-type
                              (for/list ([i mutants])
                                (mutate-random* population))))]
         [new-population (shuffle (append survivors successors mutation))]
         )
    ;(set! series (append series (list (identify-2-types new-population))))
    (set! population-mean
          (append population-mean (list average-payoff)))
    (set! pure-types
          (append pure-types (list types-scanned)))
    ;(and (< average-payoff 4)
    ;(out-data file-rank (map list
    ;                         (append (list cycles)
    ;                                 (rank
    ;                                  (scan-identify population)))))
    ;(plot-dynamic l pure-types)
    (if (zero? cycles)
        (begin
         ; (out-data file-mean (map list population-mean))
          (out-data file-type pure-types)
          population
         )
          ;(set! payoff-space round-results)
        (evolve new-population (sub1 cycles) speed per-type mutants rounds-per-match file-mean file-rank file-type)
        )))

;; TV

(define dynamic-frame (new frame%
                           [label "population average"]
                           [width 1000]
                           [height 400]))
(define dynamic-canvas (new canvas%
                            [parent dynamic-frame]))
(define dynamic-dc (send dynamic-canvas get-dc))
(define (plot-dynamic popu-length data)
  (plot/dc (lines (drop data 1)
                  #:x-min 0 #:x-max popu-length
                  #:y-min 0 #:y-max popu-length)
           dynamic-dc
           0 0 400 400))

(define (plot-mean data)
  (let* ([l (length data)]
         [coors (map list
                     (build-list l values)
                     data)])
    (plot/dc (lines coors
                    #:x-min 0 #:x-max l
                    #:y-min 0 #:y-max 11

                    )
             dynamic-dc
             0 0 1000 400)))

(define (plot-and-export file-name)
  (let* ([data (load-data file-name)]
         [l (length data)]
         [coors (map list (build-list l values)
                     data)])
    (plot (lines coors #:x-min 0 #:x-max l
                 #:y-min 0 #:y-max 11)
          #:width 1000 #:height 400
          #:x-label "cycles" #:y-label "average"
          #:out-file (string-replace file-name "txt" "png")
          )))

(define (plot-payoff-space pay-list)
  (plot/dc (points pay-list
                   #:x-min 0 #:x-max 820
                   #:y-min 0 #:y-max 820)
           dynamic-dc
           0 0
           400 400))

;; data:
;; '((1 2..)
;;   (2 3..))

;; if needed, map list data..
(define (out-data filename data)
  (define out (open-output-file filename #:mode 'text #:exists 'append))
  (write-table data out)
  (close-output-port out))


;; TRIAL RUN
; (load "ibar.rkt")
; (define A (random-population 1 150))
; (define A1 (evolve A 20000 8 1 1 50))
; (send dynamic-frame show #t)
; (plot-mean population-mean)
; (rank (scan-identify A1))

(define (run-simulation machine-per-type machines cycles speed mutant-per-type mutants rounds-per-match file-list)
  (define A (random-population machine-per-type machines))
  (define A1 (evolve A cycles speed mutant-per-type mutants rounds-per-match
                     (first file-list) (last file-list)
                     ))
  (print "hi"))
#|
machine-per-type 1
machines 100
cycles 100000
speed 5/10/15/20
mutant-per-type 1
mutants 1
rounds-per-match 1/5/10/15/20
file-mean
file-rank
|#

(define (n->sr s r)
  (let ([pre-name (string-append
                   "R:/report15/"
                   "s" (number->string s) "r" (number->string r))])
    (list
     (string-append pre-name "m.txt")
     (string-append pre-name "r.txt"))))

(define (n->mrt n)
  (let ([pre-name (string-append
                   "R:/"
                   (number->string n))])
    (list
     (string-append pre-name "m.txt")
     (string-append pre-name "r.txt")
     (string-append pre-name "t.txt"))))

(define speed-list (list 5 10 15 20))
(define speed-list-2 (list 10 15 20))

(define rounds-list (list 1 5 10 15 20))
(define rounds-list-1 (list 1 5 10))
(define rounds-list-2 (list 15 20))

(define numbers-list
  (list (list 400 500 100)
        (list 600 300 100)
        (list 800 100 100)
        (list 600 100 300)
        (list 400 100 500)
        (list 200 100 700)
        (list 0 100 900)
        (list 100 200 700)
        (list 200 300 500)
        ))

(define (run-one-shot number-list file-type)
  (define A (random-one-shot-population (first number-list)
                                        (second number-list)
                                        (last number-list)))
  (define A1 (evolve A 500 100 1 5 1 "a" "b"
                     file-type))
  (print "hi"))

(define (run-one-shots number-list file-type)
  (for ([i (length number-list)])
    (run-one-shot (list-ref number-list i)
                  file-type)
;    (set! population-mean (list 0))
    (set! pure-types (list (list 0 0)))))

(define (run-all list-of-speeds list-of-rounds)
  (for* ([i (in-list list-of-speeds)]
         [j (in-list list-of-rounds)])
    (run-simulation 1 100 100000 i 1 1 j (n->sr i j))
    (set! population-mean (list 0))))

(define (export-all-pics list-of-speeds list-of-rounds)
  (for* ([s (in-list list-of-speeds)]
         [r (in-list list-of-rounds)])
    (plot-and-export (first (n->sr s r)))))

(define (load-data file-name)
  (let ([data (read-csv-file file-name)])
    (map string->number (flatten data))))

(define (load-and-plot-mean file-mean)
  (let ([data (read-csv-file file-mean)])
    (plot-mean (map string->number (flatten data)))
    ))

(define (load-coors file-type)
  (let ([data (read-csv-file file-type)])
    (map (lambda (x) (map string->number x)) data)))

(define (load-and-divide number-list file-type)
  (let* ([l (length number-list)]
         [data (load-coors file-type)]
         [data-l (length data)]
         [unit-l (/ data-l l)])
    (for/list ([i l])
      (drop (take (drop data (* i unit-l)) unit-l) 1))))


(define (load-and-plot-rd popu-length number-list file-type)
  (let* ([data-list (load-and-divide number-list file-type)]
         [l (length data-list)])
    (plot
     (for/list ([i l])
       (lines (list-ref data-list i))
       )
     #:x-min 0 #:x-max popu-length
     #:y-min 0 #:y-max popu-length
     #:width 400 #:height 400
     #:x-label "low" #:y-label "medium"
     #:out-file (string-replace file-type "txt" "png"))))

(define (load-and-plot-type popu-length file-type number-list)
  (let ([l (length number-list)]
        [data (load-coors file-type)])
    (plot-dynamic popu-length data)))
                  

(define (plot-and-export-type popu-length file-name)
  (let ([RD-coors (drop (load-coors file-name) 1)])
    (plot (lines RD-coors #:x-min 0 #:x-max popu-length
                 #:y-min 0 #:y-max popu-length)
          #:width 400 #:height 400
          #:x-label "low" #:y-label "medium"
          #:out-file (string-replace file-name "txt" "png")
          )))

(define (export-all-type-pics popu-length list-of-numbers)
  (let ([l (length list-of-numbers)])
    (for ([i l])
      (plot-and-export-type popu-length (last (n->mrt i))))))


(define (load-and-cut file-name)
  (let ([data (load-data file-name)])
    (out-data (string-replace file-name "report" "report2")
              (map list (take-right data 100000)))))
