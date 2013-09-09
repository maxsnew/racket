#lang racket/base

(require racket/contract
         racket/match
         racket/set

         "lang-struct.rkt"
         "match-a-pattern.rkt"
         "recursive-lang.rkt")

;; TODO: throw some contracts on these hos

;; a named pattern, e.g. x_1, number_!_2
(struct named-pat (pat name notmis?)
        #:transparent)

;; any repeat, e.g., given a pattern p: p ... , p ..._1 or p ..._!_2
;; pat can be used as a generic container
(struct named-rep (pat name mis)
        #:transparent)

;; n-pats : setof named-pat
;; n-reps : setof (named-rep ())
(struct with-names (n-pats n-reps val)
        #:transparent)

;; sep-names : pat -> μT. listof (U named-pat (named-rep T)))
(define (sep-names pat)
  ;; μT. sexpof (U named-pat (named-rep T))
  ;; -> μT. (U named-pat named-rep (listof (U named-pat (named-rep T))))
  (define (flatten-names names)
    (match names
      [(cons name rest)
       (append (flatten-names name)
               (flatten-names rest))]
      ;; suspect
      ['() '()]
      [(named-pat _ _ _) (list names)]
      [(named-rep rec n mis)
       (named-rep (flatten-names rec)
                  n
                  mis)]))

  (match-a-pattern
   pat
   [`any '()]
   [`number '()]
   [`string '()]
   [`natural '()]
   [`integer '()]
   [`real '()]
   [`boolean '()]
   [`variable '()]
   [`(variable-except ,s ...) '()]
   [`(variable-prefix ,s) '()]
   [`variable-not-otherwise-mentioned '()]
   [`hole '()]
   ;; Not sure
   [`(nt ,id) '()]
   [`(name ,name ,pat)
    (list (named-pat name pat #t))]
   [`(mismatch-name ,name ,pat)
    (list (named-pat name pat #f))]
   [`(in-hole ,p1 ,p2)
    (append (sep-names p1)
            (sep-names p2))]
   [`(hide-hole ,p)
    (sep-names p)]
   ;; not sure about these 2, but they are unsupported by enum anyway
   [`(side-condition ,p ,g ,e) '()] 
   [`(cross ,s) '()]
   [`(list ,sub-pats ...)
    (apply append
           (map (λ (sub-pat)
                   (match sub-pat
                     [`(repeat ,pat ,name ,mismatch)
                      (list (named-rep (sep-names pat) name mismatch))]
                     [else (sep-names sub-pat)]))
                sub-pats))]
   [(? (compose not pair?)) '()]))

;; assoc-names : μT. (U named-pat
;;                      (named-rep T)
;;                      (listof (U named-pat
;;                                 (named-rep T))))
;;               -> μT. (with-names
;;                         (U named-pat (named-rep T)
;;                            (listof named-pat
;;                                    (with-names
;;                                       (named-rep T))))))
;; associates every named pattern or list of named patterns with the set of
;; names for patterns and repeats that are used within it
(define (assoc-names named)
  (match named
    [(named-pat _ _ _)
     (with-names (set named)
                 (set)
                 named)]
    [(named-rep rec name mis)
     (let* ([sub-assocs (assoc-names rec)]
            [sub-names (with-names-n-pats sub-assocs)]
            [sub-reps (with-names-n-reps sub-assocs)])
       (with-names sub-names
                   (set-add sub-reps
                            (named-rep '() name mis))
                   named))]
    [(list sub-named ...)
     (let* ([sub-assocs (map assoc-names sub-named)]
            [sub-names (fold-map/set with-names-n-pats
                                     sub-assocs)]
            [sub-reps (fold-map/set with-names-n-reps
                                    sub-assocs)])
       (with-names sub-names
                   sub-reps
                   sub-assocs))]))

;; trim-names : with-names -> with-names

;; trim-names returns a new version of a with-names struct wherein the
;; names are only associated with the outermost pattern that contains
;; them, e.g., (x_1 ..._1 x_2 ..._2) will have the variable pattern
;; names associated with themselves and not the outer repeats, whereas
;; (x_1 ..._1 x_1 ..._1) will have the var pattern names associated
;; with the outer repeats and not the inner patterns.
(define (trim-names w-names)

  ;; remove-names : with-names (setof named-pat) (setof named-rep) -> with-names
  (define (remove-names w-names n-pat-remove n-rep-remove)
    (match w-names
      [(with-names n-pats n-reps val)
       (let ([trimmed-n-pats (set-difference n-pats n-pat-remove)]
             [trimmed-n-reps (set-difference n-reps n-rep-remove)])
         (match val
           [(named-pat _ _ _)
            (with-names trimmed-n-pats
                        trimmed-n-reps
                        val)]
           [(named-rep rec name mis)
            (with-names trimmed-n-pats
                        trimmed-n-reps
                        (remove-names rec
                                      n-pat-remove
                                      (set-add (set-add n-rep-remove
                                                        name)
                                               mis)))]
           [(list sub-w-names ...)
            ;; we want to include everything that occurs in at least 2 subpats
            ;; but doesn't occur in n-pat-remove/n-rep-remove
            ;; then when we recur we want to add those t n-pat-remove/n-rep-remove
            (let* ([multi-occ-under
                    (λ (f rem)
                       (apply multi-occurrences
                              (map (λ (sub)
                                      (set-difference (f sub) rem))
                                   sub-w-names)))]
                   [sub-names (multi-occ-under with-names-n-pats n-pat-remove)]
                   [sub-reps  (multi-occ-under with-names-n-reps n-rep-remove)])
              (with-names sub-names
                          sub-reps
                          (map (λ (sub-w-name)
                                  (remove-names sub-w-name
                                                (set-union sub-names n-pat-remove)
                                                (set-union sub-reps  n-rep-remove))))))]))]))
  
  (match w-names
    (remove-names w-names
                  (set)
                  (set))))

;; set ... -> set
;; Return the elements that occur in at least two of the sets
(define (multi-occurrences . sets)
  (let loop ([sets sets]
             [once (set)]
             [twice (set)])
    (match sets
      ['() twice]
      [(cons s1 rest)
       (let loop-set ([remain (set->list s1)]
                      [once once]
                      [twice twice])
         (match remain
           ['() (loop rest once twice)]
           [(cons x xs)
            (cond [(set-member? once x)
                   (loop-set xs
                             once
                             (set-add twice x))]
                  [else
                   (loop-set xs
                             (set-add once x)
                             twice)])]))])))

(define (set-difference s1 s2)
  (set-intersect
   s1
   (set-symmetric-difference s1 s2)))

(module+
 test
 (provide named-pat
          named-rep
          sep-names
          multi-occurrences
          set-difference))
