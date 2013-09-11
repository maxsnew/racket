#lang racket/base

(require racket/contract
         racket/match
         racket/set

         "lang-struct.rkt"
         "match-a-pattern.rkt"
         "recursive-lang.rkt")

;; name and mismatch-name for a repeat
(struct named-rep (name mis)
        #:transparent)

;; vars : setof (U `(name ,name ,pat) `(mismatch ,name ,pat))
;; reps : setof named-rep
;; pat  : underlying pattern container
(struct with-names (vars reps pat)
        #:transparent)

;; lift-names : pat -> with-names pat
(define (lift-names pat)
  (match pat
    [`(name ,name ,p)
     (with-names (set pat) ;; include this entire pattern so it can be
                 ;; generated higher up if necessary
                 (set)
                 ;; We can safely assume that this will not have names in it
                 `(name ,name
                        ,(with-names (set)
                                     (set)
                                     p)))]
    ;; same as name case
    [`(mismatch-name ,name ,p)
     (with-names (set pat) 
                 (set)
                 `(mismatch-name ,name
                                 (with-names (set)
                                             (set)
                                             p)))]
    [`(in-hole ,p1 ,p2)
     (let ([w-names1 (lift-names p1)]
           [w-names2 (lift-names p2)])
       (match-let ([(with-names vars1 reps1 _) w-names1]
                   [(with-names vars2 reps2 _) w-names2])
         (with-names (set-union vars1 vars2)
                     (set-union reps1 reps2)
                     `(in-hole ,w-names1 ,w-names2))))]
    [`(hide-hole ,p)
     (let ([sub (lift-names p)])
       (match-let ([(with-names vars reps _) sub])
         (with-names vars
                     reps
                     sub)))]
    [`(list ,sub-pats ...)
     (define (lift-sub-pats sub-pat)
       (match sub-pat
         [`(repeat ,pat ,name ,mismatch)
          (let ([rec (lift-names pat)])
            (match-let ([(with-names vars reps _) rec])
              (with-names vars
                          (set-add reps
                                   (named-rep name mismatch))
                          `(repeat ,rec ,name ,mismatch))))]         
         [else (lift-names sub-pat)]))
     (let* ([subs (map lift-sub-pats sub-pats)]
            [vars (fold-map/set with-names-vars subs)]
            [reps (fold-map/set with-names-reps subs)])
       (with-names vars
                   reps
                   subs))]
    ;; Everything else is non-recursive/non-named so there are no names there
    [_ (with-names (set)
                   (set)
                   pat)]))

;; trim-names : with-names -> with-names

;; trim-names returns a new version of a with-names struct wherein the
;; names are only associated with the outermost pattern that contains
;; them, e.g., (x_1 ..._1 x_2 ..._2) will have the variable pattern
;; names associated with themselves and not the outer repeats, whereas
;; (x_1 ..._1 x_1 ..._1) will have the var pattern names associated
;; with the outer repeats and not the inner patterns.
(define (trim-names pat)

  ;; rem-vars, rem-reps are the vars/reps that will be enumerated at a
  ;; higher level and thus should be removed from sub-pats' w-names
  (define (remove-names w-names rem-vars rem-reps)
    
    (define (bare-rec p)
      (remove-names p rem-vars rem-reps))
    
    (match-let ([(with-names vars reps pat) w-names])
      (let ([trimmed-vars (λ () (set-subtract vars rem-vars))]
            [trimmed-reps (λ () (set-subtract reps rem-reps))])
      
        (match pat
          [`(name ,n ,p)
           (with-names (trimmed-vars)
                       (trimmed-reps)
                       `(name ,n ,(remove-names (set-add rem-vars pat)
                                                rem-reps
                                                p)))]
          
          [`(mismatch-name ,n ,p) (error "unimplemented")
           (with-names (trimmed-vars)
                       (trimmed-reps)
                       `(mismatch-name ,n
                                       (remove-names (set-add rem-vars pat)
                                                     rem-reps
                                                     p)))]
          
          [`(in-hole ,p1 ,p2) (error "unimplemented")
           (let* ([inter/under (λ (f)
                                  (set-intersect (f p1)
                                                 (f p2)))]
                  [common-vars (inter/under with-names-vars)]
                  [common-reps (inter/under with-names-reps)]
                  [enum-vars (set-subtract common-vars rem-vars)]
                  [enum-reps (set-subtract common-reps rem-reps)])
             (with-names enum-vars
                         enum-reps
                         `(in-hole ,(remove-names p1 enum-vars enum-reps)
                                   ,(remove-names p2 enum-vars enum-reps))))]

          ;; maybe just empty for hide-hole? Doesn't really matter....
          [`(hide-hole ,p)
           (with-names (trimmed-vars)
                       (trimmed-vars)
                       `(hide-hole ,(bare-rec p)))]
        
          [`(list ,sub-pats ...) (error "unimplemented")
           (let* ([multi-occ/f
                   (λ (f rem)
                      (apply multi-occurrences
                             (map (λ (sub)
                                     (set-difference (f sub) rem))
                                  sub-pats)))]
                  [enum-vars (multi-occ/f with-names-vars rem-vars)]
                  [enum-reps  (multi-occ/f with-names-reps rem-reps)])
             (with-names enum-vars
                         enum-reps
                         (map (λ (sub-w-name)
                                 (let ([rem-vars (set-union enum-vars rem-vars)]
                                       [rem-reps (set-union enum-reps rem-reps)])
                                   (remove-names sub-w-name rem-vars rem-reps))))))]

          ;; Add this case to the toplevel for readability
          [`(repeat ,p ,name ,mis)
           (with-names (trimmed-vars)
                       (trimmed-reps)
                       `(repeat ,(remove-names p
                                               rem-vars
                                               (set-add rem-reps (named-rep name mis)))
                                ,name
                                ,mis))]
          ;; non-recursive
          [_ (with-names (trimmed-vars)
                         (trimmed-reps)
                         pat)]))))
  
  (remove-names pat (set) (set)))


;; assoc-names : μT. (U named-pat
;;                      (named-rep T)
;;                      (listof (U named-pat
;;                                 (named-rep T))))
;;               -> μT. (with-names
;;                         (U named-pat (named-rep T)
;;                            (listof (with-names
;;                                       (U named-pat (named-rep T)))))))
;; associates every named pattern or list of named patterns with the set of
;; names for patterns and repeats that are used within it
#;
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
                   sub-assocs))]
    [`(in-hole ,p1 ,p2)
     `(in-hole ,(assoc-names p1)
               ,(assoc-names p2))]
    [`(hide-hole ,p)
     `(hide-hole ,(assoc-names p))]
    [_ named]))

;; trim-names : with-names -> with-names

;; trim-names returns a new version of a with-names struct wherein the
;; names are only associated with the outermost pattern that contains
;; them, e.g., (x_1 ..._1 x_2 ..._2) will have the variable pattern
;; names associated with themselves and not the outer repeats, whereas
;; (x_1 ..._1 x_1 ..._1) will have the var pattern names associated
;; with the outer repeats and not the inner patterns.
#;
(define (tim-names w-names)

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
  (provide named-rep
           with-names

           lift-names
          
           multi-occurrences
           set-difference))
