#lang racket

(require rackunit
         redex
         redex/private/lang-struct
         (only-in redex/private/matcher compiled-lang-lang)
         (submod redex/private/names test))

;; Example languages for testing
(define-language ExampleLang
  (pat any_1)
  (rep (any ..._1 any ..._1))
  (lst (rep_1 pat)))
(define Example (compiled-lang-lang ExampleLang))
(define pat
  (rhs-pattern (first (nt-rhs (first Example)))))
(define rep
  (rhs-pattern (first (nt-rhs (second Example)))))
(define lst
  (rhs-pattern (first (nt-rhs (third Example)))))

;; sep-names test
(test-begin
 (check-equal? (lift-names pat)
               (with-names (set `(name any_1 any))
                           (set)
                           `(name any_1
                                  ,(with-names (set)
                                               (set)
                                               `any))))
 (check-equal?
  (lift-names rep)
  (let* ([wrapped (λ (p)
                     (with-names (set)
                                 (set (named-rep '..._1 #f))
                                 p))]
         [rep (wrapped `(repeat
                         ,(with-names (set)
                                      (set)
                                      `any)
                         ..._1 #f))])
    (wrapped (list rep rep))))

 (check-equal?
  (lift-names lst)
  (let* ([w-empty (λ (p)
                     (with-names (set)
                                 (set)
                                 p))]
         [var `(name rep_1 (nt rep))]
         [vars (set var)])
    (with-names vars
                (set)
                (list (with-names vars
                                  (set)
                                  `(name rep_1 ,(w-empty `(nt rep))))
                      (w-empty `(nt pat)))))))

;; multi-occurrences test
(test-begin
 (check-equal? (multi-occurrences (set 1))
               (set))
 (check-equal? (multi-occurrences (set 1)
                                  (set 1))
               (set 1))
 (check-equal? (multi-occurrences (set 1)
                                  (set 2))
               (set))
 (check-equal? (multi-occurrences (set 1)
                                  (set 1)
                                  (set 1))
               (set 1))
 (check-equal? (multi-occurrences (set 1 4 5)
                                  (set 5 2)
                                  (set 4 8))
               (set 4 5)))

;; set-difference tests
(test-begin
 (check-equal? (set-difference (set) (set))
               (set))
 (check-equal? (set-difference (set) (set 1))
               (set))
 (check-equal? (set-difference (set 1) (set))
               (set 1))
 (check-equal? (set-difference (set 1) (set 1))
               (set))
 (check-equal? (set-difference (set 1 3 5) (set 2 3 4))
               (set 1 5))
 )
