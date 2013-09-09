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
 (check-equal? (sep-names pat)
               (list (named-pat 'any_1
                                'any
                                #t)))
 (check-equal? (sep-names rep)
               (list (named-rep '()
                                '..._1
                                #f)
                     (named-rep '()
                                '..._1
                                #f)))
 (check-equal? (sep-names lst)
               (list (named-pat 'rep_1
                                `(nt rep)
                                #t))))

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
