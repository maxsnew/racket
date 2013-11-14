#lang racket/base
(require racket/bool
         racket/contract
         racket/function
         racket/list
         racket/math
         racket/match
         racket/set

         "enumerator.rkt"
         "env.rkt"
         "error.rkt"
         "lang-struct.rkt"
         "match-a-pattern.rkt"
         "preprocess-pat.rkt"
         "preprocess-lang.rkt")

(provide 
 (contract-out
  [lang-enumerators (-> (listof nt?) lang-enum?)]
  [pat-enumerator (-> lang-enum?
                      any/c ;; pattern
                      enum?)]
  [enum-ith (-> enum? exact-nonnegative-integer? any/c)]
  [lang-enum? (-> any/c boolean?)]
  [enum? (-> any/c boolean?)]))

(struct lang-enum (enums unused-var/e))
(struct repeat (n terms) #:transparent)
(struct name-ref (name) #:transparent)
(struct misname-ref (name tag) #:transparent)
(struct nrep-ref (name subpat) #:transparent)
(struct decomp (ctx term) #:transparent)
(struct hide-hole (term) #:transparent)

;; Top level exports
(define enum-ith decode)

(define (lang-enumerators lang)
  (define l-enums (make-hash))
  (define unused-var/e
    (apply except/e
           var/e
           (used-vars lang)))
  (define (enumerate-lang! cur-lang enum-f)
    (for ([nt (in-list cur-lang)])
      (hash-set! l-enums
                 (nt-name nt)
                 (with-handlers ([exn:fail:redex? fail/e])
                   (enum-f (nt-rhs nt)
                           l-enums)))))
  (define-values (fin-lang rec-lang) (sep-lang lang))
  (enumerate-lang! fin-lang
                   (λ (rhs enums)
                      (enumerate-rhss rhs enums unused-var/e)))
  (enumerate-lang! rec-lang
                   (λ (rhs enums)
                      (thunk/e +inf.f
                               (λ ()
                                  (enumerate-rhss rhs enums unused-var/e)))))

  (lang-enum l-enums unused-var/e))

(define (pat-enumerator l-enum pat)
  (map/e
   to-term
   (λ (_)
      (redex-error 'pat-enum "Enumerator is not a  bijection"))
   (pat/e pat
          (lang-enum-enums l-enum)
          (lang-enum-unused-var/e l-enum))))

(define (enumerate-rhss rhss l-enums unused/e)
  (apply sum/e
         (for/list ([production (in-list rhss)])
           (pat/e (rhs-pattern production)
                  l-enums
                  unused/e))))

(define (pat/e pat l-enums unused/e)
  (match-define (ann-pat nv pp-pat) (preprocess pat))
  (map/e
   ann-pat
   (λ (ap)
      (values (ann-pat-ann ap)
              (ann-pat-pat ap)))
   (env/e nv l-enums unused/e)
   (pat-refs/e pp-pat l-enums unused/e)))

;; (: pat-refs/e : Pat (HashTable Symbol (Enum Pat)) (Enum Symbol) -> Enum RefPat)
(define (pat-refs/e pat nt-enums unused/e)
  (define (loop pat)
    (match-a-pattern
     pat
     [`any any/e]
     [`number num/e]
     [`string string/e]
     [`natural nats/e]
     [`integer integer/e]
     [`real real/e]
     [`boolean bool/e]
     [`variable var/e]
     [`(variable-except ,s ...)
      (apply except/e var/e s)]
     [`(variable-prefix ,s)
      (var-prefix/e s)]
     [`variable-not-otherwise-mentioned
      unused/e]
     [`hole (const/e the-hole)]
     [`(nt ,id)
      (hash-ref nt-enums id)]
     [`(name ,n ,pat)
      (const/e (name-ref n))]
     [`(mismatch-name ,n ,tag)
      ;; (const/e (misname-ref n tag))
      (unsupported "mismatch patterns")]
     [`(in-hole ,p1 ,p2)
      (map/e decomp
             (match-lambda
              [(decomp ctx term)
               (values ctx term)])
             (loop p1)
             (loop p2))]
     [`(hide-hole ,p)
      (map/e hide-hole
             hide-hole-term
             (loop p))]
     [`(side-condition ,p ,g ,e)
      (unsupported pat)]
     [`(cross ,s)
      (unsupported pat)]
     [`(list ,sub-pats ...)
      (list/e
       (for/list ([sub-pat (in-list sub-pats)])
         (match sub-pat
           [`(repeat ,pat #f #f)
            (map/e
             (λ (ts)
                (repeat (length ts)
                        ts))
             (λ (rep)
                (repeat-terms rep))
             (many/e (loop pat)))]
           [`(repeat ,tag ,n ,m)
            (const/e (nrep-ref n tag))]
           [else (loop sub-pat)])))]
     [(? (compose not pair?)) 
      (const/e pat)]))
  (loop pat))

(define/match (env/e nv l-enums unused/e)
  [((env names misnames nreps mreps) _ _)
   (define (val/e p)
     (pat-refs/e p l-enums unused/e))

   (define/match (misvals/e p-ts)
     [((cons p ts))
      (define p/e (val/e p))
      (dep-fold/e (λ (ts-excepts tag)
                     (define excepts
                       (map cdr ts-excepts))
                     (cons/e (const/e tag)
                             (apply except/e p/e excepts)))
                  (set->list ts))])
   
   (define/match (reprec/e nv-t)
     [((cons nv tpats))
      (define tpats/e
        (hash-traverse/e val/e tpats))
      (define env-tpats/e
        (cons/e (env/e nv l-enums unused/e)
                tpats/e))
      (many/e env-tpats/e)])
   (define/match (reprec-n/e nv-t n)
     [((cons nv tpats) _)
      (define tpats/e
        (hash-traverse/e val/e tpats))
      (define env-tpats/e
        (cons/e (env/e nv l-enums unused/e)
                tpats/e))
      (many/e env-tpats/e n)])

   (define (mreps/e mreps mrep-nreps)
     ;; lengths-table/e : Enum (Listof (Pairof Symbol Integer))
     (define lengths-table/e
       (hash-traverse/e (λ (xs)
                           (map/e (λ (xs ts) (map cons xs ts))
                                  (λ (xs-ts)
                                     (for/lists (xs ts)
                                                ([x-t (in-list xs-ts)])
                                         (values (car xs-ts) (cdr xs-ts))))
                                  (const/e xs)
                                  (many-distinct/e nats/e (length xs))))
                        mreps))
     (dep/e lengths-table/e
            (λ (mis-lengths-table)
               (define mis-lengths
                 (append* (hash-values mis-lengths-table)))
               (hash-seq/e
                (for/hash ([(n nv-t) (in-hash mrep-nreps)])
                  (define len (cdr (assoc n mis-lengths)))
                  (values n (reprec-n/e nv-t len)))))))
   
   (define names-env
     (hash-traverse/e val/e names))

   (define misnames-env
     (hash-traverse/e misvals/e misnames))

   (define invert-mreps
     (for/fold ([acc (hash)])
               ([(mname nnames) (in-hash mreps)])
       (hash-union acc
                   (for/hash ([nname (in-list nnames)])
                     (values nname mname))
                   (λ (k v1 v2)
                      (error 'hash-union "This shouldn't happen k=~s, v1=~s, v2=~s" k v1 v2)))))
   
   (define-values (non-mrep-nreps mrep-nreps)
     (for/fold ([non-mrep-nreps (hash)]
                [mrep-nreps (hash)])
               ([(k v) (in-hash nreps)])
       (cond [(hash-has-key? invert-mreps k)
              (values non-mrep-nreps (hash-set mrep-nreps k v))]
             [else
              (values (hash-set non-mrep-nreps k v) mrep-nreps)])))
   
   (define nreps-env
     (map/e
      (match-lambda**
       [(t1 (cons dep t2))
        (define t-union
          (for/fold ([t t1])
              ([(k v) (in-hash t2)])
            (hash-set t k v)))
        (cons dep t-union)])
      (match-lambda
       [(cons dep t)
        (define non-mrep-nreps/e
          (for/hash ([k (in-hash-keys non-mrep-nreps)])
            (values k (hash-ref t k))))
        (define mrep-nreps/e
          (for/hash ([k (in-hash-keys mrep-nreps)])
            (values k (hash-ref t k))))
        (values non-mrep-nreps/e
                (cons dep mrep-nreps/e))])
      (hash-traverse/e reprec/e non-mrep-nreps)
      (mreps/e mreps mrep-nreps)))
   
   
   (map/e
    t-env
    (match-lambda
     [(t-env  names misnames nreps)
      (values names misnames nreps)])
    names-env
    misnames-env
    nreps-env)])

;; to-term : (ann-pat t-env pat-with-refs) -> redex term
(define/match (to-term ap)
  [((ann-pat nv term))
   ((refs-to-fn term) nv)])

;; refs-to-fn : RefPat -> (TEnv -> Term)
(define (refs-to-fn refpat)
  (match refpat
    [(ann-pat _ _)
     (define term
       (to-term refpat))
     (λ (_) term)]
    [(decomp ctx-refs termpat-refs)
     (define ctx-fn (refs-to-fn ctx-refs))
     (define term-fn (refs-to-fn termpat-refs))
     (λ (nv)
        (define ctx (ctx-fn nv))
        (define term (term-fn term))
        (plug-hole ctx term))]
    [(hide-hole p)
     (define p-fn (refs-to-fn p))
     (λ (nv)
        (hide-hole (p-fn nv)))]
    [(name-ref n)
     (λ (nv)
        ((refs-to-fn (t-env-name-ref nv n)) nv))]
    [(misname-ref n tag)
     (λ (nv)
        ((refs-to-fn (t-env-misname-ref nv n tag)) nv))]
    [(list subrefpats ...)
     (define 1-t
       (compose
        append*
        (sequence-fn
         (for/list ([subrefpat (in-list subrefpats)])
           (match subrefpat
             [(repeat _ subs)
              (sequence-fn (map refs-to-fn subs))]
             [(nrep-ref n tag)
              (λ (nv)
                 (define env-ts (t-env-nrep-ref nv n))
                 (for/list ([nv-t (in-list env-ts)])
                   (match nv-t
                     [(cons nv tterms)
                      ((refs-to-fn (hash-ref tterms tag)) nv)])))]
             [_ (sequence-fn (list (refs-to-fn subrefpat)))])))))
     (λ (nv)
        (map (λ (tt) ((refs-to-fn tt) nv)) (1-t nv)))]
    [else (λ (_) refpat)]))

(define (plug-hole ctx term)
  (define (plug ctx)
    (match ctx
      [(? (curry eq? the-hole)) term]
      [(list ctxs ...) (map plug ctxs)]
      [_ ctx]))
  (define (unhide term)
    (match term
      [(list ctxs ...) (map unhide ctxs)]
      [(hide-hole term) (unhide term)]
      [_ term]))
  (unhide (plug ctx)))

;; (: sequence-fn : (All (a b) (Listof (a -> b)) -> (a -> (Listof b))))
(define (sequence-fn fs)
  (λ (x)
     (for/list ([f (in-list fs)])
       (f x))))
