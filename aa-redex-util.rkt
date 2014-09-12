#lang racket
(require redex/reduction-semantics)
(require "aa-redex-core.rkt")

(provide (all-defined-out))


#|
For debugging Redex judgment rules (, is forbidden, but ,@ is okay)

   (where (any ...) (,@(list (printf ">>~s<<" `x_l))))
|#

;; Redex memoizes metafunctions? Using an argument will give us the freshness
;; that we need.
(define-metafunction aa-machine
  fresh-for : any -> a
  [(fresh-for any) (atom ,(gensym))])


(define-syntax-rule (test-matches actual expected)
  (let ((expected-for-printing `expected))
    (test-equal
     (or (only-or-false ((term-match aa-machine
                                     [expected expected-for-printing])
                         actual))
         actual #| to print out a sensible error message |#)
     expected-for-printing)))


(define-metafunction aa-machine
  or- : any ... -> any
  [(or-) #f]
  [(or- any) any]
  [(or- #f any_cdr ...) (or- any_cdr ...)]
  [(or- any_car any_cdr ...) any_car])

(define-metafunction aa-machine
  and- : any ... -> any
  [(and-) #t]
  [(and- any) any]
  [(and- #f any_cdr ...) #f]
  [(and- any_car any_cdr ...) (and- any_cdr ...)])

(define-metafunction aa-machine
  equal?- : any any -> any
  [(equal?- any_a any_a) #t]
  [(equal?- any_a any_b) #f])

(define-metafunction aa-machine
  not- : any -> any
  [(not- #f) #t]
  [(not- any) #f])

;; turn a binary operator into an n-ary operator
(define-metafunction aa-machine
  ;; really, it takes an operator and a sequence of `C`s or `s`es
  big : any (any ...) -> any
  [(big ∪ ()) ∅]
  ;; [(big ∩ ()) (¬ ∅)] ;; Let's not have infinite sets
  [(big ∧ ()) true]
  [(big ∨ ()) (≠ ∅ ∅)]
  [(big any_op (any_arg)) any_arg]
  [(big any_op (any_car any_cdr ...))
   (any_op any_car (big any_op (any_cdr ...)))])

(define-metafunction aa-machine
  bindspec->list : β -> (natural ...)
  [(bindspec->list ∅) ()]
  [(bindspec->list (⊎ β_l β_r))
   ,(append (term (bindspec->list β_l)) (term (bindspec->list β_r)))]
  [(bindspec->list(@ β_l β_r))
   ,(append (term (bindspec->list β_l)) (term (bindspec->list β_r)))]
  [(bindspec->list ℓ) (ℓ)])

(define-metafunction aa-machine
  number-list : (any ...) -> ((any natural) ...)
  [(number-list (any ...))
   ,(map list (term (any ...))
         (build-list (length (term (any ...))) (lambda (x) x)))])

(module+
    test
  
  (test-equal `(or- #f #f 0 1 #f) 0)
  (test-equal `(or- #f #f #f) #f)
  (test-equal `(and- #f #f 0 #f) #f)
  (test-equal `(and- 0 1 2 3 4) 4)
  (test-equal `(and- 0 1 2 3 #f) #f)
  
  (test-equal `(number-list (a b c)) `((a 0) (b 1) (c 2)))
  (test-equal `(bindspec->list ∅) empty)
  (test-equal `(bindspec->list 3) `(3))
  (test-equal `(bindspec->list (⊎ 1 2)) `(1 2))
  (test-equal `(bindspec->list (@ 5 3)) `(5 3))
  
  (test-results))
