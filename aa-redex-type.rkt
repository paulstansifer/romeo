#lang racket
(require redex/reduction-semantics)

(require "aa-redex-core.rkt")

(provide (all-defined-out))
#;(provide ⊢ty lookup not-lookup extend typecheck-program typeof unfold-τ fold-τ)

(define-metafunction aa-machine
  lookup : Γ z -> τ
  [(lookup ε z) ,(error "not found in type environment:" `z)]
  [(lookup (z τ Γ) z) τ]
  [(lookup (z_not-it τ Γ) z) (lookup Γ z)])

(define-metafunction aa-machine
  not-lookup : Γ z -> any
  [(not-lookup ε z) #t]
  [(not-lookup (z τ Γ) z) #f]
  [(not-lookup (z_not-it τ Γ) z) (not-lookup Γ z)])

(define-metafunction aa-machine
  extend : Γ ((z τ) ...) -> Γ
  [(extend Γ ()) Γ]
  [(extend Γ ((z_car τ_car) (z_cdr τ_cdr) ...))
   (z_car τ_car (extend Γ ((z_cdr τ_cdr) ...)))])


(define-metafunction aa
  subst-in-τ : τ X τ_replace -> τ
  [(subst-in-τ Atom X τ_replace) Atom]
  [(subst-in-τ RefAtom X τ_replace) RefAtom]
  [(subst-in-τ (+ τ_l τ_r) X τ_replace)
   (+ (subst-in-τ τ_l X τ_replace) (subst-in-τ τ_r X τ_replace))]
  [(subst-in-τ (Prod ((τ_sub β_↓) ...) β_⇑) X τ_replace)
   (Prod (( (subst-in-τ τ_sub X τ_replace) β_↓) ...) β_⇑)]
  [(subst-in-τ (μ X τ) X τ_replace) (μ X τ)]
  [(subst-in-τ (μ X_other τ) X τ_replace)
   (μ X_other (subst-in-τ τ X (rec-subst τ_replace X_other)))
   #;(μ X_other (subst-in-τ τ X τ_replace))]
  [(subst-in-τ X X τ_replace) τ_replace]
  [(subst-in-τ X_other X τ_replace) X_other])

(define-metafunction aa
  flatten-τ : τ -> τ
  [(flatten-τ Atom) Atom]
  [(flatten-τ RefAtom) RefAtom]
  [(flatten-τ (+ τ_l τ_r))
   (+ (flatten-τ τ_l) (flatten-τ τ_r))]
  [(flatten-τ (Prod ((τ_sub β_↓) ...) β_⇑))
   (Prod (((flatten-τ τ_sub) β_↓) ...) β_⇑)]
  [(flatten-τ (μ X τ))
   (μ X (flatten-τ (rec-subst τ X)))]
  [(flatten-τ X) X])

(define-metafunction aa
  rec-subst : τ X -> τ
  [(rec-subst Atom X) Atom]
  [(rec-subst RefAtom X) RefAtom]
  [(rec-subst (+ τ_l τ_r) X)
   (+ (rec-subst τ_l X) (rec-subst τ_r X))]
  [(rec-subst (Prod ((τ_sub β_↓) ...) β_⇑) X)
   (Prod (( (rec-subst τ_sub X) β_↓) ...) β_⇑)]
  [(rec-subst (μ X τ) X) X]
  [(rec-subst (μ X_other τ) X)
   (μ X_other (rec-subst τ X))]
  [(rec-subst X X) X]
  [(rec-subst X_other X) X_other])

(define-metafunction aa
  unfold-τ : τ -> τ
  [(unfold-τ (μ X τ)) (flatten-τ (subst-in-τ τ X (μ X τ)))]
  [(unfold-τ τ) (flatten-τ τ)])

(define-metafunction aa
  fold-τ : τ -> τ
  [(fold-τ τ) (fold-τ-search (flatten-τ τ) (flatten-τ τ) ())])

(define-metafunction aa
  fold-τ-search : τ τ (X ...) -> τ
  [(fold-τ-search τ_arg (μ X τ) (X_seen ...))
   (μ X τ_fold)
   (where τ_fold τ)
   (where τ_arg (subst-in-τ τ_fold X (μ X τ_fold)))]
  [(fold-τ-search τ_arg (μ X τ) (X_sl ... X X_sr ...))
   τ_arg]
  [(fold-τ-search τ_arg (μ X τ) (X_seen ...))
   τ_exp
   (where τ_fold τ)
   (where τ_exp (fold-τ-search τ_arg (subst-in-τ τ_fold X (μ X τ_fold)) (X X_seen ...)))]
  [(fold-τ-search τ_arg (+ τ_l τ_r) (X_seen ...))
   τ_folded
   (where τ_folded (fold-τ-search τ_arg τ_l (X_seen ...)))
   (side-condition (not (equal? (term τ_arg) (term τ_folded))))]
  [(fold-τ-search τ_arg (+ τ_l τ_r) (X_seen ...))
   (fold-τ-search τ_arg τ_r (X_seen ...))]
  [(fold-τ-search τ_arg (Prod ((τ_l β_l) ... (τ β) (τ_r β_r) ...) β_o) (X_seen ...))
   τ_folded
   (where τ_folded (fold-τ-search τ_arg τ (X_seen ...)))
   (side-condition (not (equal? (term τ_arg) (term τ_folded))))
   (where (#t ...) ((τ=? τ_arg (fold-τ-search τ_arg τ_l (X_seen ...))) ...))]
  [(fold-τ-search τ_arg τ (X_seen ...))
   τ_arg])

(define-metafunction aa
  τ=? : τ τ -> #t or #f
  [(τ=? τ τ) #t]
  [(τ=? τ_l τ_r) #f])

(module+
 test

 (test-equal
  `(unfold-τ (μ AtomList (+ (Prod ((Atom ∅) (AtomList ∅)) ∅) (Prod () ∅))))
  `(+
    (Prod ((Atom ∅)
           ((μ AtomList (+ (Prod ((Atom ∅) (AtomList ∅)) ∅) (Prod () ∅))) ∅))
          ∅)
    (Prod () ∅)))
 )

;; TODO at least tell an iso/equi recursive type story.
(define-judgment-form aa-machine
  #:mode     (I . ⊢ty . I O)
  #:contract (Γ . ⊢ty . e τ)

  [(where #t (not-lookup Γ x))
   ((extend Γ ((x Atom))) . ⊢ty . e τ)
   ----------------------------------- ;T-Fresh
   (Γ . ⊢ty . (efresh x e) τ)]
  
  [(Γ . ⊢ty . x Atom)
   ----------------------------------- ;T-Ref
   (Γ . ⊢ty . (ref x) RefAtom)]

  [(where (Prod ((τ_child β) ...) β_export) (unfold-τ (lookup Γ x)))
   (where (#t ...) ((not-lookup Γ x_child) ...))
   ((extend Γ ((x_child τ_child) ...)) . ⊢ty . e τ)
   ------------------------------------------------------ ; T-Open
   (Γ . ⊢ty . (eopen x (x_child ...) e) τ)]

  [(where ((fD_before ... ;; retrieve definition of `f`
           (define-fn f ((x_formal τ_arg) ...) C_pre τ_ret e_body C_post)
           fD_after ...))
          (,@(list (fn-defs)))) ;; sneak the fDs from a parameter
   (where (τ_arg ...) ((lookup Γ x_actual) ...))
   ------------------------------------------------------------------- ;T-Call
   (Γ . ⊢ty . (ecall f x_actual ...) τ_ret)]

  [(where #t (not-lookup Γ x))
   (Γ . ⊢ty . e_x τ_x)
   ((extend Γ ((x τ_x))) . ⊢ty . e_body τ_body)
   ------------------------------------------ ; T-Let
   (Γ . ⊢ty . (elet x C e_x e_body) τ_body)]

  [(where (+ τ_left τ_right) (unfold-τ (lookup Γ x)))
   ((extend Γ ((x_left τ_left))) . ⊢ty . e_left τ)
   ((extend Γ ((x_right τ_right))) . ⊢ty . e_right τ)
   ----------------------------------------------------- ; T-Case
   (Γ . ⊢ty . (ecase x x_left e_left x_right e_right) τ)]

  [(where Atom (lookup Γ x_0))
   (where Atom (lookup Γ x_1))
   (Γ . ⊢ty . e_0 τ)
   (Γ . ⊢ty . e_1 τ)
   ----------------------------------- ; T-IfEq
   (Γ . ⊢ty . (eifeq x_0 x_1 e_0 e_1) τ)]
  
  [(where RefAtom (lookup Γ x_0))
   (where RefAtom (lookup Γ x_1))
   (Γ . ⊢ty . e_0 τ)
   (Γ . ⊢ty . e_1 τ)
   ----------------------------------- ; T-IfEq
   (Γ . ⊢ty . (eifeq x_0 x_1 e_0 e_1) τ)]

  [(Γ . ⊢ty . qlit τ) ...
   ------------------------------------------------------- ; T-Prod
   (Γ . ⊢ty . (eprod ((qlit β_imp) ...) β_exp) (fold-τ (Prod ((τ β_imp) ...) β_exp)))]

  [(Γ . ⊢ty . qlit τ_left)
   ------------------------------------------ ; T-Inj0
   (Γ . ⊢ty . (einj0 qlit τ_right) (fold-τ (+ τ_left τ_right)))]

  [(Γ . ⊢ty . qlit τ_right)
   ------------------------------------------ ; T-Inj1
   (Γ . ⊢ty . (einj1 τ_left qlit) (fold-τ (+ τ_left τ_right)))]

  [(where τ (lookup Γ x))
   ---------------------- ; T-Var
   (Γ . ⊢ty . x τ)]
  )

(module+
 test
 (test-equal (judgment-holds
              (ε . ⊢ty .
                 (efresh x (efresh y (einj0 (eprod ((x ∅) (y 0)) ∅) Atom)))
                 (+ (Prod ((Atom ∅) (Atom 0)) ∅) Atom)))
             #t)

 (test-equal (judgment-holds
              (ε . ⊢ty .
                 (efresh x (efresh y (einj1 Atom (eprod ((x ∅) (y 0)) ∅))))
                 (+ (Prod ((Atom ∅) (Atom 0)) ∅) Atom)))
             #f))

(define-metafunction aa
  typeof : Γ e -> τ
  [(typeof Γ e)
   ,(match (only-or-false (judgment-holds (Γ . ⊢ty . e τ) τ))
      [#f (error fn-defs)]
      [x x])])

(define (typecheck-program prog [env '()])
  (match prog
         [`((,fD ...) ,e)
          (and (andmap ;;check function definitions
                (match-lambda
                 [`(define-fn ,f (,formals ...) ,C-pre ,τ-expected ,e ,C-post)
                  (equal?
                   τ-expected
                   (only
                    (judgment-holds ((extend ε ,formals) . ⊢ty . ,e τ)
                                    τ)))])
                fD)
               (parameterize  ;;... and the program body
                ((fn-defs fD))
                (only-or-false
                 (judgment-holds ((extend ε ,env) . ⊢ty . ,e τ) τ))))]))




(module+
 test

 (define f1-fD
   `(define-fn f1 ((x1 Atom) (x2 (+ Atom (Prod ((Atom ∅)) ∅)))) true
      (Prod ((Atom 2) (Atom 2) (Atom ∅)) ∅)
      (efresh x3
              (ecase x2
                     x2-atom (eprod ((x1 2) (x2-atom 2) (x2-atom ∅)) ∅)
                     x2-prod (eopen x2-prod (x2-atom)
                                    (eprod ((x1 2) (x3 2) (x3 ∅)) ∅))))
      true))

 (test-equal
  (typecheck-program
   `((,f1-fD)
     (efresh x1 (efresh x2
                        (elet x3 true
                              (einj0 x1 (Prod ((Atom ∅)) ∅))
                              (ecall f1 x2 x3))))))
  `(Prod ((Atom 2) (Atom 2) (Atom ∅)) ∅))

 (test-equal
  (typecheck-program
   `((,f1-fD)
     (efresh x1 (efresh x2
                        (elet x3 true
                              (einj0 x1 (Prod ((Atom 0)) ∅))
                              (ecall f1 x2 x3))))))
  #f)



 (test-equal
  (typecheck-program
   `((,f1-fD)
     (efresh x1
             (efresh x2
                     (elet x3 true
                           (einj0 x1 (Prod ((Atom ∅)) ∅))
                           (elet open-me true
                                 (ecall f1 x2 x3)
                                 (eopen open-me
                                        (x4 x5 x6)
                                        (eifeq x4 x5
                                               (ecase x3 x3-l x3-l x3-r x1)
                                               x6))))))))
  `Atom)


 (test-equal
  (typecheck-program
   `((,f1-fD)
     (ecall f1 x2 x3))
   `((x1 Atom) (x2 Atom) (x3 (+ Atom (Prod ((Atom ∅)) ∅)))))
  `(Prod ((Atom 2) (Atom 2) (Atom ∅)) ∅))

  (test-equal
   (typecheck-program
    `((,f1-fD)
      (elet x3 true (einj0 x1 (Prod ((Atom ∅)) ∅))
            (ecall f1 x2 x3)))
    `((x1 Atom) (x2 Atom)))
   `(Prod ((Atom 2) (Atom 2) (Atom ∅)) ∅))

  (test-results))