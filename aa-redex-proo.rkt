#lang racket
(require "aa-redex-core.rkt")
(require "aa-redex-type.rkt")
(require "aa-redex-util.rkt")

(require redex/reduction-semantics)

(provide (all-defined-out))

(define-extended-language aa-proof aa
  [obl #|igation|# (Γ H ⊩ P)] ;; P mustn't contain any val=s
  [obls (obl ...)]
  
  [(C P H) ....
           (val= z qlit)
           (size-bounded-by s bound)]
  [bound zero one zero-or-one one+ zero+]
  [qb bound ⊥]
  [B ε (B X qb qb)]
  
  
  
  )

;; based on the aa-machine version in -util...
(define-syntax-rule (test-matches-proo actual expected)
  (let ((expected-for-printing `expected))
    (test-equal
     (or (only-or-false ((term-match aa-proof
                                     [expected expected-for-printing])
                         actual))
         actual #| to print out a sensible error message |#)
     expected-for-printing)))

(define-metafunction aa-proof
  not-lookup-C : C x -> any
  [(not-lookup-C C x) (equal?- C (subst-in-C C ((x ,(gensym)))))])

(define-metafunction aa-proof
  apply-C : C x -> C
  [(apply-C C x) (subst-in-C C ((· x)))])

(define-metafunction aa-proof
  subst-var : z subs -> z
  [(subst-var z ((z_f-pre z_t-pre) ... (z z_to) (z_f-post z_t-post) ...))
   z_to]
  [(subst-var z subs) z])

;; TODO: write these down
(define-metafunction aa-proof
  subst-in-C : C subs -> C
  [(subst-in-C true subs) true]
  [(subst-in-C (∧ C ...) subs) (∧ (subst-in-C C subs) ...)]
  [(subst-in-C (val= z qlit) subs)
   (val= (subst-var z subs) (subst-in-qlit qlit subs))]
  [(subst-in-C (any s ...) subs) (any (subst-in-s s subs) ...)])

(define-metafunction aa-proof
  subst-in-s : s subs -> s
  [(subst-in-s ∅ subs) ∅]
  [(subst-in-s (any s ...) subs) (any (subst-in-s s subs) ...)]
  [(subst-in-s (ℱe Γ) subs) (ℱe (subst-in-Γ Γ subs))]
  [(subst-in-s (any z) subs) (any (subst-var z subs))])

(define-metafunction aa-proof
  subst-in-Γ : Γ subs -> Γ
  [(subst-in-Γ ε subs) ε]
  [(subst-in-Γ (z τ Γ) subs) ((subst-var z subs) τ (subst-in-Γ Γ subs))])

(define-metafunction aa-proof
  subst-in-qlit : qlit subs -> qlit
  [(subst-in-qlit z subs) (subst-var z subs)]
  [(subst-in-qlit (einj0 qlit τ) subs)
   (einj0 (subst-in-qlit qlit subs) τ)]
  [(subst-in-qlit (einj1 τ qlit) subs)
   (einj1 τ (subst-in-qlit qlit subs))]
  [(subst-in-qlit (eprod ((qlit β) ...) β_exp) subs)
   (eprod (( (subst-in-qlit qlit subs) β) ...) β_exp)])

(module+
    test
  
  (test-equal
   `(subst-in-C (= (ℱ x_a) (ℱ x_b)) ((x_a x_b) (x_b x_c))  )
   `(= (ℱ x_b) (ℱ x_c)))
  )


(define-judgment-form aa-proof
  #:contract (Γ . ⊢p . H e P obls)
  #:mode     (I . ⊢p . I I I O)
  
  [(where (#t ...) ((not-lookup Γ x) (not-lookup-C H x) (not-lookup-C P x)))
   ((extend Γ ((x Atom))) . ⊢p . (∧ H (dsj (ℱ x) (ℱe Γ))) e
                          (∧ P (dsj (ℱ x) (ℱ ·))) obls)
   ---------------------------------------------------------------- ;; P-Fresh
   (Γ . ⊢p . H (efresh x e) P obls)]
  
  [(where (#t ...) ((not-lookup Γ x_sub) ...
                    (not-lookup-C H x_sub) ...
                    (not-lookup-C P x_sub) ...))
   (Γ . ⊢ty . x_whole τ)
   (where (Prod ((τ_sub β_sub) ...) β_export) (unfold-τ τ))
   ((extend Γ ((x_sub τ_sub) ...)) . ⊢p .
                                   (∧ H (∧ (dsj (ℱx x_whole) (ℱe Γ))
                                           (val= x_whole (eprod ((x_sub β_sub) ...) β_export))))
                                   e
                                   (∧ P (dsj (ℱx x_whole) (ℱ ·)))
                                   (obl ...))
   ----------------------------------------------------------------- ;; P-Open
   (Γ . ⊢p . H (eopen x_whole (x_sub ...) e) P (obl ...))]
  
  
  [(where ((fD_before ... ;; retrieve definition of `f`
            (define-fn f ((x_formal τ_arg) ...) C_pre τ_ret e_body C_post)
            fD_after ...))
          (,@(list (fn-defs)))) ;; sneak the fDs from a parameter
   (where obl_pre (Γ H ⊩ (subst-in-C C_pre ((x_formal x_actual) ...))))
   (where obl_invoc ((extend Γ ((· τ_ret)))
                     (∧ H
                        (∧ (⊆ (ℱ ·) (ℱe (extend ε ((x_actual τ_arg) ...))))
                           (subst-in-C C_post ((x_formal x_actual) ...))))
                     ⊩ P))
   ----------------------------------------------------------------- ;; P-Call
   (Γ . ⊢p . H (ecall f x_actual ...) P (obl_pre obl_invoc))]
  
  [(where (#t ...) ((not-lookup Γ x) (not-lookup-C H x) (not-lookup-C P x)))
   (Γ . ⊢p . H e_val C (obl_val ...))
   (Γ . ⊢ty . e_val τ_val)
   ((extend Γ ((x τ_val))) . ⊢p .
                           (∧ H
                              (∧ (apply-C C x) (⊆ (ℱ x) (ℱe Γ)))) e_body P (obl_body ...))
   ------------------------------------------------------------------ ;; P-Let
   (Γ . ⊢p . H (elet x C e_val e_body) P (obl_val ... obl_body ...))]
  
  ;; TODO mention in paper: (val= x x_l) ≡ (val= x (inj0 x_l)), which is what
  ;; we really mean.
  [(Γ . ⊢ty . x τ)
   (where (+ τ_l τ_r) (unfold-τ τ))
   ((extend Γ ((x_l τ_l))) . ⊢p . (∧ H (val= x (einj0 x_l τ_r))) e_l P (obl_l ...))
   ((extend Γ ((x_r τ_r))) . ⊢p . (∧ H (val= x (einj1 τ_l x_r))) e_r P (obl_r ...))
   ----------------------------------------------------------------- ;; P-Case
   (Γ . ⊢p . H (ecase x x_l e_l x_r e_r) P (obl_l ... obl_r ...))]
  
  [(Γ . ⊢p . (∧ H (= (ℱ x_l) (ℱ x_r))) e_yes P (obl_yes ...))
   (Γ . ⊢p . (∧ H (dsj (ℱ x_l) (ℱ x_r))) e_no P (obl_no ...))
   ----------------------------------------------------------------- ;; P-IfEq
   (Γ . ⊢p . H (eifeq x_l x_r e_yes e_no) P (obl_yes ... obl_no ...))]
  
  [(Γ . ⊢ty . qlit τ)
   -------------------------------------- ;; P-QLit
   (Γ . ⊢p . H qlit P (((extend Γ ((· τ))) (∧ H (val= · qlit)) ⊩ P)))]
  )

(define (obls-of e [Γ `ε])
  (if (only-or-false (judgment-holds (,Γ . ⊢ty . ,e τ) τ))
      (only (judgment-holds (,Γ . ⊢p . true ,e true obls) obls))
      (error "expression doesn't typecheck: " e)))

(define-metafunction aa-proof 
  obls-of-fd : fD -> obls
  [(obls-of-fd (define-fn f ((x τ) ...) H τ_r e P))
   ,(only (judgment-holds (Γ . ⊢p . H e P obls) obls))
   (where Γ (nested-Γ ((x τ) ...)))
   (where τ_r ,(only-or-false (judgment-holds (Γ . ⊢ty . e τ_ty) τ_ty)))
   (side-condition (and (not (equal? (term τ_r) false)) (begin #;(display (term τ_r)) true)))]
  [(obls-of-fd (define-fn f ((x τ) ...) P τ_r e H))
   ,(error (format "function ~a typechecks to wrong return type: ~a \n instead of: ~a \n under environment: ~a"
                   (term f) (term τ_ty) (term τ_r) (term Γ)))
   (where Γ (nested-Γ ((x τ) ...)))
   (where (τ_ty) ,(judgment-holds (Γ . ⊢ty . e τ_ty) τ_ty))]
  [(obls-of-fd (define-fn f ((x τ) ...) P τ_r e H))
   ,(error (format "function ~a doesn't typecheck: ~a \n under environment: ~a, fndefs ~a"
                   (term f) (term e) (term Γ) (fn-defs)))
   (where Γ (nested-Γ ((x τ) ...)))])

(define-metafunction aa-proof
  nested-Γ : ((x τ) ...) -> Γ
  [(nested-Γ ((x τ) (x_r τ_r) ...))
   (x τ (nested-Γ ((x_r τ_r) ...)))]
  [(nested-Γ ()) ε])


(define-metafunction aa-proof
  simplify-obl : obl -> obl
  [(simplify-obl (Γ H ⊩ P))
   (Γ (simplify-Cs Γ (simplify-C-big Γ H)) ⊩ (simplify-Cs Γ (simplify-C-big Γ P)))])

(define-metafunction aa-proof
  simplify-C-big : Γ C -> (C ...)
  [(simplify-C-big Γ (∧ C_l C_r))
   ,(append (term (simplify-C-big Γ C_l)) (term (simplify-C-big Γ C_r)))]
  [(simplify-C-big Γ C) (C)])

(define-metafunction aa-proof
  simplify-Cs : Γ (C ...) -> C
  [(simplify-Cs Γ (C ...))
   (simplify-C Γ (big ∧ ,(remove-duplicates (map (lambda (c) (term (simplify-C Γ ,c))) (term (C ...))))))])

(define-metafunction aa-proof
  simplify-C : Γ C -> C
  [(simplify-C Γ (∧ C_l C_r))
   (∧ (simplify-C Γ C_l) (simplify-C Γ C_r))
   #;(simplify-∧ Γ (simplify-C Γ C_l) (simplify-C Γ C_r))] ;;removed for environment/syntax data matching
  [(simplify-C Γ true)
   true]
  [(simplify-C Γ (ss→C s_l s_r)) 
   (simplify-ss→C Γ ss→C (simplify-s Γ s_l) (simplify-s Γ s_r))]
  [(simplify-C Γ (size-bounded-by s bound))
   (size-bounded-by (simplify-s Γ s) bound)]
  [(simplify-C Γ C) C])

(define-metafunction aa-proof
  simplify-∧ : Γ C C -> C
  [(simplify-∧ Γ true true) true]
  [(simplify-∧ Γ true C) C]
  [(simplify-∧ Γ C true) C]
  [(simplify-∧ Γ C_l C_r) (∧ C_l C_r)])

(define-metafunction aa-proof
  simplify-ss→C : Γ ss→C s s -> C
  [(simplify-ss→C Γ = s s) true]
  [(simplify-ss→C Γ ⊆ s s) true]
  [(simplify-ss→C Γ ss→C s_l s_r) (ss→C s_l s_r)])

(define-metafunction aa-proof
  simplify-s : Γ s -> s
  [(simplify-s Γ ∅) ∅]
  [(simplify-s Γ (ss→s s_l s_r)) 
   (simplify-ss→s Γ ss→s (simplify-s Γ s_l) (simplify-s Γ s_r))]
  [(simplify-s Γ (¬ s)) (¬ s)]
  [(simplify-s Γ (z→s z)) (z→s z)]
  [(simplify-s Γ (ℱe Γ_e)) (ℱe Γ_e)])

(define-metafunction aa-proof
  simplify-ss→s : Γ ss→s s s -> s
  [(simplify-ss→s Γ ∪ s s) s]
  [(simplify-ss→s Γ ∪ s ∅) s]
  [(simplify-ss→s Γ ∪ ∅ s) s]
  [(simplify-ss→s Γ ∩ s s) s]
  [(simplify-ss→s Γ ∩ s ∅) ∅]
  [(simplify-ss→s Γ ∩ ∅ s) ∅]
  [(simplify-ss→s Γ ∖ s s) ∅]
  [(simplify-ss→s Γ ∖ s ∅) s]
  [(simplify-ss→s Γ ∖ ∅ s) ∅]
  [(simplify-ss→s Γ ss→s s_l s_r) (ss→s s_l s_r)])

(module+
    test
  (define id-fn (term (define-fn id ((x Atom)) true Atom x true)))
  (parameterize
      ((fn-defs `(,id-fn)))
    (test-equal #t (not (equal? #f (only-or-false (judgment-holds ((x Atom ε) . ⊢ty . (ecall id x) τ_ty) τ_ty))))))
  
  (test-matches-proo
   (obls-of `(efresh x_a (efresh x_b (eprod ((x_a ∅) (x_b ∅)) ∅))))
   
   (((· (Prod ((Atom ∅) (Atom ∅)) ∅) (x_b Atom (x_a Atom ε))) ;; Γ
     (∧ (∧ (∧ true (dsj (ℱ x_a) (ℱe ε))) ;; H
           (dsj (ℱ x_b) (ℱe (x_a Atom ε))))
        (val= · (eprod ((x_a ∅) (x_b ∅)) ∅)))
     ⊩ ;; incidentally, this should be unsatisfiable
     (∧ (∧ true (dsj (ℱ x_a) (ℱ ·))) ;; P
        (dsj (ℱ x_b) (ℱ ·))))))
  
  (define (C-contains C C-needle)
    (match C
      [`(∧ ,C_l ,C_r) (or (C-contains C_l C-needle)
                          (C-contains C_r C-needle))]
      [_ (equal? C C-needle)]))
  
  (define (test-contains obls Hses Pses)
    (for-each (λ (obl Hs Ps)
                (match obl
                  [`(,Γ ,H ⊩ ,P)
                   ;; is the test itself broken?
                   ;; (comment out when tests are passing)
                   (for-each (λ (H-expected)
                               (test-matches-proo H-expected C)) Hs)
                   (for-each (λ (P-expected)
                               (test-matches-proo P-expected C)) Ps)
                   
                   (test-equal
                    (list (filter (λ (H-needle) (C-contains H H-needle)) Hs)
                          (filter (λ (P-needle) (C-contains P P-needle)) Ps))
                    (list Hs Ps))]))
              obls Hses Pses))
 
  
  (test-contains
   ;; this ought to be satisfiable
   (obls-of
    `(efresh x_outer (elet x_let (= (ℱ ·) (ℱ x_outer))
                           x_outer
                           (eprod ((x_outer 0) (x_let ∅)) ∅))))
   `(((dsj (ℱ x_outer) (ℱe ε)) (val= · x_outer))
     ((dsj (ℱ x_outer) (ℱe ε)) (val= · (eprod ((x_outer 0)(x_let ∅)) ∅))))
   
   `((#|C:|# (= (ℱ ·) (ℱ x_outer)) )
     (#|P:|# (dsj (ℱ x_outer) (ℱ ·))))
   )
  
  (define exp-ty `(Prod ((Atom ∅) (Atom ∅)) (⊎ 0 1)))
  (define mk-bndr-fD
    `(define-fn mk-bndr ((x_a Atom) (x_b Atom)) (dsj (ℱ x_a) (ℱ x_b))
       ,exp-ty
       (eprod ((x_a ∅) (x_b ∅)) (⊎ 0 1)) ;; make a prod that exports both xes
       (= (ℱb ·) (∪ (ℱ x_a) (ℱ x_b))))) ;; postcondition
  
  (parameterize
      ((fn-defs `(,mk-bndr-fD)))
    
    (test-contains
     ;; this ought to be unsatisfiable
     (obls-of
      `(efresh x_c (efresh x_d (ecall mk-bndr x_c x_d))))
     
     ;; ecall duplicates its H, but only requires its P once
     `(( (dsj (ℱ x_c) (ℱe ε)) #|from 1st efresh|# )
       ( (dsj (ℱ x_c) (ℱe ε)) #|from 1st efresh|#
         (= (ℱb ·) (∪ (ℱ x_c) (ℱ x_d))))  #|from ecall's C_post|#)
     `(( (dsj (ℱ x_c) (ℱ x_d)) #| from ecall's C_pre |#)
       ( (dsj (ℱ x_c) (ℱ ·)) #|from 1st efresh|#)))
    
    (define ret-ty `(Prod ((Atom 2) (Atom 2) (,exp-ty ∅)) ∅))
    
    ;; test of elet and ecall
    (test-contains
     ;; this ought to be satisfiable
     (obls-of
      `(efresh x_c
               (efresh x_d
                       (elet x_bdr (= (ℱb ·)
                                      (∪ (ℱ x_c) (ℱ x_d)))
                             (ecall mk-bndr x_c x_d)
                             (eprod ((x_c 2) (x_d 2) (x_bdr ∅)) ∅)))))
     
     `( ;; H
       ( ;; at ecall's precondition
        (dsj (ℱ x_d) (ℱe (x_c Atom ε))) ;; from 2nd efresh
        )
       ( ;; at ecall's postcondition
        (dsj (ℱ x_d) (ℱe (x_c Atom ε))) ;; from 2nd efresh
        (= (ℱb ·) (∪ (ℱ x_c) (ℱ x_d))) ;; from postc of mk-bdr
        )
       ( ;; at eprod
        (dsj (ℱ x_d) (ℱe (x_c Atom ε))) ;; from 2nd efresh
        (⊆ (ℱ x_bdr) (ℱe (x_d Atom (x_c Atom ε)))) ;; from let
        (= (ℱb x_bdr) (∪ (ℱ x_c) (ℱ x_d))) ;; from C of let
        )
       )
     `( ;; P
       ( ;; at ecall's precondition
        (dsj (ℱ x_c) (ℱ x_d)) ;; from prec of mk-bdr
        )
       ( ;; at ecall's postcondition
        (= (ℱb ·) (∪ (ℱ x_c) (ℱ x_d))) ;; from C of let
        )
       ( ;; at eprod
        (dsj (ℱ x_d) (ℱ ·)) ;; from 2nd efresh
        )
       )
     )
    
    
    )
  
  
  ;; basic eopen test
  
  (define basic-Γ `(x_lam (Prod ((Atom 1) (Atom ∅)) ∅) ε))
  (define lam-τ `(Prod ((Atom 1) (Atom ∅)) ∅))
  
  (test-contains
   ;; should be satisfiable
   (obls-of
    `(eopen x_lam (x_arg x_body) (eprod ((x_body ∅) (x_arg 0)) ∅))
    basic-Γ)
   `(( (dsj (ℱx x_lam) (ℱe ,basic-Γ))
       (val= x_lam (eprod ((x_arg 1) (x_body ∅)) ∅))
       (val= · (eprod ((x_body ∅) (x_arg 0)) ∅))))
   
   `(( (dsj (ℱx x_lam) (ℱ ·)) )))
  
  
  
  
  (test-results)
  )


