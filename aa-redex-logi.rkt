#lang racket
(require "aa-redex-core.rkt")
(require "aa-redex-util.rkt")
(require "aa-redex-type.rkt")
(require "aa-redex-proo.rkt")

(require redex/reduction-semantics)
(provide (all-defined-out))

;; Partially-evaluate `z→s` (ℱ, ℱr, ℱb, or ℱx) on `qlit`
;; Sadly, we need the type for just one case: we need to know if
;; a var ref that gets imported is an Atom (because we don't write down
;; a distinction between atoms that are binders and atoms that are refs.)
(define-metafunction aa
  pe-fn : z→s qlit τ -> s
  ;; unfold μX.τ
  [(pe-fn z→s qlit (μ X τ)) ;;qlit was x - why? --FM
   (pe-fn z→s qlit (unfold-τ (μ X τ)))]

  ;; all atom sets are unchanged under injection
  [(pe-fn z→s (einj0 qlit τ_other) (+ τ τ_r))
   (pe-fn z→s qlit τ)
   (where τ_fold (fold-τ τ_other))
   (where τ_fold (fold-τ τ_r))]
  [(pe-fn z→s (einj1 τ_other qlit) (+ τ_l τ))
   (pe-fn z→s qlit τ)
   (where τ_fold (fold-τ τ_other))
   (where τ_fold (fold-τ τ_l))]

  [(pe-fn ℱr (ref x) RefAtom)
   (ℱb x)]
  
  [(pe-fn ℱb (ref x) RefAtom)
   ∅]
  
  [(pe-fn ℱ (ref x) RefAtom)
   (ℱb x)]
  
  [(pe-fn ℱr x Atom)
   ∅]
  
  [(pe-fn ℱb x Atom)
   (ℱb x)]
  
  [(pe-fn ℱr x RefAtom)
   (ℱr x)]
  
  [(pe-fn ℱb x RefAtom)
   ∅]
  
  [(pe-fn ℱ x Atom)
   (ℱb x)]
  
  [(pe-fn ℱ x RefAtom)
   (ℱr x)]
  
  ;; eliminate ℱ
  [(pe-fn ℱ qlit τ)
   (∪ (pe-fn ℱb qlit τ) (pe-fn ℱr qlit τ))]


  ;; products:
  [(pe-fn ℱb (eprod ((qlit_sub β_↓) ..._0) β_⇑)
          (Prod ((τ_sub β_↓) ..._0) β_⇑))
   (〚〛-syn β_⇑ ((pe-fn ℱb qlit_sub τ_sub) ...))]

  [(pe-fn ℱr (eprod ((qlit_sub  β_↓) ..._0) β_⇑)
          (Prod ((τ_sub β_↓) ..._0) β_⇑))
   (big ∪ ((∖ (pe-fn ℱr qlit_sub τ_sub) (〚〛-syn β_↓ ((pe-fn ℱb qlit_sub τ_sub) ...))) ...))
   #;(big ∪
        ,(map (λ (this-qlit this-τ this-β-↓ idx)
                (if (and (equal? `Atom this-τ)
                         `(or- (β-∈ ,idx β_⇑)
                               (β-∈ ,idx β_↓) ...)) ;; over *any* β_↓
                    `∅ ;; an atom that's not a reference
                    `(∖ (pe-fn ℱr ,this-qlit ,this-τ)
                        (〚〛-syn ,this-β-↓ ((pe-fn ℱb qlit_sub τ_sub) ...)))))
              `(qlit_sub ...) `(τ_sub ...) `(β_↓ ...) (idxes `(β_↓ ...))))]

  [(pe-fn ℱx (eprod ((qlit_sub β_↓) ..._0) β_⇑)
          (Prod ((τ_sub β_↓) ..._0) β_⇑))
   (∖ (big ∪ ((pe-fn ℱb qlit_sub τ_sub) ...)) (pe-fn ℱb (eprod ((qlit_sub β_↓) ...) β_⇑) (Prod ((τ_sub β_↓) ...) β_⇑)))
   #;,(let ((bind-map `((pe-fn ℱb qlit_sub τ_sub) ...)))
      `(∖ (big ∪ (exposable-sub ,bind-map (τ_sub ...) (β_↓ ... β_⇑)))
        (〚〛-syn β_⇑ ,bind-map)))]
  
  ;; base case (for all z→s that aren't ℱ
  [(pe-fn z→s x τ)
   (z→s x)])


;; TODO can we just define the underlying freeness functions in terms of this?

(module+
    test

  (test-equal
   `(pe-fn ℱ x Atom)
   `(ℱb x))

  (test-equal
   `(pe-fn ℱ x (μ X Atom))
   `(ℱb x))

  (test-equal
   `(pe-fn ℱb (eprod ((x ∅) (y ∅ ) ( (einj1 Atom (eprod ((z ∅)) 0)) ∅))
                     (@ 0 (@ 1 2)) )
           (Prod ((Atom ∅) (Atom ∅ ) ( (+ Atom (Prod ((Atom ∅)) 0)) ∅))
                 (@ 0 (@ 1 2))))
   `(∪ (ℱb x) (∪ (ℱb y) (ℱb z))))

  (test-equal
   `(pe-fn ℱr (eprod ((x (@ 1 2)) (y ∅) (p ∅)) ∅ )
           (Prod ((Atom (@ 1 2)) (Atom ∅) ((Prod ((Atom ∅) (Atom ∅)) 0) ∅)) ∅))
   `(∪ (∖ ∅ (∪ (ℱb y) (ℱb p))) (∪ (∖ ∅ ∅) (∖ (ℱr p) ∅))))

  )

(define-metafunction aa-proof
  rem-val=s-s : Γ s ((val= z qlit) ...) -> s
  [(rem-val=s-s Γ ∅ any) ∅]
  [(rem-val=s-s Γ (ss→s s_l s_r) any)
   (ss→s (rem-val=s-s Γ s_l any) (rem-val=s-s Γ s_r any))]

  ;; we know something about this `z`
  [(rem-val=s-s Γ (z→s z) (any_pre ... (val= z qlit) any_post ...))
   (rem-val=s-s Γ (pe-fn z→s qlit (typeof Γ qlit)) ;; actually use `pe-fn`
                (any_pre ... (val= z qlit) any_post ...))] ;; fact no longer necessary
  [(rem-val=s-s Γ (z→s z) any)  (z→s z)] ;; canonicalize to new name

  ;; deal with ℱe
  [(rem-val=s-s Γ (ℱe ε) any) ∅]
  [(rem-val=s-s Γ (ℱe (x τ Γ_cdr)) any)
   (∪ (rem-val=s-s Γ (ℱ x) any) (rem-val=s-s Γ (ℱe Γ_cdr) any))])

(define-metafunction aa-proof
  rem-val=s-C : Γ C ((val= z qlit) ...) -> C
  [(rem-val=s-C Γ (∧ C_l C_r) any) (∧ (rem-val=s-C Γ C_l any)
                                      (rem-val=s-C Γ C_r any))]
  [(rem-val=s-C Γ (ss→C s_l s_r) any) (ss→C (rem-val=s-s Γ s_l any)
                                            (rem-val=s-s Γ s_r any))]
  [(rem-val=s-C Γ true any) true]
  [(rem-val=s-C Γ (val= z qlit) any) true]) ;; `z` should no longer appear.

(define-metafunction aa-proof
  collect-val=s : C -> ((val= z qlit) ...)
  [(collect-val=s (∧ C_l C_r)) ,(append `(collect-val=s C_l)
                                        `(collect-val=s C_r))]
  [(collect-val=s (ss→C s_l s_r)) ()]
  [(collect-val=s true) ()]
  [(collect-val=s (val= z qlit)) ((val= z qlit))])

;; Together, `collect-val=s` and `rem-val=s-C` suffice to remove all
;; relationships between different `z`s.

;; This should be able to deal with types like μX. prod Atom (X + Atom)


(define-metafunction aa-proof
  obl-rem-val=s : obl -> obl
  [(obl-rem-val=s (Γ H ⊩ P))
   (Γ (rem-val=s-C Γ H (collect-val=s H)) ⊩
      (rem-val=s-C Γ P (collect-val=s H)))])


(module+
    test

  (define obl-Γ `(x_lam (Prod ((Atom 1) (Atom ∅)) ∅)
                        (x_body Atom
                                (x_var Atom ε))))
  (define basic-Γ `(x_lam (Prod ((Atom 1) (Atom ∅)) ∅) ε))

  ;; temporarily removed! the current defintion of exposable-atoms is awful
  #;(test-equal
   `(obl-rem-val=s
     (,obl-Γ
      (∧ (dsj (ℱx x_lam) (ℱe ,basic-Γ))
         (∧ (val= x_lam (eprod ((x_body 1) (x_var ∅)) ∅))
            (val= · (eprod ((x_var ∅) (x_body 0)) ∅))) )
      ⊩
      (dsj (ℱx x_lam) (ℱ ·))))

   `((x_lam (Prod ((Atom 1) (Atom ∅)) ∅) (x_body Atom (x_var Atom ε)))
     (∧ (dsj (∖ (∪ (ℱb x_var) ∅) ∅)
             (∪ (∪ ∅ (∪ (∖ (ℱr x_body) (ℱb x_var)) ∅)) ∅))
        (∧ true true))
     ⊩ (dsj (∖ (∪ (ℱb x_var) ∅) ∅)
            (∪ ∅ (∪ ∅ (∖ (ℱr x_body) (ℱb x_var)))))))
  )

(define-metafunction aa-proof
  lookup-B : B X -> (qb qb)
  [(lookup-B ε X) ,(error "not found in bounds environment: " `X)]
  [(lookup-B (B X qb_b qb_r) X) (qb_b qb_r)]
  [(lookup-B (B X_not-it qb_b qb_r) X) (lookup-B B X)])

(define-metafunction aa-proof
  〚〛-qb : β (qb ...) -> qb
  [(〚〛-qb ∅ (qb ...)) zero]
  [(〚〛-qb ℓ (qb ...)) ,(list-ref `(qb ...) `ℓ)]
  [(〚〛-qb (⊎ β_0 β_1) (qb ...))
   (∪̂ (〚〛-qb β_0 (qb ...))
       (〚〛-qb β_1 (qb ...)))]
  [(〚〛-qb (@ β_0 β_1) (qb ...))
   (∪̂ (〚〛-qb β_0 (qb ...))
       (〚〛-qb β_1 (qb ...)))])

(define-metafunction aa-proof
  ⊓ : qb qb -> qb ;; lattice meet
  [(⊓ qb qb) qb]
  [(⊓ ⊥ qb) qb]
  [(⊓ qb zero+) zero+]

  [(⊓ zero one) zero-or-one]
  [(⊓ zero-or-one one+) zero+]

  [(⊓ one one+) one+]
  [(⊓ zero zero-or-one) zero-or-one]

  [(⊓ one zero-or-one) zero-or-one]
  [(⊓ zero one+) zero+]

  [(⊓ qb_l qb_r) (⊓ qb_r qb_l)])

(define-metafunction aa-proof
  ∪̂ : qb qb -> qb ;; effect of set union on set size bound
  [(∪̂ ⊥ qb) ⊥]
  [(∪̂ qb ⊥) ⊥]

  ;; nonempty sets with finite max sizes
  [(∪̂ one one) one+]
  [(∪̂ zero-or-one zero-or-one) zero+]
  [(∪̂ zero-or-one one) zero+]
  [(∪̂ one zero-or-one) zero+]

  [(∪̂ zero one) one]
  [(∪̂ one zero) one]

  ;; hack: everything else happens to be the same as lattice meet
  [(∪̂ qb_l qb_r) (⊓ qb_l qb_r)])

(define-metafunction aa-proof
  big-∪̂ : (qb ...) -> qb
  [(big-∪̂ ()) zero]
  [(big-∪̂ (qb_car qb_cdr ...)) (∪̂ qb_car (big-∪̂ (qb_cdr ...)))])

(define-metafunction aa-proof
  ∖̂ : qb qb -> qb
  [(∖̂ ⊥ qb) ⊥]
  [(∖̂ qb ⊥) ⊥]

  [(∖̂ qb zero) qb]

  [(∖̂ zero qb) zero]
  [(∖̂ one qb) zero-or-one]
  [(∖̂ zero-or-one qb) zero-or-one]
  [(∖̂ one+ qb) zero+]
  [(∖̂ zero+ qb) zero+])

(define-metafunction aa-proof
  smallest-bounds : B X τ -> (qb qb)
  [(smallest-bounds B X τ)
   ;; to prove termination easier, just walk through the quasibounds in lattice order
   ,(let next-b ((qb-b `⊥))
      (define qb-b-next
        (only (judgment-holds ((B X ,qb-b zero+) . ⊢b . τ qb_b_next any) qb_b_next)))
      (if (eq? qb-b-next qb-b)
          ;; found fixpoint for binder bound; on to the ref bound
          (let next-r ((qb-r `⊥))
            (define qb-r-next
              (only (judgment-holds
                     ((B X ,qb-b ,qb-r) . ⊢b . τ any qb_r_next) qb_r_next)))
            (if (eq? qb-r-next qb-r)
                `(,qb-b ,qb-r)
                (next-r qb-r-next)))
          (next-b qb-b-next)))])

(define-syntax-rule (bounds-of τ)
  (only (judgment-holds (ε . ⊢b . τ qb_b qb_r) (qb_b qb_r))))

(module+
    test

  (test-equal
   `(smallest-bounds ε X Atom)
   `(one zero))

  (test-equal
   `(smallest-bounds ε X (+ X (+ Atom X)))
   `(one zero))

  (test-equal
   `(smallest-bounds ε X X) ;; non-contractive type
   `(⊥ ⊥))

  (test-equal
   (bounds-of (Prod () ∅))
   `(zero zero))

  (test-equal
   `(smallest-bounds ε X (Prod () ∅))
   `(zero zero))

  (test-equal
   (bounds-of (Prod ((Atom ∅)) ∅))
   `(zero zero))

  (test-equal
   (bounds-of (Prod ((Atom ∅) (Atom ∅)) 0))
   `(one zero))

  (define B11 `((ε X_r1 zero one) X_b1 one zero))

  (test-equal
   `(smallest-bounds ,B11 X (+ (Prod () ∅) (Prod ((X_b1 ∅) (X ∅)) (⊎ 0 1))))
   `(zero+ zero))

  (test-equal
   `(smallest-bounds ,B11 X (+ (Prod ((Atom ∅)) 0) (Prod ((X_b1 ∅) (X ∅)) (⊎ 0 1))))
   `(one+ zero))

  (test-equal
   `(smallest-bounds ,B11 X (+ Atom (Prod ((X_b1 ∅) (X ∅) (X_r1 1)) (⊎ 0 1))))
   `(one+ zero+))

  (test-equal
   (bounds-of (μ X (Prod (((μ Y (+ (Prod ((Atom ∅)) 0)
                                   (Prod ((Atom ∅) (Y ∅)) (@ 0 1)))) ∅)
                          ((+ Atom X) 0)) 0)))
   `(one+ zero))

  (test-equal
   (bounds-of (μ X (Prod (((μ Y (+ (Prod ((Atom ∅)) 0)
                                   (Prod ((Atom ∅) (Y ∅)) (@ 0 1)))) ∅)
                          ((+ Atom X) ∅)) 0)))
   `(one+ zero))

  (test-equal
   (bounds-of (μ X (+ Atom (Prod ((Atom ∅) (X 0)) 0))))
   `(one zero))

  ;; make sure that ∪̂ing with ⊥ denys having any information
  (test-equal
   (bounds-of (μ X (+ (Prod ((Atom ∅)) 0)
                      (Prod ((X ∅) ((Prod () ∅) ∅)) (⊎ 0 1)))))
   `(one zero))
  )


(define-judgment-form aa-proof
  #:contract (B . ⊢b . τ qb qb)
  #:mode (I . ⊢b . I O O)
  ;; first output is bound on size of free binders and the second is the bound on the
  ;; size of free references

  [
   ----------------------- ;; B-Atom
   (B . ⊢b . Atom one zero)]
  
  [
   ----------------------- ;; B-RefAtom
   (B . ⊢b . RefAtom zero one)]

  [(B . ⊢b . τ_l qb_b_l qb_r_l)
   (B . ⊢b . τ_r qb_b_r qb_r_r)
   ---------------------------------------------------------- ;; B-Sum
   (B . ⊢b . (+ τ_l τ_r) (⊓ qb_b_l qb_b_r) (⊓ qb_r_l qb_r_r))]

  [(B . ⊢b . τ qb_b qb_r) ...
   #;(where any_binder-map (qb_b ...)) ;; we want to treat this as a whole
  #; (where (qb_ref-entry ...) (refmap ((τ β_i) ...) β_e (qb_r ...) zero))
   ------------------------------------------------------------------ ;; B-Prod
   (B . ⊢b . (Prod ((τ β_i) ...) β_e)
      (〚〛-qb β_e (qb_b ...)) #|binders|#
      (big-∪̂ ((qb_r . ∖̂ . (〚〛-qb β_i (qb_b ...))) ...)) #|refs|# )]

  [(where (qb_b qb_r) (lookup-B B X))
   ---------------------------------- ;; B-Var
   (B . ⊢b . X qb_b qb_r)]

  ;; this is a deterministic version of the fixpoint implied by the paper
  [(where (qb_b qb_r) (smallest-bounds B X τ))
   ------------------------------------------- ;; B-Mu
   (B . ⊢b . (μ X τ) qb_b qb_r)]
  )

;; assuming the types are contractive, ⊥ shouldn't happen
(define-metafunction aa-proof
  approx : z→s τ -> bound
  [(approx ℱb τ) qb_b
                 (judgment-holds (ε . ⊢b . τ qb_b qb_r))]
  [(approx ℱr τ) qb_r
                 (judgment-holds (ε . ⊢b . τ qb_b qb_r))]
  [(approx ℱ τ) (∪̂ qb_b qb_r)
                (judgment-holds (ε . ⊢b . τ qb_b qb_r))]
  [(approx ℱx (Prod ((τ β_i) ...) β_e))
   (∖̂ (big-∪̂ ((approx ℱb τ) ...)) (〚〛-qb β_e ((approx ℱb τ) ...)))
   #;,(let ((bind-map `((approx ℱb τ) ...)))
      `(∖̂ (big-∪̂ (exposable-sub ,bind-map (τ ...) (β_i ... β_e)))
          (〚〛-qb β_e ,bind-map)))])

(define-metafunction aa-proof
  type-specific-opaque-info : z τ -> C
  [(type-specific-opaque-info z Atom) (∧ (size-bounded-by (ℱb z) one) (= (ℱr z) ∅))]
  [(type-specific-opaque-info z RefAtom) (∧ (size-bounded-by (ℱr z) one) (= (ℱb z) ∅))]
  [(type-specific-opaque-info z (Prod ((τ β_i) ...) β_e))
   (size-bounded-by (ℱx z) (approx ℱx (Prod ((τ β_i) ...) β_e)))]
  [(type-specific-opaque-info z τ) true])

;; Commented out because of bug --FM
(define-metafunction aa-proof
  opaque-info : z τ -> C
  [(opaque-info z τ)
   (big ∧ ((size-bounded-by (ℱb z) bound_b)
           (size-bounded-by (ℱr z) bound_r)
           #;,(match `τ
                [`Atom ];; here was just a ` before the ] --FM
                [`(Prod ((τ β_i) ...) β_e)]
                )))

   (judgment-holds (ε . ⊢b . τ bound_b bound_r))]
  )


#;(define-metafunction aa-proof
    names-mentioned-C : C -> (z ...)
    [(names-mentioned-C (∧ C_l C_r))
     ,(append `(names-mentioned-C C_l) `(names-mentioned-C C_r))]
    [(names-mentioned-C true) ()]
    [(names-mentioned-C (ss→C s_l s_r))
     ,(append `(names-mentioned-s s_l) `(names-mentioned-s s_r))]
    [(names-mentioned-C (val= z qlit)) ,(cons `z `(names-mentioned-qlit qlit))]
    [(names-mentioned-C (size-bounded-by s bound)) (names-mentioned-s s)])

#;(define-metafunction aa-proof
    names-mentioned-qlit : qlit -> (z ...)
    [(names-mentioned-qlit x) (x)]
    [(names-mentioned-qlit (einj0 qlit τ)) (names-mentioned-qlit qlit)]
    [(names-mentioned-qlit (einj1 τ qlit)) (names-mentioned-qlit qlit)]
    [(names-mentioned-qlit (eprod ((qlit β_i) ...) β_e))
     ,(append* `((names-mentioned-qlit qlit) ...))])

#;(define-metafunction aa-proof
    names-mentioned-s : s -> (z ...)
    [(names-mentioned-s (ss→s s_l s_r))
     ,(append `(names-mentioned-s s_l) `(names-mentioned-s s_r))]
    [(names-mentioned-s (¬ s)) (names-mentioned-s s)]
    [(names-mentioned-s (z→s z)) (z)]
    [(names-mentioned-s (ℱe ε)) ()]
    [(names-mentioned-s (ℱe (z τ Γ))) ,(cons `z `(names-mentioned-s (ℱe Γ)))])

(define-metafunction aa-proof
  sets-mentioned-C : C -> ((z→s z) ...)
  [(sets-mentioned-C (∧ C_l C_r))
   ,(append `(sets-mentioned-C C_l) `(sets-mentioned-C C_r))]
  [(sets-mentioned-C true) ()]
  [(sets-mentioned-C (ss→C s_l s_r))
   ,(append `(sets-mentioned-s s_l) `(sets-mentioned-s s_r))]
  [(sets-mentioned-C (val= z qlit)) ()]
  [(sets-mentioned-C (size-bounded-by s bound)) (sets-mentioned-s s)])

(define-metafunction aa-proof
  sets-mentioned-s : s -> ((z→s z) ...)
  [(sets-mentioned-s (ss→s s_l s_r))
   ,(append `(sets-mentioned-s s_l) `(sets-mentioned-s s_r))]
  [(sets-mentioned-s (¬ s)) (sets-mentioned-s s)]
  [(sets-mentioned-s (z→s z)) ((z→s z))]
  [(sets-mentioned-s (ℱe Γ)) ((ℱ (expand-fe-union Γ)))]
  [(sets-mentioned-s s) ()])

(define-metafunction aa-proof
  expand-fe-union : Γ -> s
  [(expand-fe-union ε) ∅]
  [(expand-fe-union (z τ Γ)) (∪ (ℱ z) (expand-fe-union Γ))])

(define-metafunction aa-proof
  bound-set-size-constraint : (z→s z) Γ -> C
  [(bound-set-size-constraint (z→s z) Γ) (∧ (opaque-info z (lookup Γ z))
                                            (∧ (size-bounded-by (z→s z) (approx z→s (lookup Γ z)))
                                               (type-specific-opaque-info z (lookup Γ z))))])

(define-metafunction aa-proof
  bound-set-sizes : obl -> obl
  [(bound-set-sizes (Γ H ⊩ P))
   (Γ (∧ H (big ∧
                ,(map
                  #;(λ (x) `(size-bounded-by s (bounds-of (lookup Γ ,x))))
                  (λ (x) (term (bound-set-size-constraint ,x Γ)))
                  #;(remove-duplicates (append `(names-mentioned-C H) `(names-mentioned-C P)))
                  (remove-duplicates (append `(sets-mentioned-C H) `(sets-mentioned-C P)))
                  ))) ⊩ P)])

(define-metafunction aa-proof
  eliminate-ℱ-ℱe : obl -> obl
  [(eliminate-ℱ-ℱe obl) (eliminate-ℱ (eliminate-ℱe obl))])

(define-metafunction aa-proof
  eliminate-ℱ : obl -> obl
  [(eliminate-ℱ (Γ H ⊩ P)) (Γ (eliminate-ℱ-C Γ H) ⊩ (eliminate-ℱ-C Γ P))])

(define-metafunction aa-proof
  eliminate-ℱ-C : Γ C -> C
  [(eliminate-ℱ-C Γ (∧ C_l C_r))
   (∧ (eliminate-ℱ-C Γ C_l) (eliminate-ℱ-C Γ C_r))]
  [(eliminate-ℱ-C Γ true) true]
  [(eliminate-ℱ-C Γ (ss→C s_l s_r))
   (ss→C (eliminate-ℱ-s Γ s_l) (eliminate-ℱ-s Γ s_r))]
  [(eliminate-ℱ-C (val= z qlit)) (val= z qlit)]
  [(eliminate-ℱ-C (size-bounded-by s bound))
   (size-bounded-by (eliminate-ℱ-s Γ s) bound)])

(define-metafunction aa-proof
  eliminate-ℱ-s : Γ s -> s
  [(eliminate-ℱ-s Γ (ss→s s_l s_r))
   (ss→s (eliminate-ℱ-s Γ s_l) (eliminate-ℱ-s Γ s_r))]
  [(eliminate-ℱ-s Γ (¬ s)) (¬ (eliminate-ℱ-s Γ s))]
  [(eliminate-ℱ-s Γ (ℱ z)) (∪ (ℱr z) (ℱb z))]
  [(eliminate-ℱ-s Γ (z→s z)) (z→s z)]
  [(eliminate-ℱ-s Γ ∅) ∅])

(define-metafunction aa-proof
  eliminate-ℱe : obl -> obl
  [(eliminate-ℱe (Γ H ⊩ P)) (Γ (eliminate-ℱe-C Γ H) ⊩ (eliminate-ℱe-C Γ P))])

(define-metafunction aa-proof
  eliminate-ℱe-C : Γ C -> C
  [(eliminate-ℱe-C Γ (∧ C_l C_r))
   (∧ (eliminate-ℱe-C Γ C_l) (eliminate-ℱe-C Γ C_r))]
  [(eliminate-ℱe-C Γ true) true]
  [(eliminate-ℱe-C Γ (ss→C s_l s_r))
   (ss→C (eliminate-ℱe-s Γ s_l) (eliminate-ℱe-s Γ s_r))]
  [(eliminate-ℱe-C (val= z qlit)) (val= z qlit)]
  [(eliminate-ℱe-C (size-bounded-by s bound))
   (size-bounded-by (eliminate-ℱe-s Γ s) bound)])

(define-metafunction aa-proof
  eliminate-ℱe-s : Γ s -> s
  [(eliminate-ℱe-s Γ (ss→s s_l s_r))
   (ss→s (eliminate-ℱe-s Γ s_l) (eliminate-ℱe-s Γ s_r))]
  [(eliminate-ℱe-s Γ (¬ s)) (¬ (eliminate-ℱe-s Γ s))]
  [(eliminate-ℱe-s Γ (ℱe z)) (ℱ (expand-fe-union Γ))]
  [(eliminate-ℱe-s Γ (z→s z)) (z→s z)]
  [(eliminate-ℱe-s Γ ∅) ∅])

(module+ test (test-results))
