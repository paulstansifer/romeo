#lang racket
(require redex/reduction-semantics rackunit)

(provide (all-defined-out))

(define-language aa
  [prog ((fD ...) e)]

  [fD (define-fn f ((x τ) ...) C τ e C)]
  [f variable-not-otherwise-mentioned]
  [x variable-not-otherwise-mentioned]

  [e (ecall f x ...)
     (efresh x e)
     (elet x C e e)
     (ecase x x e x e)
     (eopen x (x ...) e)
     (eifeq x x e e)
     qlit]

  [qlit x
        (ref x)
        (einj0 qlit τ)
        (einj1 τ qlit)
        (eprod ((qlit β) ...) β)]

  [τ Atom ;; = BAtom in the paper
     RefAtom ;; = RAtom in the paper
     (+ τ τ)
     (Prod ((τ β) ...) β)
     (μ X τ)
     X]
  [X variable-not-otherwise-mentioned]

  [(C P H) (∧ C C)
           (ss→C s s)
           true]
  [ss→C = ≠ dsj ⊆]

  [s ∅
     (ss→s s s)
     (z→s z)
     (ℱe Γ)]
  [ss→s ∪ ∩ ∖]
  [z→s ℱ ℱb ℱr ℱx]

  [subs ((z z) ...)]

  [Γ ε
     (z τ Γ)]

  [z x
     ·]

  [β ∅
     (⊎ β β) 
     (@ β β) ;; = ▹ in the paper
     ℓ]
  [ℓ natural]
)

(define-extended-language aa-machine aa
  [v a
     (inj0 v)
     (inj1 v)
     (prod v ...)]
  [a (atom at)]
  [at variable-not-otherwise-mentioned]

  [ρ ε
     (x v ρ)]

  [result v
          FAULT]

  [binder-map ((a ...) ...)]
  )

;; used by -exec and -type
(define fn-defs (make-parameter `()))

;; I prefer using backtick...
(define-syntax-rule (quasiquote x ...) (term x ...))


(define-metafunction aa-machine
  disjoint : any any -> any ; spelled '#' in the formalism
  [(disjoint (atom at) (atom at)) #f]
  [(disjoint (atom at_0) (atom at_1)) #t]
  [(disjoint (atom at_0) ((atom at_1) ...))
   ,(andmap (λ (a) `(disjoint (atom at_0) ,a))
            `((atom at_1) ...))]
  [(disjoint ((atom at_0) ...) any)
   ,(andmap (λ (a) `(disjoint ,a any))
            `((atom at_0) ...))]
  [(disjoint any ε) #t]
  )

(define (plain-disjoint lst0 lst1)
  (= (length lst0) (length (remove* lst1 lst0))))

(define-metafunction aa-machine
  not-disjoint : any any -> any
  [(not-disjoint any_a any_b) ,(not `(disjoint any_a any_b))])

(module+
 test
 (test-equal `(disjoint (atom a1) ε) #t)
 (test-equal `(disjoint (atom a1) (atom a2)) #t)
 (test-equal `(disjoint (atom a1) (atom a1)) #f)
 (test-equal `(disjoint (atom a1) ((atom a1) (atom a2))) #f)
 (test-equal `(disjoint (atom a1) ((atom a2) (atom a2))) #t))

(define-metafunction aa-machine
  type-subst : τ X τ -> τ
  [(type-subst Atom X τ_s) Atom]
  [(type-subst (+ τ_0 τ_1) X τ_s)  (+ (type-subst τ_0 X τ_s)
                                      (type-subst τ_1 X τ_s))]
  [(type-subst (Prod ((τ_child β_child) ...) β_e) X τ_s)
   (Prod (((type-subst τ_child X τ_s) β_child) ...) β_e)]
  [(type-subst (μ X τ_child) X τ_s) τ_s]
  [(type-subst (μ X_0 τ_child) X_1 τ_s) (μ X_0 (type-subst τ_child X_1 τ_s))]
  [(type-subst X X τ_s) τ_s]
  [(type-subst X_0 X_1 τ_s) X_0])

(module+
 test
 (test-equal `(type-subst (Prod ((a1 ∅) (a2 1) ((+ a2 a3) (⊎ 0 1))) ∅)
                          a2 Atom)
             `(Prod ((a1 ∅) (Atom 1) ((+ Atom a3) (⊎ 0 1))) ∅)))

(define-metafunction aa-machine
  type-unfold : (μ X τ) -> τ
  [(type-unfold (μ X τ)) (type-subst τ X (μ X τ))])

(module+
 test
 (test-equal
  ;; Sort of like LetClauses (but without values)
  `(type-unfold (μ X (Prod (((+ X (Prod () ∅)) ∅) (Atom ∅)) (⊎ 0 1))))
  `(Prod (((+ (μ X (Prod (((+ X (Prod () ∅)) ∅) (Atom ∅)) (⊎ 0 1)))
              (Prod () ∅)) ∅) (Atom ∅)) (⊎ 0 1))))

(define-metafunction aa-machine
  β->lst : β -> (ℓ ...)
  [(β->lst ∅) ()]
  [(β->lst ℓ) (ℓ)]
  [(β->lst (⊎ β_0 β_1)) ,(append `(β->lst β_0) `(β->lst β_1))]
  [(β->lst (@ β_0 β_1)) ,(append `(β->lst β_0) `(β->lst β_1))])

(module+
 test
 (test-equal `(β->lst (⊎ 0 (@ 1 ∅)))
             `(0 1)))

(define-metafunction aa-machine
  β-∈ : ℓ β -> any
  [(β-∈ ℓ ∅) #f]
  [(β-∈ ℓ ℓ) #t]
  [(β-∈ ℓ_0 ℓ_1) #f]
  [(β-∈ ℓ (⊎ β_0 β_1)) ,(or `(β-∈ ℓ β_0) `(β-∈ ℓ β_1))]
  [(β-∈ ℓ (@ β_0 β_1)) ,(or `(β-∈ ℓ β_0) `(β-∈ ℓ β_1))]
  )

(define-metafunction aa-machine
  〚〛 : β ((any ...) ...) -> (any ...)
  [(〚〛 ∅ ((any ...) ...)) ()]
  [(〚〛 ℓ ((any ...) ...)) ,(list-ref `((any ...) ...) `ℓ)]
  [(〚〛 (⊎ β_0 β_1) ((any ...) ...))
   ,(append `(〚〛 β_0 ((any ...) ...))
            `(〚〛 β_1 ((any ...) ...)))]
  [(〚〛 (@ β_0 β_1) ((any ...) ...))
   ,(append `(〚〛 β_0 ((any ...) ...))
            `(〚〛 β_1 ((any ...) ...)))])

(define-metafunction aa-machine
  〚〛-subs : β (subs ...) -> subs
  [(〚〛-subs ∅ (subs ...)) ()]
  [(〚〛-subs ℓ (subs ...)) ,(list-ref `(subs ...) `ℓ)]
  [(〚〛-subs (⊎ β_0 β_1) (subs ...))
   ,(append `subs_left `subs_right)
   (where subs_left (〚〛-subs β_0 (subs ...)))
   (where subs_right (〚〛-subs β_1 (subs ...)))
   (side-condition (plain-disjoint (map car `subs_left) (map car `subs_right)))]
  [(〚〛-subs (@ β_0 β_1) (subs ...))
   ,(append `subs_left `subs_right)
   (where subs_left (〚〛-subs β_0 (subs ...)))
   (where subs_right ,(remove* `subs_left `(〚〛-subs β_1 (subs ...))
                               (λ (pair0 pair1) (eq? (car pair0) (car pair1)))))]
  )

(module+
 test
 (test-equal `(〚〛-subs 0
               (((x x0) (y y0))
                ((y y1) (z z1))
                ((x x2) (y y2) (z z2) (xx xx2))))
             `((x x0) (y y0)))
 
 (test-equal `(〚〛-subs (@ 0 1)
               (((x x0) (y y0))
                ((y y1) (z z1))
                ((x x2) (y y2) (z z2) (xx xx2))))
             `((x x0) (y y0) (z z1))))

(define-metafunction aa-machine
  〚〛-syn : β (s ...) -> s
  [(〚〛-syn ∅ (s ...)) ∅]
  [(〚〛-syn ℓ (s ...)) ,(list-ref `(s ...) `ℓ)]
  [(〚〛-syn (⊎ β_0 β_1) (s ...))
   (∪ (〚〛-syn β_0 (s ...))
      (〚〛-syn β_1 (s ...)))]
  [(〚〛-syn (@ β_0 β_1) (s ...))
   (∪ (〚〛-syn β_0 (s ...))
      (〚〛-syn β_1 (s ...)))])

(define-metafunction aa-machine
  apply-subs : subs v -> v
  [(apply-subs subs (prod v ...))
   (prod (apply-subs subs v) ...)]
  [(apply-subs subs (inj0 v))
   (inj0 (apply-subs subs v))]
  [(apply-subs subs (inj1 v))
   (inj1 (apply-subs subs v))]
  [(apply-subs subs (atom at))
   (atom ,(cadr (or (assoc `at `subs)
                    `(at at))))])

(define-metafunction aa-machine
  apply-subs-r : subs v τ -> v
  [(apply-subs-r subs (prod v ...) (Prod ((τ β) ...) β_ex))
   (prod (apply-subs-r subs v τ) ...)]
  [(apply-subs-r subs (inj0 v) (+ τ_l τ_r)) 
   (inj0 (apply-subs-r subs v τ_l))]
  [(apply-subs-r subs (inj1 v) (+ τ_l τ_r)) 
   (inj1 (apply-subs-r subs v τ_r))]
  [(apply-subs-r subs (atom at) RefAtom)
   (atom ,(cadr (or (assoc `at `subs)
                    `(at at))))]
  [(apply-subs-r subs (atom at) Atom) (atom at)])

(define-metafunction aa-machine
  apply-subs-b : subs v τ -> v
  [(apply-subs-b subs (prod v ...) (Prod ((τ β) ...) β_ex))
   (prod (apply-subs-b subs v τ) ...)]
  [(apply-subs-b subs (inj0 v) (+ τ_l τ_r)) 
   (inj0 (apply-subs-b subs v τ_l))]
  [(apply-subs-b subs (inj1 v) (+ τ_l τ_r)) 
   (inj1 (apply-subs-b subs v τ_r))]
  [(apply-subs-b subs (atom at) Atom)
   (atom ,(cadr (or (assoc `at `subs)
                    `(at at))))]
  [(apply-subs-b subs (atom at) RefAtom) (atom at)])

(define-metafunction aa-machine
  refmap : ((τ β) ...) β (any ...) any -> (any ...)
  [(refmap ((τ β_i) ...) β_e (any_ref ...) any_cancel)
  ,(map (λ (τ ref idx)
           (if (and (eq? τ `Atom)
                    (foldr (λ (x y) (or x y)) #f
                           `((,idx . β-∈ . β_i) ... (,idx . β-∈ . β_e))))
               `any_cancel ;; actually, it's a binder
               ref))
    `(τ ...) `(any_ref ...) (idxes `(any_ref ...)))])


(define-metafunction aa-machine
  free-binders : τ v -> (a ...)
  [(free-binders Atom a) (a)]
  [(free-binders RefAtom a) ()]
  [(free-binders (+ τ_0 τ_1) (inj0 v)) (free-binders τ_0 v)]
  [(free-binders (+ τ_0 τ_1) (inj1 v)) (free-binders τ_1 v)]
  [(free-binders (μ X τ) v)  (free-binders (type-unfold (μ X τ)) v)]
  [(free-binders (Prod ((τ_child β_child) ..._0 ) β_e)
                 (prod v_child ..._0))
   (〚〛 β_e ((free-binders τ_child v_child) ...))])

(module+
 test
 (test-equal `(free-binders Atom (atom a1))
             `((atom a1)))
 (test-equal
  (term
   (free-binders
    (Prod ((Atom ∅) ((Prod ((Atom ∅) (Atom ∅)) 1) ∅) (Atom ∅)) (⊎ 1 2))
    (prod (atom a1) (prod (atom a2) (atom a3)) (atom a4))))
  `((atom a3) (atom a4)))

 (test-equal
  `(free-binders
    (μ X (Prod (((+ X (Prod () ∅)) ∅) (Atom ∅)) (⊎ 0 1)))
    (prod (inj0 (prod (inj0 (prod (inj1 (prod)) (atom a1)))
                      (atom a2)))
          (atom a3)))
  `((atom a1) (atom a2) (atom a3)))

 ;; TODO: should we really treat (+ Atom Atom) the way we do; as a refernce and a binder?

 (test-equal
  `(refmap ((Atom 1) (Atom ∅) (Atom ∅) ((+ Atom Atom) 1) ((+ Atom Atom) ∅)) 2
           (0 1 2 3 4) 999)
  `(0 999 999 3 4)))

(define (trc s x)
  (printf "[~s] ~s~%" s x)
  x)

;; idxes : [Any] -> [Nat]
;; Produces (0 1 2 3 ⋯), of the same length as the input.
(define (idxes lst) (build-list (length lst) values))

(define-metafunction aa-machine
  free-references : τ v -> (a ...)
  [(free-references Atom a) ()]
  [(free-references RefAtom a) (a)]
  [(free-references (+ τ_0 τ_1) (inj0 v)) (free-references τ_0 v)]
  [(free-references (+ τ_0 τ_1) (inj1 v)) (free-references τ_1 v)]
  [(free-references (μ X τ) v)  (free-references (type-unfold (μ X τ)) v)]

  [(free-references (Prod ((τ_child β_child) ..._0 ) β_e)
               (prod v_child ..._0))
   ,(apply append (term ((remove-atoms (free-references τ_child v_child) (〚〛 β_child ((free-binders τ_child v_child) ...))) ...)))
   #;,(append-map
     (λ (τ β v idx)
        (if (and (equal? τ `Atom) (member idx `(ℓ_imported ...)))
            `() ;; binders aren't references
            (remove* `(〚〛 ,β binder-map) ;; these get bound
                     `(free-references ,τ ,v))))

     `(τ_child ...) `(β_child ...) `(v_child ...)
     (idxes `(v_child ...)))

   (where binder-map ((free-binders τ_child v_child) ...))
   (where (ℓ_imported ...)
          ,(append* `((β->lst β_child) ... (β->lst β_e))))]
  )

(define-metafunction aa-machine
  remove-atoms : (a ...) (a ...) -> (a ...)
  [(remove-atoms (a_l ...) (a_r ...))
   ,(remove* (term (a_r ...)) (term (a_l ...)))])

(module+
 test
 (test-equal `(free-references (Prod ((Atom ∅) (RefAtom ∅) (RefAtom 0)) ∅)
                               (prod (atom a1) (atom a2) (atom a1)))
             `((atom a2)))

 (test-equal
  `(free-references
    (Prod (((Prod ((Atom ∅) ((Prod ((Atom ∅) (RefAtom ∅)) ∅) ∅)) 0) 1)
           ((Prod ((Atom ∅) ((Prod ((RefAtom ∅) (RefAtom ∅)) ∅) ∅)) 0) 0)) ∅)
    (prod (prod (atom a0) (prod (atom a1) (atom a2)))
          (prod (atom a1) (prod (atom a3) (atom a0)))))
  `((atom a2) (atom a3))))


(define-metafunction aa-machine
  free-atoms : τ result -> (a ...)
  [(free-atoms τ v) ,(append `(free-binders τ v) `(free-references τ v))]
  [(free-atoms τ FAULT) ()])
;;TODO test free-atoms, also!

;; These functions (and the whole definition of exposable-atoms) were awful.
;; Thanks Fabian for updating to the new semantics!
#;(define-metafunction aa-machine
  exposable-sub : (any ...) (τ ...) (β ...) -> (any ...)
  [(exposable-sub (any ...) (τ ...) (β ...))
   (exposable-sub-rec ((any ℓ τ) ...) ,(append* `((β->lst β) ...)))
   (where (ℓ ...) ,(idxes `(any ...)))])

#;(define-metafunction aa-machine
  exposable-sub-rec : ((any ℓ τ) ...) (ℓ_used ...) -> (any ...)
  [(exposable-sub-rec () (ℓ_used ...)) ()]
  [(exposable-sub-rec ((any ℓ Atom) (any_cdr ℓ_cdr τ_cdr) ...) (ℓ_used ...))
   ,(cons `any `(exposable-sub-rec ((any_cdr ℓ_cdr τ_cdr) ...) (ℓ_used ...)))
   (side-condition (member `ℓ `(ℓ_used ...)))]
  [(exposable-sub-rec ((any ℓ Atom) (any_cdr ℓ_cdr τ_cdr) ...) (ℓ_used ...))
   (exposable-sub-rec ((any_cdr ℓ_cdr τ_cdr) ...) (ℓ_used ...))]
  [(exposable-sub-rec ((any ℓ τ) (any_cdr ℓ_cdr τ_cdr) ...) (ℓ_used ...))
   ,(cons `any `(exposable-sub-rec ((any_cdr ℓ_cdr τ_cdr) ...) (ℓ_used ...)))])

(define-metafunction aa-machine
  exposable-atoms : (Prod ((τ β_imp) ...) β_exp) (prod v ...)
                    -> (a ...)
  [(exposable-atoms (Prod ((τ β_imp) ...) β_exp) (prod v ...))
   (remove-atoms ,(apply append (term ((free-binders τ v) ...))) (free-binders (Prod ((τ β_imp) ...) β_exp) (prod v ...)))
   #;,(remove* `(〚〛 β_exp binder-map)
             (append* `(exposable-sub binder-map (τ ...) (β_imp ... β_exp) )))
   (where binder-map ((free-binders τ v) ...))])


(define (nmlz ats)
  (remove-duplicates (sort ats (λ (x y) (string<? (symbol->string x)
                                                  (symbol->string y)))
                           #:key cadr) #:key cadr))

(module+
 test

 (test-equal (nmlz `((atom a3) (atom a1) (atom a3) (atom a2)))
             `((atom a1) (atom a2) (atom a3)))

 (define (comb->type c)
   (define (kid->kid-type kid)
     (match kid
            [`(,kc ↓ ,βi)
             `(,(comb->type kc) ,βi)]
            [kc
             `(,(comb->type kc) ∅)]))
   (match c
          [`(p ,kids ... ⇑ ,βe)
           `(Prod ,(map kid->kid-type kids) ,βe)]
          [`(p ,kids ...)
           `(Prod ,(map kid->kid-type kids) ∅)]
          [`(i0 ,kid) `(+ ,(comb->type kid) Atom)]
          [`(ii ,kid) `(+ Atom ,(comb->type kid))]
          [a `Atom]))

 (define (comb->val c)
   (define (kid->kid-val kid)
     (match kid
            [`(,kc ↓ ,βi) (comb->val kc)]
            [kc (comb->val kc)]))
   (match c
          [`(p ,kids ... ⇑ ,βe)
           `(prod ,@(map kid->kid-val kids))]
          [`(p ,kids ...)
           `(prod ,@(map kid->kid-val kids))]
          [`(i0 ,kid) `(inj0 ,(comb->val kid))]
          [`(ii ,kid) `(inj1 ,(comb->val kid))]
          [a `(atom ,(string->symbol
                      (string-append "a_" (symbol->string a))))]))

 (define (comb->both c)
   `(,(comb->type c) ,(comb->val c)))

 (test-equal
  (nmlz `(exposable-atoms ,@(comb->both `(p a (a ↓ 0) b))))
  (map comb->val `(a b)))

 (test-equal
  (nmlz `(exposable-atoms
          ,@(comb->both
             `(p (p a b c ⇑ (@ 0 (@ 1 2)))
                 ( (p (p d ⇑ 0) dd (d ↓ (@ 0 1)) a e) ↓ 0)
                 (p f ⇑ 0) ; re-exported
                 (p g ⇑ 0) ; abandoned
                 ⇑ 2))
          ))
  (map comb->val `(a b c g)))

)





(define (only x)
  (match x
         [`(,item) item]
         [`() "No results"]
         [xs (format "Too many results: ~s" xs)]))


(define (only-or-false x)
  (match x
         [`(,item) item]
         [_ #f]))


(module+ test (test-results))
