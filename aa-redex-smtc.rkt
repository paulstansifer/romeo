#lang racket

(require "aa-redex-core.rkt")
(require "aa-redex-type.rkt")
(require "aa-redex-logi.rkt")
(require "aa-redex-util.rkt")
(require "aa-redex-proo.rkt")
(require "aa-redex-util-proo.rkt")

(require rackunit)
(require redex/reduction-semantics)
(provide (all-defined-out))

;(provide check-obls)


#;(define Z3-COMMAND "z3 /in /smt2")
#;(define Z3-DEFS
  (list "(define-sort Set (T) (Array T Bool))"
        "(declare-sort Elem)"
        "(declare-const emptyset (Set Elem))"
        "(assert (forall ((e Elem)) (not (select emptyset e))))"
        "(define-fun disjoint ((s1 (Set Elem)) (s2 (Set Elem))) Bool
                (= (intersect s1 s2) emptyset))"
        "(define-fun sizeone ((s (Set Elem))) Bool
                (exists ((e1 Elem)) (forall ((e2 Elem)) (=> (select s e2) (= e1 e2)))))"))

(define smt-setnum 0)
(define smt-set-maxnum 0)
(define smt-curbindings empty)

(define (smt-reset-names)
  (set! smt-setnum 0)
  (set! smt-set-maxnum 0)
  (set! smt-curbindings empty))

(define (smt-reset-bindings)
  (set! smt-setnum 0)
  (set! smt-curbindings empty))

(define (get-smt-sets any)
  (build-list smt-set-maxnum (lambda (n) (format "set~a" (+ n 1)))))


;; Quoted-z->s-expr -> String
(define (smt-get-name quoted-set)
  (if (ormap (lambda (b) (equal? (first b) quoted-set)) smt-curbindings)
      (second 
       (first 
        (filter (lambda (b) (equal? (first b) quoted-set)) 
                smt-curbindings)))
      (begin
        (set! smt-setnum (+ smt-setnum 1))
        (set! smt-set-maxnum (max smt-set-maxnum smt-setnum))
        (set! smt-curbindings 
              (cons (list quoted-set (format "set~a" smt-setnum))
                    smt-curbindings))
        (format "set~a" smt-setnum))))


(define-extended-language aa-smt aa-proof
  [smt-set smt-empty 
           (string (z→s z))
           (smt-union smt-set smt-set)
           (smt-intersection smt-set smt-set)
           (smt-difference smt-set smt-set)
           (smt-complement smt-set)]
  [smt-line smt-constraint
            (smt-not smt-constraint)]
  [smt-constraint smt-true
                  (smt-seteq smt-set smt-set)
                  (smt-setneq smt-set smt-set)
                  (smt-setdisjoint smt-set smt-set)
                  (smt-subset smt-set smt-set)
                  (smt-size-one smt-set)
                  (smt-size-zero-or-one smt-set)]
  [smt-pre ((smt-line pre C) ...)]
  [smt-post ((smt-line pos C) ...)]
  
  ;;from sugar
  [var (x any)]
  [xenv (env poss pres)]
  [cnd (annot (C any))
       (pfresh var)
       (popen var (var ...))]
  [pos cnd      
       (fcpre any any (C any))
       (ignore any C)]
  [poss (pos ...)]
  [pre cnd
       (letsub var)
       (ifthen var var)
       (ifelse var var)
       (fcpost any any (C any))
       (fcenv any any)
       (caseleft var var)
       (caseright var var)
       (qcons any)
       setsizes]
  [pres pre
        (∧ pres pres)]
  [env (envx ...)]
  [envx (x any any (var ...))])

(define-metafunction aa-smt
  obls->smt : (obl ...) (xenv ...) -> ((string ...) ((smt-pre smt-post env) ...))
  [(obls->smt (obl ..._n) (xenv ..._n))
   ,(begin 
      (let ([lines (term ((obl->smt (bound-set-sizes (eliminate-ℱ-ℱe (obl-rem-val=s obl))) xenv) ...))])
             (term (,(get-smt-sets lines) ,lines))))])

(define-metafunction aa-smt
  non-trivial? : obl -> #t or #f
  [(non-trivial? (Γ H ⊩ true)) #f]
  [(non-trivial? obl) #t])

(define-metafunction aa-smt
  obl->smt : obl xenv -> (smt-pre smt-post env)
  [(obl->smt (Γ H ⊩ P) (env poss pres))
   ,(begin 
      (smt-reset-bindings)
      (term ((C->smt Γ (simplify-C Γ H) ,(gensym) (∧ pres setsizes))
             (((C->smt/post Γ (simplify-C Γ C) ,(gensym)) pos (simplify-C Γ C)) ...)
             env)))
   (where ((C pos) ...) ,(filter (lambda (p) (not (equal? 'ignore (first (second p))))) 
                                (map list (term (simplify-C-big ε P)) (term poss))))])

(define-metafunction aa-smt
  smt->not : (smt-line ...) -> (smt-line ...)
  [(smt->not (smt-constraint ...)) ((smt-not smt-constraint) ...)])

(define-metafunction aa-smt
  C->smt : Γ C any pres -> smt-pre
  [(C->smt Γ (∧ C_1 C_2) any (∧ pres_1 pres_2)) 
   ((smt-line_1 any_1 C_w1) ... (smt-line_2 any_2 C_w2) ...)
   (where ((smt-line_1 any_1 C_w1) ...) (C->smt Γ C_1 any pres_1))
   (where ((smt-line_2 any_2 C_w2) ...) (C->smt Γ C_2 any pres_2))
   #;(flatten-constraints ((C->smt Γ C_1 any) (C->smt Γ C_2 any)))]
  [(C->smt Γ (∧ C_1 C_2) any pre) 
   ((smt-line_1 any_1 C_w1) ... (smt-line_2 any_2 C_w2) ...)
   (where ((smt-line_1 any_1 C_w1) ...) (C->smt Γ C_1 any pre))
   (where ((smt-line_2 any_2 C_w2) ...) (C->smt Γ C_2 any pre))
   #;(flatten-constraints ((C->smt Γ C_1 any) (C->smt Γ C_2 any)))]
  [(C->smt Γ true any pre) ((smt-true pre true))]
  [(C->smt Γ (ss→C s_1 s_2) any pre) (((C->smt-ss Γ ss→C s_1 s_2 any) pre (ss→C s_1 s_2)))]
  [(C->smt Γ (val= z qlit) any) 
   ,(error "What to do here? Case: val= z qlit")]
  [(C->smt Γ (size-bounded-by s bound) any setsizes) 
   ((smt-constraint setsizes (size-bounded-by s bound)) ...)
   (where (smt-constraint ...) (C->smt-size-bound Γ s bound any))])

(define-metafunction aa-smt
  C->smt/post : Γ C any -> smt-line
  [(C->smt/post Γ true any) smt-true]
  [(C->smt/post Γ (ss→C s_1 s_2) any) (C->smt-ss Γ ss→C s_1 s_2 any)])

(define-metafunction aa-smt
  C->smt-size-bound : Γ s bound any -> (smt-constraint ...)
  [(C->smt-size-bound Γ s zero any) ((C->smt-ss Γ = s ∅ any))]
  [(C->smt-size-bound Γ s zero+ any) ()]
  [(C->smt-size-bound Γ s one+ any) ((C->smt-ss Γ ≠ s ∅ any))]
  [(C->smt-size-bound Γ s one any) 
   ((smt-size-one (s->smt Γ s any)))]
  [(C->smt-size-bound Γ s zero-or-one any) 
   ((smt-size-zero-or-one (s->smt Γ s any)))])


(define-metafunction aa-smt
  C->smt-ss : Γ ss→C s s any -> smt-constraint
  [(C->smt-ss Γ = s_1 s_2 any) (smt-seteq (s->smt Γ s_1 any) (s->smt Γ s_2 any))]
  [(C->smt-ss Γ ≠ s_1 s_2 any) (smt-setneq (s->smt Γ s_1 any) (s->smt Γ s_2 any))]
  [(C->smt-ss Γ dsj s_1 s_2 any) (smt-setdisjoint (s->smt Γ s_1 any) (s->smt Γ s_2 any))]
  [(C->smt-ss Γ ⊆ s_1 s_2 any) (smt-subset (s->smt Γ s_1 any) (s->smt Γ s_2 any))])

(define-metafunction aa-smt
  s->smt : Γ s any -> smt-set
  [(s->smt Γ ∅ any) smt-empty]
  [(s->smt Γ (ss→s s_1 s_2) any) (s->smt-ss Γ ss→s s_1 s_2 any)]
  [(s->smt Γ (¬ s) any) (smt-complement (s->smt Γ s any))]
  [(s->smt Γ (z→s z) any) (s->smt-zs Γ z→s z any)]
  [(s->smt Γ (ℱe Γ_1) any) (s->smt Γ (expand-fe-union Γ_1) any)])

(define-metafunction aa-smt
  s->smt-zs : Γ z→s z any -> smt-set
  [(s->smt-zs Γ z→s z any) (,(smt-get-name (term (z→s z))) (z→s z))])

(define-metafunction aa-smt
  s->smt-ss : Γ ss→s s s any -> smt-set
  [(s->smt-ss Γ ∪ s_1 s_2 any)
   (smt-union (s->smt Γ s_1 any) (s->smt Γ s_2 any))]
  [(s->smt-ss Γ ∩ s_1 s_2 any)
   (smt-intersection (s->smt Γ s_1 any) (s->smt Γ s_2 any))]
  [(s->smt-ss Γ ∖ s_1 s_2 any)
   (smt-difference (s->smt Γ s_1 any) (s->smt Γ s_2 any))])

(define-metafunction aa-smt
  flatten-constraints : ((smt-constraint ...) ...) -> (smt-constraint ...)
  [(flatten-constraints ((any ...) ...)) (any ... ...)])

(define-metafunction aa-smt
  flatten-lines : ((smt-line ...) ...) -> (smt-line ...)
  [(flatten-lines ((smt-line ...) ...)) (smt-line ... ...)])



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;  ;;;;;;;;  ;;;;;;;;        ;;;;;;;;  ;;;;;;;;  ;;    ;;  ;;;;;;;;
;     ;;     ;;    ;;           ;;     ;;         ;;  ;;      ;;
;     ;;     ;;    ;;           ;;     ;;          ;;;;       ;;
;     ;;     ;;    ;;           ;;     ;;;;;        ;;        ;;
;     ;;     ;;    ;;           ;;     ;;          ;;;;       ;;
;     ;;     ;;    ;;           ;;     ;;         ;;  ;;      ;;
;     ;;     ;;;;;;;;           ;;     ;;;;;;;;  ;;    ;;     ;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction aa-smt
  smt->text : (smt-line ...) -> (string ...)
  [(smt->text (smt-line ...))
   ((smt->text-line smt-line) ...)])

(define-metafunction aa-smt
  smt->text-line : smt-line -> string
  [(smt->text-line smt-constraint)
   ,(format "(assert ~a)" (term (smt->text-c smt-constraint)))]
  [(smt->text-line (smt-not smt-constraint))
   ,(format "(assert (not ~a))" (term (smt->text-c smt-constraint)))])

(define-metafunction aa-smt
  smt->text-c : smt-constraint -> string
  [(smt->text-c smt-true) "true"]
  [(smt->text-c (smt-seteq smt-set_1 smt-set_2)) 
   ,(format "(= ~a ~a)" (term (smt->text-s smt-set_1)) 
            (term (smt->text-s smt-set_2)))]
  [(smt->text-c (smt-setneq smt-set_1 smt-set_2))
   ,(format "(not (= ~a ~a))" (term (smt->text-s smt-set_1)) 
            (term (smt->text-s smt-set_2)))]
  [(smt->text-c (smt-setdisjoint smt-set_1 smt-set_2))
   ,(format "(disjoint ~a ~a)" (term (smt->text-s smt-set_1)) 
            (term (smt->text-s smt-set_2)))]
  [(smt->text-c (smt-subset smt-set_1 smt-set_2))
   ,(format "(subset ~a ~a)" (term (smt->text-s smt-set_1)) 
            (term (smt->text-s smt-set_2)))]
  [(smt->text-c (smt-size-one smt-set))
   ,(format "(sizeone ~a)" (term (smt->text-s smt-set)))]
  [(smt->text-c (smt-size-zero-or-one smt-set))
   ,(format "(or (sizeone ~a) (= ~a emptyset))" 
            (term (smt->text-s smt-set))
            (term (smt->text-s smt-set)))])

(define-metafunction aa-smt
  smt->text-s : smt-set -> string
  [(smt->text-s smt-empty) "emptyset"]
  [(smt->text-s (string (z→s z))) string]
  [(smt->text-s (smt-union smt-set_1 smt-set_2))
   ,(format "(union ~a ~a)" (term (smt->text-s smt-set_1)) 
            (term (smt->text-s smt-set_2)))]
  [(smt->text-s (smt-intersection smt-set_1 smt-set_2))
   ,(format "(intersect ~a ~a)" (term (smt->text-s smt-set_1)) 
            (term (smt->text-s smt-set_2)))]
  [(smt->text-s (smt-difference smt-set_1 smt-set_2))
   ,(format "(difference ~a ~a)" (term (smt->text-s smt-set_1)) 
            (term (smt->text-s smt-set_2)))]
  [(smt->text-s (smt-complement smt-set))
   ,(format "(complement ~a)" (term (smt->text-s smt-set)))])



(define (process-model names model)
  (let* ([m (term (model->sets ,model))])
    (list (map (lambda (en) (string-replace (symbol->string en) "Elem!val!" "e")) (first m))
          (map (lambda (s) (list (second (assoc (first s) (cons (list "emptyset" (term ∅)) names)))
                                 (first s)
                                 (map (lambda (en) (string-replace (symbol->string en) "Elem!val!" "e")) (second s))))
               (second m)))))

(define-language smt-model
  [m (model constdef ... 
            constforall
            def ...)]
  [constdef (declare-fun Evar () Elem)]
  [Evar (variable-prefix Elem!val!)]
  [kvar (variable-prefix k!)]
  [svar emptyset (variable-prefix set)]
  [constforall any]
  [def setdef elemdef kdef]
  [setdef (define-fun svar () (Array Elem Bool) (any as-array kvar))]
  [elemdef (define-fun (variable-prefix e) () Elem Evar)]
  [kdef (define-fun kvar ((x!1 Elem)) Bool fundef)]
  [fundef true
          false
          (ite cond fundef fundef)]
  [cond (= x!1 Evar)])

(define-metafunction smt-model
  model->sets : m -> ((Evar ...) ((string (Evar ...)) ...))
  [(model->sets (model (declare-fun Evar () Elem) ... constforall def ...))
   ((Evar ...) (defs->sets (Evar ...) (sortdefs (def ...))))])
                                 
(define-metafunction smt-model
  sortdefs : (def ...) -> ((setdef ...) (kdef ...))
  [(sortdefs ()) (() ())]
  [(sortdefs (setdef def_r ...)) 
   ((setdef setdef_r ...) (kdef ...))
   (where ((setdef_r ...) (kdef ...)) (sortdefs (def_r ...)))]
  [(sortdefs (elemdef def_r ...)) (sortdefs (def_r ...))]
  [(sortdefs (kdef def_r ...))
   ((setdef ...) (kdef kdef_r ...))
   (where ((setdef ...) (kdef_r ...)) (sortdefs (def_r ...)))])

(define-metafunction smt-model
  defs->sets : (Evar ...) ((setdef ...) (kdef ...)) -> ((string (Evar ...)) ...)
  [(defs->sets (Evar ...) (((define-fun svar () (Array Elem Bool) (any as-array kvar)) ...) (kdef ...)))
   ((string (vars-in-set (Evar ...) kvar (kdef ...))) ...)
   (where (string ...) ,(map symbol->string (term (svar ...))))])

(define-metafunction smt-model
  vars-in-set : (Evar ...) kvar (kdef ...) -> (Evar ...)
  [(vars-in-set (Evar ...) kvar (kdef_l ... (define-fun kvar ((x!1 Elem)) Bool fundef) kdef_r ...))
   ,(filter (lambda (ev) (term (var-in-set? ,ev fundef))) (term (Evar ...)))])

(define-metafunction smt-model
  var-in-set? : Evar fundef -> #t or #f
  [(var-in-set? Evar true) #t]
  [(var-in-set? Evar false) #f]
  [(var-in-set? Evar (ite (= x!1 Evar) fundef_t fundef_e))
   (var-in-set? Evar fundef_t)]
  [(var-in-set? Evar (ite (= x!1 Evar_other) fundef_t fundef_e))
   (var-in-set? Evar fundef_e)])

(define-metafunction aa-smt
  set-names : (smt-line ...) -> ((string (z→s z)) ...)
  [(set-names (smt-line ...)) 
   ,(remove-duplicates (term ((string (z→s z)) ... ...)))
   (where (((string (z→s z)) ...) ...) ((set-names-line smt-line) ...))])

(define-metafunction aa-smt
  set-names-line : smt-line -> ((string (z→s z)) ...)
  [(set-names-line smt-constraint) (set-names-C smt-constraint)])

(define-metafunction aa-smt
  set-names-C : smt-constraint -> ((string (z→s z)) ...)
  [(set-names-C smt-true) ()]
  [(set-names-C (smt-seteq smt-set_l smt-set_r)) 
   (any_l ... any_r ...)
   (where (any_l ...) (set-names-set smt-set_l))
   (where (any_r ...) (set-names-set smt-set_r))]
  [(set-names-C (smt-setneq smt-set_l smt-set_r)) 
   (any_l ... any_r ...)
   (where (any_l ...) (set-names-set smt-set_l))
   (where (any_r ...) (set-names-set smt-set_r))]
  [(set-names-C (smt-setdisjoint smt-set_l smt-set_r)) 
   (any_l ... any_r ...)
   (where (any_l ...) (set-names-set smt-set_l))
   (where (any_r ...) (set-names-set smt-set_r))]
  [(set-names-C (smt-subset smt-set_l smt-set_r)) 
   (any_l ... any_r ...)
   (where (any_l ...) (set-names-set smt-set_l))
   (where (any_r ...) (set-names-set smt-set_r))]
  [(set-names-C (smt-size-one smt-set)) 
   (set-names-set smt-set)]
  [(set-names-C (smt-size-zero-or-one smt-set)) 
   (set-names-set smt-set)])

(define-metafunction aa-smt
  set-names-set : smt-set -> ((string (z→s z)) ...)
  [(set-names-set smt-empty) ()]
  [(set-names-set (string (z→s z))) ((string (z→s z)))]
  [(set-names-set (smt-union smt-set_l smt-set_r))
   (any_l ... any_r ...)
   (where (any_l ...) (set-names-set smt-set_l))
   (where (any_r ...) (set-names-set smt-set_r))]
  [(set-names-set (smt-intersection smt-set_l smt-set_r))
   (any_l ... any_r ...)
   (where (any_l ...) (set-names-set smt-set_l))
   (where (any_r ...) (set-names-set smt-set_r))]
  [(set-names-set (smt-difference smt-set_l smt-set_r))
   (any_l ... any_r ...)
   (where (any_l ...) (set-names-set smt-set_l))
   (where (any_r ...) (set-names-set smt-set_r))]
  [(set-names-set (smt-complement smt-set))
   (set-names-set smt-set)])

(define-metafunction aa-smt
  sat-unsat-out : (string ...) number -> (number ...)
  [(sat-unsat-out () number) ()]
  [(sat-unsat-out ("sat" "unsat" string ...) number)
   (sat-unsat-out (string ...) ,(+ `number 1))]
  [(sat-unsat-out (string_1 string_2 string_r ...) number)
   (number number_r ...)
   (where (number_r ...) (sat-unsat-out (string_r ...) ,(+ `number 1)))])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;        ;;;;;;;;  ;;;;;;;;    ;;;;;;  ;;;;;;;;    ;;;;;;
;           ;;     ;;        ;;           ;;     ;;
;           ;;     ;;        ;;           ;;     ;;
;           ;;     ;;;;;      ;;;;;;      ;;      ;;;;;; 
;           ;;     ;;              ;;     ;;           ;;
;           ;;     ;;              ;;     ;;           ;;
;           ;;     ;;;;;;;;  ;;;;;;       ;;     ;;;;;;  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(smt-reset-names)
#;(check-equal? (term (C->smt ε (dsj (ℱx x_lam) (ℱ ·)) (gen-sym)))
              (term ((smt-setdisjoint ("set1" (ℱx x_lam)) ("set2" (ℱ ·))))))
#;(check-equal? (term (smt->text ((smt-setdisjoint ("set1" (ℱx x_lam)) ("set2" (ℱ ·))))))
              '("(assert (disjoint set1 set2))"))

;(displayln "Use metafunction check-obls : obls -> #t or #f to check proof obligations")
;(displayln "(maybe edit Z3-COMMAND definition at the top of the file if z3 is not in PATH)")
;(displayln "Example line: (term (check-obls ((ε (dsj (ℱx x_lam) (ℱ ·)) ⊩ true))))")

;(define exp-ty `(Prod ((Atom ∅) (Atom ∅)) (⊎ 0 1)))
; (define mk-bndr-fD
;   `(define-fn mk-bndr ((x_a Atom) (x_b Atom)) (dsj (ℱ x_a) (ℱ x_b))
;      ,exp-ty
;      (eprod ((x_a ∅) (x_b ∅)) (⊎ 0 1)) ;; make a prod that exports both xes
;      (= (ℱb ·) (∪ (ℱ x_a) (ℱ x_b))))) ;; postcondition
;
; (parameterize
;  ((fn-defs `(,mk-bndr-fD)))
;
;  (term (check-obls 
;   ;; this ought to be unsatisfiable
;   ,(obls-of
;    `(efresh x_c (efresh x_d (ecall mk-bndr x_c x_d)))))))
