#lang racket
(require "aa-redex-core.rkt")
(require "aa-redex-type.rkt")
(require "aa-redex-util.rkt")
(require "aa-redex-proo.rkt")
(require "aa-redex-logi.rkt")
(require redex/reduction-semantics)

(provide (all-defined-out))
#;(provide aa-sugar desugar-type desugar-function strip-types lookup-env/stx lookup-env/sources lookup-env/type modify-env)

(define-extended-language aa-sugar aa
  [type-decls (type-decl ...)]
  [fun-decls (fun-decl ...)]
  [type-decl (define-type t type)]
  [id variable]
  [t id]
  [prod-type (id (t b) ... b)]
  [b natural 
     ()
     (@ b ...)
     (U b ...)]
  [type Atom
        RefAtom
        prod-type
        (union prod-type ...)]
  [C/A C/S
       (∧ C/A C/A)]
  [C/S (true any)
       ((ss→C s_l s_r) any)]
  [fun-decl (define-fun (id any) ((var t) ...) C/A t C/A exp)]
  [arg-exp var
           ((id arg-exp ...) any)]
  [var (x any)]
  [exp arg-exp
       (let (var exp C/A) ... exp)
       (let/infer (var arg-exp) ... exp)
       (ifeq arg-exp arg-exp exp exp)
       (match arg-exp ((id var ...) exp) ...)
       (open arg-exp (id var ...) exp)
       (fresh var ... exp)])
            
(define-extended-language aa-sugar/compile aa-sugar
  [typex anytype type]
  [wrap-exp WrapHole 
            (elet x C e wrap-exp)]
  [we e wrap-exp]
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
       (qcons any)]
  [pres pre
        (∧ pres pres)]
  [env (envx ...)]
  ;; [Variable] [Type] [Syntax Object of Declaration Occurrence] 
  ;; [Binders: ([Variable] [Syntax Object of Constructor/Destructor]) ...]
  ;; [Refs: ([Variable] [Syntax Object of Constructor/Destructor]) ...]
  [envx (x type any (var ...))]
  [FD fun-decl]
  [FDs (FD ...)]
  [TD type-decl]
  [TDs (TD ...)])

;; -----------------------------------------------------------------------------
;; Desugar Type
;; -----------------------------------------------------------------------------

(define-metafunction aa-sugar
  desugar-type : t type-decls ((t X) ...) -> τ
  [(desugar-type t type-decls ((t_l X_l) ... (t X) (t_r X_r) ...)) X]
  [(desugar-type t type-decls ((t_rec X_tvar) ...))
   ,(let ([typevar (term t)])
      (term (μ ,typevar (desugar-type/decl (typename->type t type-decls) type-decls ((t ,typevar) (t_rec X_tvar) ...)))))
   (side-condition (term (type-recursive? t t type-decls ())))]
  [(desugar-type t type-decls ((t_rec X_tvar) ...)) 
   (desugar-type/decl (typename->type t type-decls) type-decls ((t_rec X_tvar) ...))])

(define-metafunction aa-sugar
  desugar-type/decl : type type-decls ((t X) ...) -> τ
  [(desugar-type/decl Atom type-decls ((t X) ...)) Atom]
  [(desugar-type/decl RefAtom type-decls ((t X) ...)) RefAtom]
  [(desugar-type/decl (id (t_ds b) ... b_ex) type-decls ((t X) ...))
   (Prod (((desugar-type t_ds type-decls ((t X) ...)) (desugar-bindings b)) ...) (desugar-bindings b_ex))]
  [(desugar-type/decl (union prod-type) type-decls ((t X) ...))
   (desugar-type/decl prod-type type-decls ((t X) ...))]
  [(desugar-type/decl (union prod-type_l prod-type_r ...) type-decls ((t X) ...))
   (+ (desugar-type/decl prod-type_l type-decls ((t X) ...))
      (desugar-type/decl (union prod-type_r ...) type-decls ((t X) ...)))])

(define-metafunction aa-sugar
  desugar-bindings : b -> β
  [(desugar-bindings ()) ∅]
  [(desugar-bindings natural) natural]
  [(desugar-bindings (@ b)) (desugar-bindings b)]
  [(desugar-bindings (U b)) (desugar-bindings b)]
  [(desugar-bindings (@ b b_rest ...)) 
   (@ (desugar-bindings b) (desugar-bindings (@ b_rest ...)))]
  [(desugar-bindings (U b b_rest ...)) 
   (⊎ (desugar-bindings b) (desugar-bindings (U b_rest ...)))])

(define-metafunction aa-sugar
  type-recursive? : t t type-decls (t ...) -> #t or #f
  [(type-recursive? t t_cur type-decls (t_l ... t_cur t_r ...)) #f]
  [(type-recursive? t t_cur type-decls (t_seen ...))
   (type-recursive?-type t type type-decls (t_cur t_seen ...))
   (where ((define-type t_l type_l) ... (define-type t_cur type) (define-type t_r type_r) ...) type-decls)])

(define-metafunction aa-sugar
  type-recursive?-type : t type type-decls (t ...) -> #t or #f
  [(type-recursive?-type t Atom type-decls (t_seen ...)) #f]
  [(type-recursive?-type t RefAtom type-decls (t_seen ...)) #f]
  [(type-recursive?-type t prod-type type-decls (t_seen ...)) 
   (type-recursive?-prod t prod-type type-decls (t_seen ...))]
  [(type-recursive?-type t (union prod-type ...) type-decls (t_seen ...)) 
   ,(foldr (lambda (x y) (or x y)) #f (term ((type-recursive?-prod t prod-type type-decls (t_seen ...)) ...)))])

(define-metafunction aa-sugar
  type-recursive?-prod : t prod-type type-decls (t ...) -> #t or #f
  [(type-recursive?-prod t (id () b) type-decls (t_seen ...)) #f]
  [(type-recursive?-prod t (id (t_l b_l) ... (t b) (t_r b_r) ... b_ex) type-decls (t_seen ...)) #t]
  [(type-recursive?-prod t (id (t_s b_s) ... b_ex) type-decls (t_seen ...)) 
   ,(foldr (lambda (x y) (or x y)) #f (term ((type-recursive? t t_s type-decls (t_seen ...)) ...)))])

(define-metafunction aa-sugar
  typename->type : t type-decls -> type
  [(typename->type t (type-decl_l ... (define-type t type) type-decl_r ...)) type]
  [(typename->type t type-decls) 
   ,(raise-syntax-error 'type-lookup (format "No type of this name declared: ~a" (term t)) #f #f '())])

(define-metafunction aa-sugar
  constructor->typename : id type-decls -> t
  [(constructor->typename id (type-decl_l ... (define-type t (id (t_f b_f) ... b)) type-decl_r ...)) t]
  [(constructor->typename id (type-decl_l ... (define-type t (union prod-type_l ... (id (t_f b_f) ... b) prod-type_r ...)) type-decl_r ...)) t])

;; -----------------------------------------------------------------------------
;; Desugar Code
;; -----------------------------------------------------------------------------

(define-metafunction aa-sugar/compile
  desugar-function : FD FDs TDs -> (fD (xenv ...))
  [(desugar-function (define-fun (id any_fd) (((x any)  t) ...) C/A_pre t_ret C/A_post exp) FDs TDs)
   ((define-fn id 
     ((x (desugar-type t TDs ())) ...) 
     C_pre 
     (desugar-type t_ret TDs ()) 
     e
     C_post)
    (xenv ...))
   (where (C_pre pres) (desugar-constraint/pre C/A_pre ·))
   (where (C_post poss) (desugar-constraint/post C/A_post))
   (where (e type (xenv ...)) (desugar-exp exp (typename->type t_ret TDs) FDs TDs ((x (typename->type t TDs) any ()) ...) poss pres))])

;; Main desugaring function.
;; returns expression, it's type and the ann
(define-metafunction aa-sugar/compile
  desugar-exp : exp typex FDs TDs env poss pres -> (e type (xenv ...))
  [(desugar-exp (x any) typex FDs TDs env poss pres)
   (x RefAtom ((env poss (∧ pres (qcons any)))))
   (where RefAtom (lookup-env/type x env))]
  [(desugar-exp (x any) RefAtom FDs TDs env poss pres)
   ((ref x) RefAtom ((env poss (∧ pres (qcons any)))))
   (where Atom (lookup-env/type x env))]
  [(desugar-exp (x any) typex FDs TDs env poss pres)
   (x (lookup-env/type x env) ((env poss (∧ pres (qcons any)))))]
  [(desugar-exp arg-exp typex FDs TDs env poss pres)
   (desugar-argexprs/wrap ((x arg-exp typex)) ,(mk-qlit (term x) (term type) (term any_pos)) FDs TDs env poss pres)
   (where x ,(gensym))
   (where type (argexp->type arg-exp FDs TDs env))
   (where (any_arg any_pos) arg-exp)]
  [(desugar-exp (let exp) typex FDs TDs env poss pres)
   (desugar-exp exp typex FDs TDs env poss pres)]
  [(desugar-exp (let (var exp_let C/A) (var_rest exp_rest C/A_rest) ... exp) typex FDs TDs env poss pres)
   (make-elet var C/A exp_let (let (var_rest exp_rest C/A_rest) ... exp) typex FDs TDs env poss pres)]
  [(desugar-exp (let/infer ((x_n any) arg-exp) ... exp) typex FDs TDs env poss pres)
   (desugar-argexprs/wrap ((x_n (any_arg any) anytype) ...) 
                          ,(lambda (lenv lposs lpres) (term (desugar-exp exp typex FDs TDs ,lenv ,lposs ,lpres)))
                          FDs TDs env poss pres)
   (where ((any_arg any_pos) ...) (arg-exp ...))]
  [(desugar-exp (ifeq arg-exp_l arg-exp_r exp_t exp_e) typex FDs TDs env poss pres)
   (desugar-argexprs/wrap ((x_eval arg-exp_eval typex_eval) ...) 
                          ,(mk-eifeq (term (x_l any_l)) (term (x_r any_r)) (term exp_t) (term exp_e) (term typex) (term FDs) (term TDs))
                          FDs TDs env poss pres)
   (where type (argexp->type arg-exp_l FDs TDs env))
   (where type (argexp->type arg-exp_r FDs TDs env))
   (where (((x_eval arg-exp_eval typex_eval) ...) ((x_l any_l) (x_r any_r))) (split-args ((arg-exp_l type) (arg-exp_r type)) env))]
  [(desugar-exp (ifeq arg-exp_l arg-exp_r exp_t exp_e) typex FDs TDs env poss pres)
   (desugar-argexprs/wrap ((x_eval arg-exp_eval typex_eval) ...) 
                          ,(mk-eifeq (term (x_l any_l)) (term (x_r any_r)) (term exp_t) (term exp_e) (term typex) (term FDs) (term TDs))
                          FDs TDs env poss pres)
   (where type_l (argexp->type arg-exp_l FDs TDs env))
   (where type_r (argexp->type arg-exp_r FDs TDs env))
   (side-condition (and (member (term type_l) '(RefAtom Atom)) (member (term type_r) '(RefAtom Atom))))
   (where (((x_eval arg-exp_eval typex_eval) ...) ((x_l any_l) (x_r any_r))) (split-args ((arg-exp_l RefAtom) (arg-exp_r RefAtom)) env))]
  [(desugar-exp (match arg-exp ((id var_p ...) exp) ...) typex FDs TDs env poss pres)
   (desugar-argexprs/wrap ((x_eval arg-exp_eval typex_eval) ...)
                          ,(lambda (lenv lposs lpres) (term (wrap-case x_arg (union prod-type prod-type_r ...) any_arg (((id var_p ...) exp) ...) typex FDs TDs ,lenv ,lposs ,lpres)))
                          FDs TDs env poss pres)
   (where (union prod-type prod-type_r ...) (argexp->type arg-exp FDs TDs env))
   (where (((x_eval arg-exp_eval typex_eval) ...) ((x_arg any_arg))) (split-args ((arg-exp anytype)) env))]
  [(desugar-exp (open arg-exp (id (x_a any_a) ..._n) exp) typex FDs TDs env poss pres)
    (desugar-argexprs/wrap ((x_eval arg-exp_eval typex_eval) ...)
                           ,(mk-eopen (term (x_arg any_arg)) (term (((x_a any_a) (typename->type t_b TDs)) ...)) (term exp) (term typex) (term FDs) (term TDs))
                           FDs TDs env poss pres)
    (where (id (t_b b_b) ..._n b_ex) (argexp->type arg-exp FDs TDs env))
    (where (((x_eval arg-exp_eval typex_eval) ...) ((x_arg any_arg))) (split-args ((arg-exp anytype)) env))]
  [(desugar-exp (fresh exp) typex FDs TDs env poss pres)
   (desugar-exp exp typex FDs TDs env poss pres)]
  [(desugar-exp (fresh (x any) var ... exp) typex FDs TDs env (pos ...) pres)
   (make-efresh (x any) (fresh var ... exp) typex FDs TDs env (pos ...) pres)]
  
  ;; Error cases
  [(desugar-exp (open arg-exp (id (x_a any_a) ...) exp) typex FDs TDs env poss pres)
   ,(raise-syntax-error 'open (format "Malformed open: ~a" (term type)) 'open #f (term (any_a ...)))
   (where (x_arg type any_arg #;(id (t b) ..._n b_ex) wrap-exp env_arg (xenv_arg ...) (pres_arg ...)) (desugar-argexp/var arg-exp anytype FDs TDs env pres))
   #;(where (e_open type_out (xenv_open ...)) (desugar-exp exp typex FDs TDs (extend-env ((x_a (typename->type t TDs) any_a) ...) (join-env env_arg env))))]
  
  [(desugar-exp (let/infer ((x_n any) arg-exp) any_rest ... exp) typex FDs TDs env (pos ...) pres)
   ,(raise-syntax-error 'ilet (format "Could not compile rest of inferred let statement") (term any) #f '())
   (where (x_arg type_arg any_arg wrap-exp env_arg (xenv_arg ...) (pres_arg ...)) (desugar-argexp/var arg-exp anytype FDs TDs env pres))
   #;(where (e_body type_out (xenv_body ...)) (desugar-exp (let/infer any_rest ... exp) typex FDs TDs (extend-env ((x_n type_arg any)) (join-env env_arg env)) (pos ...) (join-pres pres (pres_arg ...))))]
  [(desugar-exp (let/infer ((x_n any) arg-exp) any_rest ... exp) typex FDs TDs env (pos ...) pres)
   ,(raise-syntax-error 'ilet (format "Could not decode binding expression") (term any) #f '())
   #;(where (x_arg type_arg any_arg wrap-exp env_arg (xenv_arg ...) (pres_arg ...)) (desugar-argexp/var arg-exp anytype FDs TDs env pres))
   #;(where (e_body type_out (xenv_body ...)) (desugar-exp (let/infer any_rest ... exp) typex FDs TDs (extend-env ((x_n type_arg any)) (join-env env_arg env)) (pos ...) (join-pres pres (pres_arg ...))))])

(define-metafunction aa-sugar/compile
  wrap-case : x type any (((id var ...) exp) ...) typex FDs TDs env poss pres -> (e type (xenv ...))
  [(wrap-case x_c (union (id (t b) ..._n b_ex)) any (((id var ..._n) exp)) typex FDs TDs env #;(envx_l ... (x_c (union (id (t b) ..._n b_ex)) any any_source) envx_r ...) poss pres)
   (desugar-exp (open (x_c any) (id var ...) exp) typex FDs TDs (modify-env x_c (id (t b) ... b_ex) (lookup-env/stx x_c env) (lookup-env/sources x_c env) env) #;(envx_l ... (x_c (id (t b) ... b_ex) any any_source) envx_r ...) poss pres)
   (where (union (id (t b) ..._n b_ex)) (lookup-env/type x_c env))]
  [(wrap-case x_c (union (id (t b) ..._n b_ex) prod-type ..._m) any (((id var ..._n) exp) any_rc ..._m) typex FDs TDs env poss pres)
   ((ecase x_c 
           x_id e_left
           x_nc e_right) type (xenv_left ... xenv_right ...))
   (side-condition (> (length (term (prod-type ...))) 0))
   (where x_id ,(gensym (term id)))
   (where x_nc ,(gensym (term x_c)))
   (where (e_left type (xenv_left ...)) (desugar-exp (open (x_id any) (id var ...) exp) typex FDs TDs (extend-env ((x_id (id (t b) ... b_ex) any)) env) poss (∧ pres (caseleft (x_c any) (x_id any)))))
   (where (e_right type (xenv_right ...)) (wrap-case x_nc (union prod-type ...) any (any_rc ...) typex FDs TDs (extend-env ((x_nc (union prod-type ...) any)) env) poss (∧ pres (caseright (x_c any) (x_nc any)))))])

(define-metafunction aa-sugar/compile
  argexp->type : arg-exp FDs TDs env -> type
  [(argexp->type (x any) FDs TDs env)
   (lookup-env/type x env)]
  [(argexp->type ((id any_args ..._n) any) FDs TDs env)
   (typename->type t_out TDs)
   (where (FD_l ... (define-fun (id any_fd) (((x_formal any_formal) t_arg) ..._n) C/A_pre t_out C/A_post exp) FD_r ...) FDs)]
  [(argexp->type ((id any_args ..._n) any) FDs TDs env)
   type_val
   (where type_val (typename->type (constructor->typename id TDs) TDs))])

(define-metafunction aa-sugar/compile
  desugar-argexprs/wrap : ((x arg-exp typex) ...) any FDs TDs env poss pres -> (e type (xenv ...))
  ;; Continue with inner expression
  [(desugar-argexprs/wrap () any FDs TDs env poss pres)
   ,((term any) (term env) (term poss) (term pres))]
  ;; Convert Binder into Reference
  [(desugar-argexprs/wrap ((x (x_arg any_pos) RefAtom) any_rest ...) any FDs TDs env poss pres)
   ((elet x (= (ℱr ·) (ℱb x_arg)) (ref x_arg) e) type (xenv_add xenv ...))
   (where Atom (lookup-env/type x_arg env)) ;; Variable is Atom
   (where env_new (extend-env/source x RefAtom any_pos ((x_arg any_pos)) env))
   (where pres_new (∧ pres (∧ (annot ((= (ℱr ·) (ℱb x_arg)) any_pos)) (letsub (x any_pos)))))
   (where xenv_add (env ((ignore any_pos (= (ℱr ·) (ℱb x_arg)))) (∧ pres (qcons any_pos))))
   (where (e type (xenv ...)) (desugar-argexprs/wrap (any_rest ...) any FDs TDs env_new poss pres_new))]
  ;; introduce new variable
  [(desugar-argexprs/wrap ((x (x_arg any_pos) typex) any_rest ...) any FDs TDs env poss pres)
   ((elet x (= (ℱa ·) (ℱa x_arg)) (ref x_arg) e) type (xenv_add xenv ...))
   (where type (lookup-env/type x_arg env))
   (side-condition (or (equal? (term typex) (term type)) (equal? (term typex) (term anytype))))
   (where env_new (extend-env/source x type any_pos ((x_arg any_pos)) env))
   (where pres_new (∧ pres (∧ (annot ((= (ℱa ·) (ℱa x_arg)) any_pos)) (letsub (x any_pos)))))
   (where xenv_add (env ((ignore any_pos (= (ℱa ·) (ℱa x_arg)))) (∧ pres (qcons any_pos))))
   (where (e type (xenv ...)) (desugar-argexprs/wrap (any_rest ...) any FDs TDs env_new poss pres_new))]
  ;; Convert Binder function result in Reference (invent new name, put on stack)
  [(desugar-argexprs/wrap ((x ((id arg-exp ..._n) any_pos) RefAtom) any_rest ...) any FDs TDs env poss pres)
   (desugar-argexprs/wrap ((x_gen ((id arg-exp ...) any_pos) Atom) (x (x_gen any_pos) RefAtom) any_rest ...) any FDs TDs env poss pres)
   (where (FD_l ... (define-fun (id any_fd) (((x_formal any_formal) t_arg) ..._n) C/A_pre t_out C/A_post exp) FD_r ...) FDs)
   (where Atom (typename->type t_out TDs))
   (where x_gen ,(gensym (term x)))]
  ;; Call function that has all its arguments evaluated
  [(desugar-argexprs/wrap ((x ((id (x_arg any_arg) ..._n) any_pos) typex) any_rest ...) any FDs TDs env poss pres)
   ((elet x C (ecall id x_arg ...) e_body) type (xenv_pre xenv_invoc xenv ...))
   
   ;; Lookup function, return type, and add variable x with that type to the environment for handing down
   (where (FD_l ... (define-fun (id any_fd) (((x_formal any_formal) t_arg) ..._n) C/A_pre t_out C/A_post exp) FD_r ...) FDs)
   (where type_val (typename->type t_out TDs))
   (where env_new (extend-env/source x type_val any_pos ((x_arg any_arg) ...) env))
   
   ;; Check if variables have right types (RefAtom)
   (where (type_args ...) ((lookup-env/type x_arg env) ...))
   (where (type_args ...) ((typename->type t_arg TDs) ...))
   
   ;; Postconditions - used for pres handed down (see pres_new)
   (where (C_post/pre pres_post) (desugar-constraint/fc-pre C/A_post x ((x_formal x_arg) ...) any_fd any_pos))
   
   ;; Preconditions - used for poss in precondition obligation
   (where (C_pre poss_pre) (desugar-constraint/fc C/A_pre ((x_formal x_arg) ...) any_fd any_pos))
   
   ;; Postconditions - used for constraint on let and poss in invocation xenv
   (where (C_post poss_post) (desugar-constraint/fc C/A_post ((x_formal x_arg) ...) any_fd any_pos))
   
   ;; Actual constraint for let: add environment constraint to function postconditions
   (where C (∧ (⊆ (ℱ ·) (ℱe (extend ε ((x_arg (desugar-type t_arg TDs ())) ...)))) C_post))
   
   ;; These preconditions are handed down. They are the current preconditions + function call (environment + postcondition) + let-environment
   (where pres_new (∧ pres (∧ (∧ (fcenv any_fd any_pos) pres_post) (letsub (x any_pos)))))
   
   ;; the precondition is evaluated in the current environment, on the preconditions and with the current pres
   (where xenv_pre (env poss_pre pres))
   
   ;; the postcondition is evaluated in the current environment, on the postconditions and with the postconditions as knowledge (-> trivial)
   (where (C_post/parts ...) (split-∧ C_post))
   (where xenv_invoc (env ((ignore any_pos (⊆ (ℱ ·) (ℱe (extend ε ((x_arg (desugar-type t_arg TDs ())) ...))))) (ignore any_pos C_post/parts) ...) 
                          (∧ pres (∧ (fcenv any_fd any_pos) pres_post))))
   
   (where (e_body type (xenv ...)) (desugar-argexprs/wrap (any_rest ...) any FDs TDs env_new poss pres_new))]
  
  ;; Function call without fully evaluated arguments
  [(desugar-argexprs/wrap ((x ((id (any_argexp any_arg) ..._n) any_pos) typex) any_rest ...) any FDs TDs env poss pres)
   (desugar-argexprs/wrap ((x_eval arg-exp_eval typex_eval) ... (x ((id (x_arg any_arg) ...) any_pos) typex) any_rest ...) any FDs TDs env poss pres)
   
   ;; Lookup function
   (where (FD_l ... (define-fun (id any_fd) (((x_formal any_formal) t_arg) ..._n) C/A_pre t_out C/A_post exp) FD_r ...) FDs)
   
   (where (((x_eval arg-exp_eval typex_eval) ...) ((x_arg any_arg) ...)) (split-args (((any_argexp any_arg) (typename->type t_arg TDs)) ...) env))
   (side-condition (> (length (term (x_eval ...))) 0))]
  
  ;; Call constructor that has all its arguments evaluated
  [(desugar-argexprs/wrap ((x ((id (x_arg any_arg) ..._n) any_pos) typex) any_rest ...) any FDs TDs env poss pres)
   ((elet x C_c e_c e_body) type (xenv_pre xenv ...))
   
   ;; Lookup constructor, return type, and add variable x with that type to the environment for handing down
   (where type_val (typename->type (constructor->typename id TDs) TDs))
   (where (type_arg ..._n) (constructor->argtypes id type_val TDs))
   (where env_new (extend-env/source x type_val any_pos ((x_arg any_arg) ...) env))
   
   ;; Check if variables have right types (RefAtom)
   (where (type_arg ...) ((lookup-env/type x_arg env) ...))
   
   ;; Create qlit and postcondition
   (where (e_c C_c) (desugar-constructor id type_val (x_arg ...) TDs))
   (where (C_c/parts ...) (split-∧ C_c))
   
   ;; These preconditions are handed down. They are the current preconditions + function call (environment + postcondition) + let-environment
   (where pres_new (∧ pres (∧ (qcons any_pos) (letsub (x any_pos)))))
   
   ;; the constraint is evaluated in the current environment, postcondition and current preconditions
   (where xenv_pre (env ((ignore any_pos C_c/parts) ...) (∧ pres (qcons any_pos))))
   
   (where (e_body type (xenv ...)) (desugar-argexprs/wrap (any_rest ...) any FDs TDs env_new poss pres_new))]
  
  ;; Constructor call without fully evaluated arguments
  [(desugar-argexprs/wrap ((x ((id (any_argexp any_arg) ..._n) any_pos) typex) any_rest ...) any FDs TDs env poss pres)
   (desugar-argexprs/wrap ((x_eval arg-exp_eval typex_eval) ... (x ((id (x_arg any_arg) ...) any_pos) typex) any_rest ...) any FDs TDs env poss pres)
   
   ;; Lookup Constructor
   (where type_out (typename->type (constructor->typename id TDs) TDs))
   (where (type_arg ..._n) (constructor->argtypes id type_out TDs))
   
   (where (((x_eval arg-exp_eval typex_eval) ...) ((x_arg any_arg) ...)) (split-args (((any_argexp any_arg) type_arg) ...) env))
   (side-condition (> (length (term (x_eval ...))) 0))])

(define-metafunction aa-sugar/compile
  split-args : ((arg-exp typex) ...) env -> (((x arg-exp typex) ...) (var ...))
  [(split-args () env) (() ())]
  [(split-args (((x any) typex) any_rest ...) env)
   ((any_evals ...) ((x any) var_r ...))
   (where type (lookup-env/type x env))
   (side-condition (member (term typex) (term (anytype type))))
   (where ((any_evals ...) (var_r ...)) (split-args (any_rest ...) env))]
  [(split-args (((x_c any_pos) typex) any_rest ...) env)
   (((x (x_c any_pos) typex) any_evals ...) ((x any_pos) var ...))
   (where x ,(gensym (term x_c)))
   (where ((any_evals ...) (var ...)) (split-args (any_rest ...) env))]
  [(split-args ((((id any_args ...) any_pos) typex) any_rest ...) env)
   (((x ((id any_args ...) any_pos) typex) any_evals ...) ((x any_pos) var ...))
   (where x ,(gensym (term id)))
   (where ((any_evals ...) (var ...)) (split-args (any_rest ...) env))])

(define-metafunction aa-sugar/compile
  constructor->argtypes : id type TDs -> (type ...)
  [(constructor->argtypes id prod-type TDs)
   (constructor->argtypes id (union prod-type) TDs)]
  [(constructor->argtypes id (union (id (t_arg b) ..._n b_expt) prod-type ...) TDs)
   ((typename->type t_arg TDs) ...)]
  [(constructor->argtypes id (union prod-type_first prod-type ...) TDs)
   (constructor->argtypes id (union prod-type ...) TDs)])

(define-metafunction aa-sugar/compile
  desugar-constructor : id type (x ...) TDs -> (e C)
  [(desugar-constructor id prod-type (x ...) TDs)
   (desugar-constructor id (union prod-type) (x ...) TDs)]
  [(desugar-constructor id (union (id (t_arg b) ..._n b_expt)) (x ..._n) TDs)
   (postcond-prod (eprod ((x (desugar-bindings b)) ...) (desugar-bindings b_expt)) (desugar-type/decl (id (t_arg b) ... b_expt) TDs ()))
   #;((eprod ((x (desugar-bindings b)) ...) (desugar-bindings b_expt)) (postcond-product (x ...) ((desugar-type t_arg TDs ()) ...) (b ...) b_expt))]
  [(desugar-constructor id (union (id (t_arg b) ..._n b_expt) prod-type_r1 prod-type_r ...) (x ..._b) TDs)
   ((einj0 e_inj (desugar-type/decl (union prod-type_r1 prod-type_r ...) TDs ())) C)
   (where (e_inj C) (desugar-constructor id (union (id (t_arg b) ... b_expt)) (x ...) TDs))]
  [(desugar-constructor id (union prod-type_l prod-type_r ...) (x ...) TDs)
   ((einj1 (desugar-type/decl prod-type_l TDs ()) e_inj) C)
   (where (e_inj C) (desugar-constructor id (union prod-type_r ...) (x ...) TDs))])

(define-metafunction aa-sugar/compile
  postcond-prod : qlit τ -> (e C)
  [(postcond-prod qlit τ)
   (qlit (∧ (= (ℱb ·) (pe-fn ℱb qlit τ)) (= (ℱr ·) (pe-fn ℱr qlit τ))))])

(define-metafunction aa-sugar/compile
  desugar-constraint/post : C/A -> (C poss)
  [(desugar-constraint/post (∧ C/A_l C/A_r)) 
   ((∧ C_l C_r) (pos_l ... pos_r ...))
   (where (C_l (pos_l ...)) (desugar-constraint/post C/A_l))
   (where (C_r (pos_r ...)) (desugar-constraint/post C/A_r))]
  [(desugar-constraint/post (any_l any)) (any_l ((annot (any_l any))))])

(define-metafunction aa-sugar/compile
  desugar-constraint/fc : C/A ((x x) ...) any any -> (C poss)
  [(desugar-constraint/fc (∧ C/A_l C/A_r) ((x_formal x_arg) ...) any_fd any_fc) 
   ((∧ C_l C_r) (pos_l ... pos_r ...))
   (where (C_l (pos_l ...)) (desugar-constraint/fc C/A_l ((x_formal x_arg) ...) any_fd any_fc))
   (where (C_r (pos_r ...)) (desugar-constraint/fc C/A_r ((x_formal x_arg) ...) any_fd any_fc))]
  [(desugar-constraint/fc (C any) ((x_formal x_arg) ...) any_fd any_fc) 
   ((subst-in-C C ((x_formal x_arg) ...)) ((fcpre any_fd any_fc ((subst-in-C C ((x_formal x_arg) ...)) any))))])

(define-metafunction aa-sugar/compile
  desugar-constraint/pre : C/A z -> (C pres)
  [(desugar-constraint/pre (∧ C/A_l C/A_r) z) 
   ((∧ C_l C_r) (∧ pres_l pres_r))
   (where (C_l pres_l) (desugar-constraint/pre C/A_l z))
   (where (C_r pres_r) (desugar-constraint/pre C/A_r z))]
  [(desugar-constraint/pre (any_l any) z) (any_l (annot ((subst-in-C any_l ((· z))) any)))])

(define-metafunction aa-sugar/compile
  desugar-constraint/fc-pre : C/A z ((x x) ...) any any -> (C pres)
  [(desugar-constraint/fc-pre (∧ C/A_l C/A_r) z ((x_formal x_arg) ...) any_fd any_fc) 
   ((∧ C_l C_r) (∧ pres_l pres_r))
   (where (C_l pres_l) (desugar-constraint/fc-pre C/A_l ((x_formal x_arg) ...) any_fd any_fc))
   (where (C_r pres_r) (desugar-constraint/fc-pre C/A_r ((x_formal x_arg) ...) any_fd any_fc))]
  [(desugar-constraint/fc-pre (C any) z ((x_formal x_arg) ...) any_fd any_fc) 
   ((subst-in-C C ((· z) (x_formal x_arg) ...)) (fcpost any_fd any_fc ((subst-in-C C ((· x) (x_formal x_arg) ...)) any)))])


;; -----------------------------------------------------------------------------
;; make-e
;; -----------------------------------------------------------------------------

;[cnd (annot (C any))
;       (pfresh var)
;       (popen var (var ...))]
;  [pos cnd      
;       (fcpre any any (C any))
;       (ignore any C)]
;  [poss (pos ...)]
;  [pre cnd
;       (letsub var)
;       (ifthen var var)
;       (ifelse var var)
;       (fcpost any any (C any))
;       (fcenv any any)
;       (caseleft var var)
;       (caseright var var)
;       (qcons any)]

(define ((mk-qlit qlit type pos) env poss pres)
  (term (make-qlit ,qlit ,type ,pos ,env ,poss ,pres)))
  
(define-metafunction aa-sugar/compile
  make-qlit : qlit type any env poss pres -> (qlit type (xenv ...))
  [(make-qlit qlit type any env poss pres) (qlit type ((env poss (∧ pres (qcons any)))))])

;exp typex FDs TDs env poss pres -> (e type (xenv ...))

(define ((mk-eifeq var1 var2 exp1 exp2 typex FDs TDs) env poss pres)
  (term (make-eifeq ,var1 ,var2 ,exp1 ,exp2 ,typex ,FDs ,TDs ,env ,poss ,pres)))
  
(define-metafunction aa-sugar/compile
  make-eifeq : var var exp exp typex FDs TDs env poss pres -> (e type (xenv ...))
  [(make-eifeq (x_l any_l) (x_r any_r) exp_yes exp_no typex FDs TDs env poss pres) 
   ((eifeq x_l x_r e_yes e_no) type_yes (xenv_yes ... xenv_no ...))
   (where (e_yes type_yes (xenv_yes ...)) (desugar-exp exp_yes typex FDs TDs env poss (∧ pres (ifthen (x_l any_l) (x_r any_r)))))
   (where (e_no type_no (xenv_no ...)) (desugar-exp exp_no typex FDs TDs env poss (∧ pres (ifthen (x_l any_l) (x_r any_r)))))])

(define ((mk-ecase var1 var2 var3 exp1 exp2 typex FDs TDs) env poss pres)
  (term (make-ecase ,var1 ,var2 ,var3 ,exp1 ,exp2 ,typex ,FDs ,TDs ,env ,poss ,pres)))
  
(define-metafunction aa-sugar/compile
  make-ecase : var var var exp exp typex FDs TDs env poss pres -> (e type (xenv ...))
  [(make-ecase (x_c any_c) (x_l any_l) (x_r any_r) exp_l exp_r typex FDs TDs env poss pres) 
   ((ecase x_c x_l e_l x_r e_r) type_l (xenv_l ... xenv_r ...))
   (where (e_l type_l (xenv_l ...)) (desugar-exp exp_l typex FDs TDs env poss (∧ pres (caseleft any_c any_l))))
   (where (e_r type_r (xenv_r ...)) (desugar-exp exp_r typex FDs TDs env poss (∧ pres (caseright any_c any_r))))])

(define ((mk-elet var C exp1 exp2 typex FDs TDs) env poss pres)
  (term (make-elet ,var ,C ,exp1 ,exp2 ,typex ,FDs ,TDs ,env ,poss ,pres)))
  
(define-metafunction aa-sugar/compile
  make-elet : var C/A exp exp typex FDs TDs env poss pres -> (e type (xenv ...))
  [(make-elet (x_c any_c) C/A exp_val exp_body typex FDs TDs env poss pres) 
   ((elet x_c C e_val e_body) type_body (xenv_val ... xenv_body ...))
   (where (C poss_val) (desugar-constraint/post C/A))
   (where (C/pre pres_body) (desugar-constraint/pre C/A x_c))
   (where (e_val type_val (xenv_val ...)) (desugar-exp exp_l anytype FDs TDs env poss_val pres))
   (where (e_body type_body (xenv_body ...)) (desugar-exp exp_r typex FDs TDs (extend-env ((x_c type_val any_c)) env) poss (∧ pres (∧ pres_body (letsub (x_c any_c))))))])

(define ((mk-ecall fid fdp args FDs TDs) env poss pres)
  (term (make-ecall ,fid ,fdp ,args ,FDs ,TDs ,env ,poss ,pres)))
  
(define-metafunction aa-sugar/compile
  make-ecall : id any (var ...) FDs TDs env poss pres -> (e type (xenv ...))
  [(make-ecall id any_fc ((x_actual any_actual) ..._n) FDs TDs env poss pres)
   ((ecall id x_actual ...) type_out ((env poss_pre pres) (env poss (∧ pres (∧ (fcenv any_fd any_fc) pres_post)))))
   (where (FD_l ... (define-fun (id any_fd) (((x_formal any_formal) t_arg) ..._n) C/A_pre t_out C/A_post exp) FD_r ...) FDs)
   (where type_out (typename->type t_out TDs))
   (where (C_pre poss_pre) (desugar-constraint/fc C/A_pre ((x_formal x_arg) ...) any_fd any))
   (where (C_post pres_post) (desugar-constraint/fc-pre C/A_post · ((x_formal x_actual) ...) any_fd any_fc))])

(define ((mk-eopen var vars exp typex FDs TDs) env poss pres)
  (term (make-eopen ,var ,vars ,exp ,typex ,FDs ,TDs ,env ,poss ,pres)))
  
(define-metafunction aa-sugar/compile
  make-eopen : var ((var type) ...) exp typex FDs TDs env poss pres -> (e type (xenv ...))
  [(make-eopen (x any) (((x_sub any_sub) type_b) ...) exp typex FDs TDs env (pos ...) pres)
   ((eopen x (x_sub ...) e) type (xenv ...))
   (where (e type (xenv ...)) (desugar-exp exp typex FDs TDs (extend-env ((x_sub type_b any_sub) ...) env) (pos ... (popen (x any) ((x_sub any_sub) ...))) (∧ pres (popen (x any) ((x_sub any_sub) ...)))))])

(define ((mk-efresh var exp typex FDs TDs) env poss pres)
  (term (make-efresh ,var ,exp ,typex ,FDs ,TDs ,env ,poss ,pres)))
  
(define-metafunction aa-sugar/compile
  make-efresh : var exp typex FDs TDs env poss pres -> (e type (xenv ...))
  [(make-efresh (x any) exp typex FDs TDs env (pos ...) pres)
   ((efresh x e) type (xenv ...))
   (where (e type (xenv ...)) (desugar-exp exp typex FDs TDs (extend-env ((x Atom any)) env) (pos ... (pfresh (x any))) (∧ pres (pfresh (x any)))))])

;; -----------------------------------------------------------------------------
;; Environment
;; -----------------------------------------------------------------------------

(define-metafunction aa-sugar/compile
  lookup-env : x env -> envx
  [(lookup-env x (envx_l ... (x type any any_var) envx_r ...))
   (x type any any_var)])

(define-metafunction aa-sugar/compile
  lookup-env/type : x env -> type
  [(lookup-env/type x (envx_l ... (x type any any_var) envx_r ...))
   type])

(define-metafunction aa-sugar/compile
  lookup-env/stx : x env -> any
  [(lookup-env/stx x (envx_l ... (x type any any_var) envx_r ...))
   any])

(define-metafunction aa-sugar/compile
  lookup-env/sources : x env -> (var ...)
  [(lookup-env/sources x (envx_l ... (x type any (var ...)) envx_r ...))
   (var ...)])


(define-metafunction aa-sugar/compile
  extend-env : ((x type any) ...) env -> env
  [(extend-env ((x type any) ...) env) 
   ,(foldr (lambda (v e) (term (extend-env/x ,v ,e))) (term env) (term ((x type any ()) ...)))])

(define-metafunction aa-sugar/compile
  extend-env/x : envx env -> env
  [(extend-env/x envx (envx_l ... envx envx_r ...))
   (envx_l ... envx envx_r ...)]
  [(extend-env/x (x type any any_var) (envx_l ... (x type_x any_x any_varx) envx_r ...))
   ,(raise-syntax-error 'scope (format "Variable ~a already declared!" (term x)) (term any) #f (term (any_x)))]
  [(extend-env/x envx (envx_e ...)) (envx envx_e ...)])

(define-metafunction aa-sugar/compile
  extend-env/source : x type any (var ...) env -> env
  [(extend-env/source x type any (var ...) env)
   (extend-env/x (x type any (var ...)) env)])

(define-metafunction aa-sugar/compile
  join-env : env ... -> env
  [(join-env) ()]
  [(join-env env) env]
  [(join-env () env ...) (join-env env ...)]
  [(join-env (envx envx_r ...) env env_r ...)
   (join-env (envx_r ...) (extend-env/x envx env) env_r ...)])

(define-metafunction aa-sugar/compile
  modify-env : x type any (var ...) env -> env
  [(modify-env x type any any_var (envx_l ... (x type_x any_x any_varx) envx_r ...))
   (envx_l ... (x type any any_var) envx_r ...)])

(define-metafunction aa-sugar/compile
  join-pres : pres (pres ...) -> pres
  [(join-pres pres ()) pres]
  [(join-pres pres (pres_f pres_r ...))
   (join-pres (∧ pres pres_f) (pres_r ...))])

(define-metafunction aa-sugar/compile
  join-pres/nolet : pres (pres ...) -> pres
  [(join-pres/nolet pres ()) pres]
  [(join-pres/nolet pres ((∧ pres_l (letsub (x any))))) (∧ pres pres_l)]
  [(join-pres/nolet pres (pres_f pres_r ...))
   (join-pres/nolet (∧ pres pres_f) (pres_r ...))])

;; -----------------------------------------------------------------------------
;; Helpers
;; -----------------------------------------------------------------------------

(define-metafunction aa-sugar/compile
  flatten-b : (b ...) -> (natural ...)
  [(flatten-b ()) ()]
  [(flatten-b (natural b ...))
   (natural natural_rest ...)
   (where (natural_rest ...) (flatten-b (b ...)))]
  [(flatten-b (() b ...))
   (natural_rest ...)
   (where (natural_rest ...) (flatten-b (b ...)))]
  [(flatten-b ((@ b_s ...) b ...))
   (natural_s ... natural_rest ...)
   (where (natural_s ...) (flatten-b (b_s ...)))
   (where (natural_rest ...) (flatten-b (b ...)))]
  [(flatten-b ((U b_u ...) b ...))
   (natural_u ... natural_rest ...)
   (where (natural_u ...) (flatten-b (b_u ...)))
   (where (natural_rest ...) (flatten-b (b ...)))])

(define-metafunction aa-sugar/compile
  strip-types : fD -> fD
  [(strip-types (define-fn f ((x τ) ...) C_pre τ_out e C_post))
   (define-fn f ((x Atom) ...) C_pre Atom (strip-types/e e) C_post)])

(define-metafunction aa-sugar/compile
  strip-types/e : e -> e
  [(strip-types/e (ecall f x ...)) (ecall f x ...)]
  [(strip-types/e (efresh x e)) (efresh x (strip-types/e e))]
  [(strip-types/e (elet x C e_l e_r)) 
   (elet x C (strip-types/e e_l) (strip-types/e e_r))]
  [(strip-types/e (ecase x x_l e_l x_r e_r))
   (ecase x x_l (strip-types/e e_l) x_r (strip-types/e e_r))]
  [(strip-types/e (eopen x_o (x ...) e))
   (eopen x_o (x ...) (strip-types/e e))]
  [(strip-types/e (eifeq x_l x_r e_l e_r)) 
   (eifeq x_l x_r (strip-types/e e_l) (strip-types/e e_r))]
  [(strip-types/e x) x]
  [(strip-types/e (einj0 qlit τ))
   (einj0 (strip-types/e qlit) Atom)]
  [(strip-types/e (einj1 τ qlit)) 
   (einj1 Atom (strip-types/e qlit))]
  [(strip-types/e (eprod ((qlit β) ...) β_ex)) 
   (eprod (((strip-types/e qlit) β) ...) β_ex)])

(define-metafunction aa-sugar/compile
  split-∧ : C -> (C ...)
  [(split-∧ (∧ C_l C_r))
   (C_left ... C_right ...)
   (where (C_left ...) (split-∧ C_l))
   (where (C_right ...) (split-∧ C_r))]
  [(split-∧ C) (C)])