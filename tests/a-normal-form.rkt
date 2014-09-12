#lang racket

(require "../aa-redex-sugar.rkt")
(require "../aa-redex-core.rkt")
(require "../aa-redex-type.rkt")
(require "../aa-redex-proo.rkt")
(require "../smt-1.rkt")
(require redex)

(define tatom (term (define-type atom Atom)))
(define tterm 
  (term 
   (define-type term
     (union (Var (atom ()) ())
            (Lambda (atom ()) (term 0) ())
            (App (term ()) (term ()) ())
            (Let (atom ()) (term ()) (term 0) ())
            (If (term ()) (term ()) (term ()) ())))))

(define tcontext
  (term
   (define-type context
     (union (CEmpty ())
            (CLet (atom ()) (term ()) (context 0) (@ 0))
            (CCompose (context ()) (context 0) (@ 0 1))))))

(define tclosure
  (term
   (define-type closure
     (Clo (context ()) (term 0) ()))))

(define tbool
  (term
   (define-type bool
     (union
     (True ())
     (False ())))))

(define tdecls (list tatom tterm tcontext tclosure tbool))

(test-equal (andmap (lambda (t) (redex-match? aa-sugar type-decl t)) tdecls) #t)

(define ffill
  (term
   (define-fun fill ((clo closure)) true term (= (ℱr ·) (ℱr clo))
     (open clo (Clo c t)
           (match c
             ((CEmpty) t)
             ((CLet x t1 c2) (Let x t1 (fill (Clo c2 t))))
             ((CCompose c1 c2) (fill (Clo c1 (fill (Clo c2 t))))))))))

(define fnorm
  (term
   (define-fun norm ((t term)) true term (= (ℱr ·) (ℱr t))
     (fill (split t (False))))))

(define fsplit
  (term
   (define-fun split ((t term) (mode bool)) true closure (= (ℱr ·) (ℱr t))
     (match t
       ((Var x) (Clo (CEmpty) t))
       ((Lambda x tt) (Clo (CEmpty) (Lambda x (norm tt))))
       ((App t1 t2) (open (split t1 (True)) (Clo c1 u1) 
                          (open (split t2 (True)) (Clo c2 u2)
                                (valueify (Clo (CCompose c1 c2) (App u1 u2)) mode))))
       ((Let x t1 t2) (open (split t1 (False)) (Clo c1 u1)
                          (open (split t2 mode) (Clo c2 u2)
                                (Clo (CCompose c1 (CLet x u1 c2)) u2))))
       ((If t1 t2 t3) (open (split t1 (True)) (Clo c1 u1)
                            (valueify (Clo c1 (If u1 (norm t2) (norm t3))) mode)))))))

(define fvalueify
  (term
   (define-fun valueify ((clo closure) (mode bool)) true closure (= (ℱr ·) (ℱr clo))
     (match mode
       ((True) (open clo (Clo c t)
                     (fresh x (Clo (CCompose c (CLet x t (CEmpty))) (Var x)))))
       ((False) clo)))))

(define fdecls (list ffill fnorm fsplit fvalueify))

(test-equal (andmap (lambda (f) (redex-match? aa-sugar fun-decl f)) fdecls) #t)

(define desugared-funs (map (lambda (f) (term (desugar-function ,f ,fdecls ,tdecls))) fdecls))

(define anf-obls
  (parameterize
      ((fn-defs desugared-funs))
    (foldr append empty (map (lambda (fd) (term (obls-of-fd ,fd))) desugared-funs))))

(define failed-obls '())

(define (run)
  (set! failed-obls 
        (parameterize
      ((fn-defs desugared-funs))
    (term (check-obls ,anf-obls))))
  (display "Failed to prove the following number of proof obligations: ")
  (displayln (foldr + 0 (map length failed-obls))))