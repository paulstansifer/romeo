#lang racket
(require "../aa-redex-core.rkt")
(require "../aa-redex-type.rkt")
(require "../aa-redex-logi.rkt")
(require "../aa-redex-util.rkt")
(require "../aa-redex-proo.rkt")
(require "../aa-redex-sugar2.rkt")
(require "../smt-1.rkt")
(require redex)

(define tatom (term (define-type atom Atom)))

(define texpr/let (term (define-type expr/let 
                      (union (App/Let (expr/let ()) (expr/let ()) ())
                             (Lam/Let (atom ()) (expr/let 0) ())
                             (Var/Let (atom ()) ())
                             (Let (let-clauses ()) (expr/let 0) ())))))

(define tlet-clauses (term (define-type let-clauses
                             (union (LCNone ())
                                    (LCBind (atom ()) (expr/let ()) (let-clauses ()) (U 0 2))))))

(define texpr (term (define-type expr
                      (union (App (expr ()) (expr ()) ())
                             (Lam (atom ()) (expr 0) ())
                             (Var (atom ()) ())))))
                     
(define tdecls (list tatom texpr/let tlet-clauses texpr))

(test-equal (andmap (lambda (t) (redex-match? aa-sugar type-decl t)) tdecls) #t)

(define convert
  (term
   (define-fun
     convert ((e expr/let)) true expr (∧ (= (ℱr ·) (ℱr e)) (= (ℱb ·) (ℱb e)))
     (match e
       ((App/Let e1 e2) (App (convert e1) (convert e2)))
       ((Lam/Let x e1) (Lam x (convert e1)))
       ((Var/Let x) (Var x))
       ((Let lc e1) (convert/let e1 lc))))))

(define convert/let
  (term
   (define-fun convert/let ((e expr/let) (lc let-clauses)) true expr (= (ℱr ·) (∪ (∖ (ℱr e) (ℱb lc)) (ℱr lc)))
     (match lc
       ((LCNone) (convert e))
       ((LCBind x be rest) (fresh y (App (Lam y (convert/let (rename x y e) rest)) (convert be))))))))

(define rename
  (term
   (define-fun rename ((x atom) (y atom) (e expr/let)) 
     (dsj (ℱ y) (∪ (ℱ e) (ℱ x)))
     expr/let 
     (∧ (= (∖ (ℱr ·) (ℱb y)) (∖ (ℱr e) (ℱb x))) (= (ℱb ·) (ℱb e)))
     (match e
       ((App/Let e1 e2) (App/Let (rename x y e1) (rename x y e2)))
       ((Lam/Let z e1) (rename/lam x y z e1))
       ((Var/Let z) (rename/var x y z))
       ((Let lc e1) (rename/let x y lc (LCNone) e1))))))

(define rename/lam
  (term
   (define-fun rename/lam ((x atom) (y atom) (z atom) (e expr/let))
     (dsj (ℱ y) (∪ (ℱ e) (∪ (ℱ x) (ℱ z))))
     expr/let
     (∧ (= (∖ (ℱr ·) (∪ (ℱb y) (ℱb z))) (∖ (ℱr e) (∪ (ℱb x) (ℱb z)))) (dsj (ℱ ·) (∪ (ℱ z) (ℱ x))))
     (ifeq x z
           (Lam/Let z e)
           (Lam/Let z (rename x y e))))))

(define rename/var
  (term
   (define-fun rename/var ((x atom) (y atom) (z atom))
     (dsj (ℱ y) (∪ (ℱ x) (ℱ z)))
     expr/let
     (∧ (= (∖ (ℱr ·) (ℱb y)) (∖ (ℱr z) (ℱb x))) (dsj (ℱ ·) (ℱ x)))
     (ifeq x z
           (Var/Let y)
           (Var/Let z)))))

(define rename/let
  (term
   (define-fun rename/let ((x atom) (y atom) (lc let-clauses) (lc-acc let-clauses) (e expr/let)) 
     (dsj (ℱ y) (∪ (ℱ lc) (∪ (ℱ e) (ℱ x))))
     expr/let 
     (∧ (= (∖ (ℱr ·) (ℱb y))
           (∪ (∪ (∖ (ℱr lc) (ℱb x)) 
                 (∖ (ℱr lc-acc) (ℱb y))) 
              (∖ (ℱr e) 
                 (∪ (∪ (ℱb lc) (ℱb lc-acc)) (ℱb x))))) (= (ℱb ·) (ℱb e)))
     (match lc
       ((LCNone) (Let lc-acc (rename x y e)))
       ((LCBind z be rest) (ifeq x z
                                 (rename/let/nonrec x y rest (LCBind z (rename x y be) lc-acc) e)
                                 (rename/let x y rest (LCBind z (rename x y be) lc-acc) e)))))))

(define rename/let/nonrec
  (term
   (define-fun rename/let/nonrec ((x atom) (y atom) (lc let-clauses) (lc-acc let-clauses) (e expr/let)) 
     (dsj (ℱ y) (∪ (ℱ lc) (∪ (ℱ e) (ℱ x))))
     expr/let
     (∧ (= (∖ (ℱr ·) (ℱb y)) (∪ (∪ (∖ (ℱr lc) (ℱb x)) (∖ (ℱr lc-acc) (ℱb y))) (∖ (ℱr e) (∪ (ℱb lc) (ℱb lc-acc))))) (= (ℱb ·) (ℱb e)))
     (match lc
       ((LCNone) (Let lc-acc e))
       ((LCBind z be rest) (rename/let/nonrec x y rest (LCBind z (rename x y be) lc-acc) e))))))
                              

(define fdecls (list convert convert/let rename rename/let rename/let/nonrec rename/var rename/lam))

(test-equal (andmap (lambda (f) (redex-match? aa-sugar fun-decl f)) fdecls) #t)

(define desugared-funs (map (lambda (f) (term (desugar-function ,f ,fdecls ,tdecls))) fdecls))

(define mylet-obls
  (parameterize
      ((fn-defs desugared-funs))
    (foldr append empty (map (lambda (fd) (term (obls-of-fd ,fd))) desugared-funs))))

(define failed-obls '())

(define (run)
  (set! failed-obls 
        (parameterize
      ((fn-defs desugared-funs))
    (term (check-obls ,mylet-obls))))
  (display "Failed to prove the following number of proof obligations: ")
  (displayln (foldr + 0 (map length failed-obls))))