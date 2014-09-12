#lang racket
(require "../aa-redex-core.rkt")
(require "../aa-redex-type.rkt")
(require "../aa-redex-logi.rkt")
(require "../aa-redex-util.rkt")
(require "../aa-redex-proo.rkt")
(require "../smt-1.rkt")
(require redex)

(define Var (term (Prod ((Atom ∅)) ∅)))
(define Lam (term (Prod ((Atom ∅)
                         ((μ a (+ (Prod ((Atom ∅)) ∅) 
                                  (+ (Prod ((Atom ∅) (a 0)) ∅) 
                                     (Prod ((a ∅) (a ∅)) ∅))))
                          0))
                        ∅)))
(define App (term (Prod (((μ a (+ (Prod ((Atom ∅)) ∅) 
                                  (+ (Prod ((Atom ∅) (a 0)) ∅) 
                                     (Prod ((a ∅) (a ∅)) ∅))))
                          ∅)
                         ((μ a (+ (Prod ((Atom ∅)) ∅) 
                                  (+ (Prod ((Atom ∅) (a 0)) ∅) 
                                     (Prod ((a ∅) (a ∅)) ∅))))
                          ∅))
                        ∅)))
(define lam (term (fold-τ (+ ,Var (+ ,Lam ,App)))))



(define V (term (Prod ((Atom ∅)) ∅)))
(define ENil (term (Prod () ∅)))

(define inECons (term (μ e (+ ,ENil 
                              (Prod ((e ∅) 
                                     (Atom ∅)
                                     ((μ s (+ (Prod ((e ∅)
                                                     (Atom ∅)
                                                     (,lam (⊎ 0 1))) ∅)
                                              (μ n (+ ,Var
                                                      (Prod ((n ∅) (s ∅)) ∅)))))
                                      ∅))
                                    (⊎ 0 1))))))

(define ECons (term (Prod ((,inECons ∅)
                           (Atom ∅)
                           ((μ s (+ (Prod ((,inECons ∅)
                                           (Atom ∅)
                                           (,lam (⊎ 0 1))) ∅)
                                    (μ n (+ ,Var
                                            (Prod ((n ∅) (s ∅)) ∅)))))
                            ∅)) (⊎ 0 1))))
(define env (term (fold-τ (+ ,ENil ,ECons))))

(define inA (term (μ n (+ ,V (Prod ((n ∅)
                                    ((μ s (+ (Prod (((μ e (+ ,ENil
                                                             (Prod ((e ∅) (Atom ∅) (s ∅)) (⊎ 0 1)))) ∅)
                                                    (Atom ∅)
                                                    (,lam (⊎ 0 1))) ∅)
                                             
                                             n)) ∅)) ∅)))))
(define A (term (Prod ((,inA ∅)
                       ((μ s (+ (Prod (((μ e (+ ,ENil
                                                (Prod ((e ∅) (Atom ∅) (s ∅)) (⊎ 0 1)))) ∅)
                                       (Atom ∅)
                                       (,lam (⊎ 0 1))) ∅)
                                
                                ,inA)) ∅)) ∅)))
(define neu (term (fold-τ (+ ,V ,A))))

(define L (term (Prod ((,env ∅)
                       (Atom ∅)
                       (,lam (⊎ 0 1)))
                      ∅)))
(define N neu)
(define sem (term (fold-τ (+ ,L ,N))))


(define rsem (term (μ
                    s
                    (+
                     (Prod
                      (((μ e (+ (Prod () ∅) (Prod ((e ∅) (Atom ∅) (s ∅)) (⊎ 0 1)))) ∅)
                       (Atom ∅)
                       ((μ a (+ Atom (+ (Prod ((Atom ∅) (a 0)) ∅) (Prod ((a ∅) (a ∅)) ∅)))) (⊎ 0 1)))
                      ∅)
                     (μ n (+ Atom (Prod ((n ∅) (s ∅)) ∅)))))))


(define oldA (term (Prod ((n ∅) (s ∅)) ∅)))
(define oldL (term (Prod ((l ∅) (Atom ∅) (,lam (⊎ 0 1))) ∅)))
(define oldN (term (+ ,V ,A)))

(define oldECons (term (Prod ((l ∅) (Atom ∅) (s ∅)) 1)))

(define oldneu (term (μ n (μ l (μ s (+ ,V ,oldA))))))
(define oldsem (term (μ n (μ l (μ s (+ ,oldL ,oldN))))))
(define oldenv (term (μ n (μ l (μ s (+ ,ENil ,oldECons))))))

(redex-match? aa τ Lam)
(redex-match? aa τ App)
(redex-match? aa τ Var)
(redex-match? aa τ lam)
(redex-match? aa τ V)
(redex-match? aa τ A)
(redex-match? aa τ neu)
(redex-match? aa τ L)
(redex-match? aa τ N)
(redex-match? aa τ sem)
(redex-match? aa τ ENil)
(redex-match? aa τ ECons)
(redex-match? aa τ env)

(define reify 
  (term 
   (define-fn 
     reify ((s ,sem)) true ,lam 
     (ecase s
            DEBUG (eopen DEBUG (env y t)
                         (efresh x 
                                 (elet y-env (∧ (= (∪ (ℱb env) (ℱb y)) (ℱb ·))
                                                (= (∪ (ℱr env) (ℱr x)) (ℱr ·)))
                                       (einj1 ,ENil (eprod ((env ∅) (y ∅) ((einj1 ,L (einj0 (eprod ((x ∅)) ∅) ,A)) ∅)) (⊎ 0 1)))
                                       (elet evaled (⊆ (ℱ ·) (∪ (ℱr y-env) (∖ (ℱ t) (ℱb y-env)))) (ecall evals y-env t)
                                             (elet res (⊆ (ℱ ·) (ℱ evaled)) (ecall reify evaled)
                                                   (einj1 ,Var (einj0 (eprod ((x ∅) (res 0)) ∅) ,App)))))))
            N (ecall reifyn N))
     true)))

(redex-match? aa fD reify)

(define reifyn
  (term
   (define-fn
     reifyn ((n ,neu)) true ,lam
     (ecase n
            V (einj0 V (+ ,Lam ,App))
            A (eopen A (nn d)
                     (elet x1 true (ecall reifyn nn)
                           (elet x2 true (ecall reify d)
                                 (einj1 ,Var (einj1 ,Lam (eprod ((x1 ∅) (x2 ∅)) ∅)))))))
     true)))

(redex-match? aa fD reifyn)

(define evals
  (term
   (define-fn
     evals
     ((env ,env) (t ,lam)) true ,sem
     (ecase t
            Var (eopen Var (var-atom)
                       (ecase env 
                              ENil (einj1 ,L (einj0 (eprod ((var-atom ∅)) ∅) ,A))
                              ECons (eopen ECons (tail y v)
                                           (eifeq var-atom y v (ecall evals tail t)))))
            tt (ecase tt
                      Lam (eopen Lam (x tl)
                                 (einj0 (eprod ((env ∅) (x ∅) (tl (⊎ 0 1))) ∅) ,N))
                      App (eopen App (t1 t2)
                                 (elet res (⊆ (ℱ ·) (∪ (ℱr env) (∖ (ℱ t1) (ℱb env)))) (ecall evals env t1)
                                       (ecase res
                                              L (eopen L (cenv x tl)
                                                       (elet res2 (⊆ (ℱ ·) (∪ (ℱr env) (∖ (ℱ t2) (ℱb env)))) (ecall evals env t2)
                                                             (elet newenv (∧ (= (∪ (ℱb cenv) (ℱb x)) (ℱb ·))
                                                                             (= (∪ (ℱr cenv) (ℱr res2)) (ℱr ·)))
                                                                   (einj1 ,ENil (eprod ((cenv ∅) (x ∅) (res2 ∅)) (⊎ 0 1)))
                                                                   (ecall evals newenv tl))))
                                              N (elet resn (⊆ (ℱ ·) (∪ (ℱr env) (∖ (ℱ t2) (ℱb env)))) (ecall evals env t2) 
                                                      (einj1 ,L (einj1 ,V (eprod ((N ∅) (resn ∅)) ∅)))))))))
     (⊆ (ℱ ·) (∪ (ℱr env) (∖ (ℱ t) (ℱb env)))))))

(redex-match? aa fD evals)

(define eval
  (term
   (define-fn eval ((t ,lam)) true ,sem
     (elet l true (einj0 (eprod () ∅) ,ECons)
           (ecall evals l t))
     true)))

(redex-match? aa fD eval)

(define normalize
  (term
   (define-fn normalize ((t ,lam)) true ,lam
     (elet res true (ecall eval t)
           (ecall reify res))
     true)))

(redex-match? aa fD normalize)

(redex-match? aa fD (term (define-fn reify ((s Atom)) true Atom s true)))

(parameterize
    ((fn-defs `(,reify ,reifyn ,evals ,eval ,normalize)))
  (length (term (obls-of-fd ,reifyn))))
;(judgment-holds (,`ε . ⊢p . true ,program true obls) obls)

(test-equal
 (only-or-false 
  (judgment-holds ((x ,env ε)
                   . ⊢ty . 
                   (ecase x
                          ENil (einj0 ENil ,ECons)
                          ECons (einj1 ,ENil ECons))
                   τ_ty) τ_ty)) env)

(define nbe-obls
  (parameterize
      ((fn-defs `(,reify ,reifyn ,evals ,eval ,normalize)))
    (append 
     (term (obls-of-fd ,evals))
     (term (obls-of-fd ,reify))
     (term (obls-of-fd ,reifyn))
     (term (obls-of-fd ,eval))
     (term (obls-of-fd ,normalize)))))

(test-equal (only-or-false (judgment-holds ((x Atom ε) . ⊢ty . (einj0 (eprod ((x ∅)) ∅) (+ ,Lam ,App)) τ_ty) τ_ty)) lam)