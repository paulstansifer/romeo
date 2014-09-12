#lang racket
(require "../aa-redex-core.rkt")
(require "../aa-redex-type.rkt")
(require "../aa-redex-logi.rkt")
(require "../aa-redex-util.rkt")
(require "../aa-redex-proo.rkt")
(require "../smt-1.rkt")
(require redex)

(define lvar (term RefAtom))
(define labs (term (Prod ((Atom ∅) ((μ L (+ ,lvar (+ (Prod ((Atom ∅) (L 0)) ∅) (Prod ((L ∅) (L ∅)) ∅)))) 0)) ∅)))
(define lapp (term (Prod (((μ L (+ ,lvar (+ (Prod ((Atom ∅) (L 0)) ∅) (Prod ((L ∅) (L ∅)) ∅)))) ∅) ((μ L (+ ,lvar (+ (Prod ((Atom ∅) (L 0)) ∅) (Prod ((L ∅) (L ∅)) ∅)))) ∅)) ∅)))

(define lam (term (fold-τ (+ ,lvar (+ ,labs ,lapp)))))

(define lam/let (term (μ L (+ (+ ,lvar (Prod ((Atom ∅) (L 0)) ∅)) 
                              (+ (Prod ((L ∅) (L ∅)) ∅) 
                                 (Prod (((μ LA (+ (Prod () ∅)
                                                  (Prod ((Atom ∅) (L ∅) (LA ∅)) (⊎ 0 2)))) ∅)
                                        (L 0)) ∅))))))

(define labs/let (term (Prod ((Atom ∅) (,lam/let 0)) ∅)))
(define lapp/let (term (Prod ((,lam/let ∅) (,lam/let ∅)) ∅)))
(define llet (term (Prod (((μ LA (+ (Prod () ∅)
                                    (Prod ((Atom ∅) (,lam/let ∅) (LA ∅)) (⊎ 0 2)))) ∅)
                          (,lam/let 0)) ∅)))
(define letbinds (term (μ LA (+ (Prod () ∅)
                                (Prod ((Atom ∅) ((μ L (+ (+ ,lvar (Prod ((Atom ∅) (L 0)) ∅)) 
                                                             (+ (Prod ((L ∅) (L ∅)) ∅) 
                                                                (Prod ((LA ∅)
                                                                       (L 0)))))) ∅) (LA ∅)) (⊎ 0 2))))))

(define convert
  (term
   (define-fn
     convert ((e ,lam/let)) true ,lam
     (ecase e
            left (ecase left
                        var (einj0 var (+ ,labs ,lapp))
                        abs (eopen abs (abs-b abs-e)
                                   (elet ce (∧ (= (ℱr ·) (ℱr abs-e)) (= (ℱb ·) (ℱb abs-e)))
                                         (ecall convert abs-e)
                                         (einj1 ,lvar (einj0 (eprod ((abs-b ∅) (ce 0)) ∅) ,lapp)))))
            right (ecase right
                         app (eopen app (app-l app-r)
                                    (elet cl (∧ (= (ℱr ·) (ℱr app-l)) (= (ℱb ·) (ℱb app-l)))
                                          (ecall convert app-l)
                                          (elet cr (∧ (= (ℱr ·) (ℱr app-r)) (= (ℱb ·) (ℱb app-r)))
                                                (ecall convert app-r)
                                                (einj1 ,lvar (einj1 ,labs (eprod ((cl ∅) (cr ∅)) ∅))))))
                         let (eopen let (let-b let-e)
                                    (ecase let-b
                                           letl (ecall convert let-e)
                                           letr (eopen letr (x be rest)
                                                       (elet rlet (∧ (= (ℱr ·) (∪ (ℱr rest) (∖ (ℱr let-e) (ℱb rest)))) (= (ℱb ·) ∅))
                                                             (einj1 (+ ,lvar ,labs/let) (einj1 ,lapp/let (eprod ((rest ∅) (let-e 0)) ∅)))
                                                             (elet crlet (∧ (= (ℱr ·) (ℱr rlet)) (= (ℱb ·) (ℱb rlet)))
                                                                   (ecall convert rlet)
                                                                   (elet cbe (∧ (= (ℱr ·) (ℱr be)) (= (ℱb ·) (ℱb be)))
                                                                         (ecall convert be)
                                                                         (einj1 ,lvar (einj1 ,labs (eprod (((einj1 ,lvar (einj0 (eprod ((x ∅) (crlet 0)) ∅) ,lapp)) ∅) (cbe ∅)) ∅)))))))))))
     (∧ (= (ℱr ·) (ℱr e)) (= (ℱb ·) (ℱb e))))))


(define fdecls (list convert))


(define mylet-obls
  (parameterize
      ((fn-defs fdecls))
    (foldr append empty (map (lambda (fd) (term (obls-of-fd ,fd))) fdecls))))

(define failed-obls '())

(define (run)
  (set! failed-obls 
       (parameterize
      ((fn-defs fdecls))
    (term (check-obls ,mylet-obls))))
  (display "Failed to prove the following number of proof obligations: ")
  (displayln (foldr + 0 (map length failed-obls))))