#lang racket

(require "aa-redex-core.rkt")
(require "aa-redex-type.rkt")
(require "aa-redex-logi.rkt")
(require "aa-redex-util.rkt")
(require "aa-redex-proo.rkt")
(require "aa-redex-sugar.rkt")
(require "aa-redex-smtc.rkt")

(require redex/reduction-semantics)
(provide check-program log logln)

;; Command line command to start Z3 such that it accepts input on stdin
(define Z3-COMMAND (make-parameter "z3 /in /smt2"))

;; If true, accepts failing preconditions, else throws exception
(define Z3-ACCEPT-ABSURD (make-parameter false))

;; Initial definitions needed for Z3
(define Z3-DEFS
  (list
   "(set-option :interactive-mode true)"
   ;; Array Sort
   "(define-sort Set (T) (Array T Bool))"   
   ;; Generic Elem Sort
   "(declare-sort Elem)"
   ;; The empty set constant
   "(declare-const emptyset (Set Elem))"
   ;;Assert that the empty set is actually empty
   "(assert (forall ((e Elem)) (not (select emptyset e))))" 
   ;; Introduce the notion of disjointness
   "(define-fun disjoint ((s1 (Set Elem)) (s2 (Set Elem))) Bool
      (= (intersect s1 s2) emptyset))"
   ;; Introduce the notion of sets of size one
   "(define-fun sizeone ((s (Set Elem))) Bool
           (exists ((e1 Elem)) (forall ((e2 Elem)) (= (select s e2) (= e1 e2)))))"))

#;(define smt-setnum 0)
#;(define smt-sets empty)
#;(define smt-curbindings empty)

(define log display)
(define logln displayln)

(define (check-program dfuns)
  (smt-reset-names)
  (logln "Generating Proof Obligations")
  (let*-values ([(oblss-l prep-t prep-tr prep-tgc) (time-apply prepare-smt (list dfuns))]
                [(oblss) (begin (logln (format "Proof obligations generated in ~a ms (~ams real, ~ams GC)" prep-t prep-tr prep-tgc)) (first oblss-l))]
                [(proc) (process (Z3-COMMAND))]
                [(proc-out proc-in proc-ignore proc-err proc-control) (apply values proc)]
                [(smts) (map second oblss)]
                [(set-defs) (remove-duplicates (apply append (map first oblss)))])
    (begin
      (smt-write Z3-DEFS proc-in)
      (smt-write 
       (map (lambda (sd)
              (format "(declare-const ~a (Set Elem))" sd)) 
            set-defs) proc-in)
      (for-each (lambda (fd smtd)
                  (log (format "Checking proof obligations for function ~a..." (second (first fd))))
                  (let-values ([(r ctime creal cgc) (time-apply (lambda () (foldr (lambda (smtt b) (map + ((check-obl proc-out proc-in proc-err) smtt) b)) (list 0 0) smtd)) '())])
                    (logln (format "done in ~ams (~ams real, ~ams GC): ~a goal clauses checked" ctime creal cgc (first (first r)) #;(second (first r))))))
                dfuns smts)
      (let ([out-err empty])
        (close-output-port proc-in)
        (proc-control 'wait)
        (set! out-err (port->lines proc-err))
        (close-input-port proc-out)
        (close-input-port proc-err)
        (if (not (empty? out-err))
            (error out-err)
            (void))))))

(define (prepare-smt dfuns)
  (match dfuns
    [(list) empty]
    [(list-rest (list fd xenvs) rest)
     (log (format "Generating proof obligations for function ~a..." (second fd)))
     (let*-values ([(obll time-total time-real time-gc) (time-apply (lambda (fd) (term (obls-of-fd ,fd))) (list fd))]
                   [(obls) (first obll)])
       (logln (format "done in ~ams (~ams real, ~ams GC) - ~a proof obligations, ~a goal clauses" time-total time-real time-gc (length obls) (foldr + 0 (map length (map second xenvs)))))
       (log "Generating SMT input...")
       (if (= (length obls) (length xenvs))
           (let-values ([(smtobls smt-total smt-real smt-gc) (time-apply (lambda () (term (obls->smt ,obls ,xenvs))) '())])
             (logln (format "done in ~ams (~ams real, ~ams GC)" smt-total smt-real smt-gc))
             (append smtobls (prepare-smt rest)))
           (error (format "Error in preparing function ~a for SMT-step: number of proof obligations (~a) does not match number of prepared environments (~a)" 
                          (second fd) (length obls) (length xenvs)))))]))


#;(match dfuns
    [(list) #t]
    [(list-rest (list fd envs) rst)
     (let ([obls (term (obls-of-fd ,fd))])
       (if (= (length obls) (length envs))
           (if (check-program/obls obls envs)
               #f
               (check-program rst))
           (list (length obls) (length envs) fd)))])

#;(define ((check-program/obls proc-out proc-in proc-err) obls)
    (if (= (length obls) (length envs))
        (for-each
         (check-obl proc-out proc-in proc-err)
         obls
         envs)
        (begin
          (displayln (format "Obls: ~a | Envs: ~a" (length obls) (length envs)))
          (displayln "")
          (displayln "Obls:")
          (for-each displayln obls)
          (displayln "")
          (displayln "Envs:")
          (for-each displayln envs)
          (error "Could not match obligations and environments"))))

#;(match envs
    [(list) #f]
    [(list-rest (list env cs) rst)
     (let ([result (term (check-obls (,(first obls))))])
       (if (empty? result)
           (check-program/obls (rest obls) rst)
           (process-counterexample (fourth (caar result)) (fifth (caar result)) env)))])

;; Takes a postcondition (c), a counterexcample (ce) and variable
;; dependency/source information, and throws an appropriate syntax error
(define (process-counterexample c cd ce env)
  (match ce
    [(list (list univ ...)
           (list
            (list (list opl varl) snl msl) ...
            emptysetdef
            (list (list opr varr) snr msr) ...))
     (let* ([op (append opl opr)]
            [var (append varl varr)]
            [sn (append snl snr)]
            [ms (append msl msr)]
            [smap (map list (map list op var) ms)])
       (match c
         [(list op left right)
          (let* ([sleft (term (eval-set ,left ,smap))]
                 [sright (term (eval-set ,right ,smap))]
                 [elems (match op
                          ['= (set-diff (set-union sleft sright) (set-intersect sleft sright))]
                          ['dsj (set-intersect sleft sright)]
                          ['⊆ (set-diff sleft sright)])]
                 [lapp (map (lambda (s) (term (find-atom-source ,left ,s ,smap))) elems)]
                 [rapp (map (lambda (s) (term (find-atom-source ,right ,s ,smap))) elems)]
                 [tapp (apply append (append lapp rapp))]
                 [datagen (lambda (setss) (map (lambda (set) 
                                                 (match set 
                                                   [(list 'ℱb x) (let ([srcs (term (find-binder-sources ,x ,env))])
                                                                   (list (format "  - A free binder in ~a\n" (string-join (map (curry format "~a") (map first srcs)) ", " #:before-last ", OR ")) (map second srcs)))]
                                                   [(list 'ℱr x) (let ([srcs (term (find-ref-sources ,x ,env))])
                                                                   (list (format "  - A free reference in ~a\n"  (string-join (map (curry format "~a") (map first srcs)) ", " #:before-last ", OR ")) (map second srcs)))]))
                                               (first setss)))])
            (if (empty? tapp)
                (begin (displayln sleft)
                       (displayln lapp)
                       (displayln sright)
                       (displayln rapp)
                       (displayln left)
                       (displayln op)
                       (displayln right)
                       (displayln smap))
                '())
            (match cd
              [(list 'annot (list cc cstx)) 
               (let ([data (datagen tapp)])
                 (raise-syntax-error 'annotated-constraints (format "Could not prove that the following constraint always holds: ~a\nThere may be an atom that is:\n~aand thus free on the ~a hand side, but not on the ~a hand side" 
                                                                    cc (apply string-append (map first data)) (if (empty? lapp) "right" "left") (if (empty? lapp) "left" "right")) 
                                     cstx #f (append* (map second data))))]
              [(list 'pfresh (list v stx)) 
               (let ([data (datagen (apply append rapp))])
                 (raise-syntax-error 'fresh (format "Variable ~a may not be free in the result, but it could appear as:\n~a" v (apply string-append (map first data))) stx #f (append* (map second data))))]
              [(list 'popen (list v stx) open-decs)
               (let ([var (first (term (find-atom-source ,left ,(first elems) ,smap)))]
                     [data (datagen (apply append (term (find-atom-source ,right ,(first elems) ,smap))))])
                 (list (lambda (data) (raise-syntax-error 'match (format "Exposable atoms in ~a may not be free in the result, but ~a could be:\n~a" v var (apply string-append (map first data))) stx #f (append* (map second data))))))]
              [(list 'fcpre fd fc (list cc cstx))
               (let ([data (datagen tapp)])
                 (lambda (data) (raise-syntax-error 'annotated-constraints (format "Could not prove that the precondition of ~a is always satisfied: ~a\nThere may be an atom that is:\n~a" (syntax->datum fd) cc (apply string-append (map first data))) fc #f (cons fd (cons cstx (append* (map second data)))))))]))]))]
    [else (displayln else) (error "MATCHING ERROR")]))

(define-metafunction aa-smt
  find-binder-sources : x env -> (var ...)
  [(find-binder-sources x env)
   (var ... ...)
   (where ((x_sub any_sub) ...) (lookup-env/sources x env))
   (side-condition (> (length (term (x_sub ...))) 0))
   (where ((var ...) ...) ((find-binder-sources x_sub (modify-env x_sub (lookup-env/type x_sub env) any_sub (lookup-env/sources x_sub env) env)) ...))]
  [(find-binder-sources x env)
   ()
   (where RefAtom (lookup-env/type x env))]
  [(find-binder-sources x env)
   ((x (lookup-env/stx x env)))])

(define-metafunction aa-smt
  find-ref-sources : x env -> (var ...)
  [(find-ref-sources x env)
   (var ... ...)
   (where ((x_sub any_sub) ...) (lookup-env/sources x env))
   (side-condition (> (length (term (x_sub ...))) 0))
   (where ((var ...) ...) ((find-ref-sources x_sub (modify-env x_sub (lookup-env/type x_sub env) any_sub (lookup-env/sources x_sub env) env)) ...))]
  [(find-ref-sources x env)
   ()
   (where Atom (lookup-env/type x env))]
  [(find-ref-sources x env)
   ((x (lookup-env/stx x env)))])

#;(define-syntax (mamama stx)
    (syntax-case stx ()
      [(m v1 v ...)
       (raise-syntax-error #f "hoho" #'(m v1 v ...) #'v1 (filter (lambda (s) (not (equal? (syntax->datum s) (syntax->datum #'v1)))) (syntax->list #'(v ...))))]))

;(mamama x y x z x v x x w y)

;; Takes a set constructor and atomic set information from a counterexample and
;; returns the list of elements that are in the constructed set
(define-metafunction aa
  eval-set : s any -> (string ...)
  [(eval-set ∅ any) ()]
  [(eval-set (∪ s_l s_r) any)
   ,(set-union (term (eval-set s_l any)) (term (eval-set s_r any)))]
  [(eval-set (∩ s_l s_r) any)
   ,(set-intersect (term (eval-set s_l any)) (term (eval-set s_r any)))]
  [(eval-set (∖ s_l s_r) any)
   ,(set-diff (term (eval-set s_l any)) (term (eval-set s_r any)))]
  [(eval-set any (any_l ... (any (string ...)) any_r ...))
   (string ...)]
  [(eval-set any (any_x ...))
   ()])

(define (set-union s1 s2)
  (remove-duplicates (append s1 s2)))

(define (set-intersect s1 s2)
  (remove-duplicates (filter (lambda (x) (member x s2)) s1)))

(define (set-diff s1 s2)
  (remove-duplicates (filter (lambda (x) (not (member x s2))) s1)))

;; Takes a set constructor, an element and atomic set information from a counterexample
;; and returns possible sources for the given element in the set described by the constructor 
(define-metafunction aa
  find-atom-source : s string any -> ((s ...) ...)
  [(find-atom-source ∅ string any) ()]
  [(find-atom-source (∪ s_l s_r) string any)
   ,(set-union (term (find-atom-source s_l string any)) (term (find-atom-source s_r string any)))]
  [(find-atom-source (∩ s_l s_r) string any)
   ,(if (or (empty? (term any_l)) (empty? (term any_r)))
        '()
        (apply append (map (lambda (s1) (map (lambda (s2) (set-union s1 s2)) (term any_r))) (term any_l))))
   (where any_l (find-atom-source s_l string any))
   (where any_r (find-atom-source s_r string any))]
  [(find-atom-source (∖ s_l s_r) string any)
   ,(if (empty? (term any_r))
        (term any_l)
        '())
   (where any_l (find-atom-source s_l string any))
   (where any_r (find-atom-source s_r string any))]
  [(find-atom-source s string (any_l ... (s (string_l ... string string_r ...)) any_r ...))
   ((s))]
  [(find-atom-source any string (any_x ...))
   ()])

;; -----------------------------------------------------------------------------
;; SMT-Interface

(define (display/debug arg) '())

(define (smt-write x port)
  #;(display-lines x)
  (display-lines x port))

(define ((check-obl proc-out proc-in proc-err) smt-tuple)
  (let* ([env (third smt-tuple)]
         [pre-code (term (smt->text ,(map first (first smt-tuple))))]
         #;[post-code (term (smt->text (smt->not ,(third smt-tuple))))]
         [name-map (term (set-names ,(append (map first (first smt-tuple)) (map first (second smt-tuple)))))]
         #;[result empty]
         [checked 0]
         [ignored 0])
    (smt-write (list "" "(push)" "") proc-in) 
    (smt-write pre-code proc-in)
    (smt-write (list "" "(check-sat)" "") proc-in)
    (let ([out-pre (read proc-out)])
      (if (equal? out-pre 'sat)
          (for-each
           (lambda (c)
             (display/debug "Proof obligation:")
             (display/debug (map third (first smt-tuple)))
             (display/debug "->")
             (display/debug (first c))
             (if (equal? (first (second c)) 'ignore)
                 (begin
                   (display/debug "IGNORED")
                   (set! ignored (+ ignored 1)))
                 (begin
                   (set! checked (+ checked 1))
                   (smt-write (list "" "(push)" "") proc-in)
                   (smt-write (term (smt->text (smt->not (,(first c))))) proc-in)
                   (smt-write (list "" "(check-sat)" "") proc-in)
                   (let ([out-post (read proc-out)])
                     (if (equal? out-post 'sat)
                         (begin 
                           (smt-write (list "" "(get-model)" "") proc-in)
                           (let ([model (read proc-out)])
                             (if (equal? model 'sat)
                                 (set! model (read proc-out))
                                 '())
                             (process-counterexample (third c) (second c) (process-model name-map model) env)))
                         '()))
                   (smt-write (list "" "(pop)" "") proc-in))))
           (second smt-tuple))
          (if (equal? out-pre 'unsat)
              (if (Z3-ACCEPT-ABSURD)
                  (displayln (format "Warning: Absurd part of program at ~a" 'x))
                  (begin
                    (smt-write (list "" "(pop)" "") proc-in)
                    (analyze-unsat-core (find-unsat-core proc-out proc-in proc-err (first smt-tuple) '()))))
              (if (equal? out-pre 'unknown)
                  (error "SMT Solver cannot determine satisfiability")
                  (error "SMT communication error")))))
    (smt-write (list "" "(pop)" "") proc-in)
    (list checked ignored)))

(define (find-unsat-core proc-out proc-in proc-err constraints core)
  (smt-write (list "" "(push)" "") proc-in)
  (for-each (lambda (c) (smt-write (term (smt->text (,(first c)))) proc-in))
            core)
  (smt-write (list "" "(check-sat)" "") proc-in)
  (let ([out-post (read proc-out)])
    (if (or (equal? out-post 'sat) #;(equal? out-post 'unknown))
        (letrec ([fuc (lambda (cs)
                        (if (empty? cs)
                            (begin (smt-write (list "" "(pop)" "") proc-in)
                                   (find-unsat-core proc-out proc-in proc-err constraints (cons (first (filter (lambda (c) (not (member c core))) constraints)) core)))
                            (if (member (first cs) core)
                                (fuc (rest cs))
                                (begin
                                  (smt-write (term (smt->text (,(first (first cs))))) proc-in)
                                  (smt-write (list "" "(check-sat)" "") proc-in)
                                  (let ([cout (read proc-out)])
                                    (if (or (equal? cout 'sat) #;(equal? out-post 'unknown))
                                        (fuc (rest cs))
                                        (if (equal? cout 'unsat)
                                            (begin 
                                              (smt-write (list "" "(pop)" "") proc-in)
                                              (find-unsat-core proc-out proc-in proc-err constraints (cons (first cs) core)))
                                            (error (format "SMT communication error: ~a" cout)))))))))])
          (fuc constraints))
        (if (equal? out-post 'unsat)
            (begin (smt-write (list "" "(pop)" "") proc-in) core)
            (if (equal? out-post 'unknown)
                (begin (smt-write (list "" "(get-assertions)" "") proc-in)
                       (displayln (read proc-out))
                       (error "SMT solver cannot determine satisfiability"))
                (error (format "SMT communication error: ~a" out-post)))))))

(define (analyze-unsat-core core)
  (let* ([res (map (lambda (c) (match c [(list x y z) (term (unsat-cond-data ,x ,y ,z))]))
                   core)]
         [strs (map first res)]
         [stxs (apply append (map second res))]
         [msg (string-append "The following constraints cannot be simultaneously satisfied:\n" (string-join strs "\n"))])
    (if (> (length stxs) 0)
        (raise-syntax-error 'unsatisfiable msg (first stxs) #f stxs)
        (error msg))))

(define-metafunction aa-smt
  unsat-cond-data : smt-line any C -> (string (any ...))
  [(unsat-cond-data smt-line (annot (C any)) C_exp) 
   (,(format "- Constraint: ~a" (term C)) (any))]
  [(unsat-cond-data smt-line (pfresh (x any)) C_exp) 
   (,(format "- Freshness of variable ~a" (term x)) (any))]
  [(unsat-cond-data smt-line (popen (x any) (var_b ...)) C_exp) 
   (,(format "- Opening of variable ~a" (term x)) (any))]  
  [(unsat-cond-data smt-line (fcpre any_fd any_fc (C any_c)) C_exp) 
   (,(format "- Function precondition: ~a" (term C)) (any_fd any_fc any_c))]
  [(unsat-cond-data smt-line (ignore any C) C_exp) 
   (,(format "- Inferred constraint of argument-expression ~a : ~a" (syntax->datum (term any)) (term C)) (any))]
  [(unsat-cond-data smt-line (letsub (x any)) C_exp) 
   (,(format "- Let-Result must contain only free atoms from the current environment for variable ~a" (term x)) (any))]
  [(unsat-cond-data smt-line (ifthen (x_l any_l) (x_r any_r)) C_exp) 
   (,(format "- If-Branch: ~a = ~a" (term x_l) (term x_r)) (any_l any_r))]
  [(unsat-cond-data smt-line (ifelse (x_l any_l) (x_r any_r)) C_exp) 
   (,(format "- If-Branch: ~a ≠ ~a" (term x_l) (term x_r)) (any_l any_r))]
  [(unsat-cond-data smt-line (fcpost any_fd any_fc (C any)) C_exp) 
   (,(format "- Knowledge after function call: ~a" (term C)) (any_fd any_fc any))]
  [(unsat-cond-data smt-line (fcenv any_fd any_fc) C_exp) 
   (,(format "- Knowledge after function call (free atoms in result must be subset of free atoms of arguments)") (any_fd any_fc))]
  [(unsat-cond-data smt-line (caseleft (x_c any_c) (x_b any_b)) C_exp) 
   (,(format "- Matching case: ~a" (syntax->datum (term any_c))) (any_c any_b))]
  [(unsat-cond-data smt-line (caseright (x_c any_c) (x_b any_b)) C_exp) 
   (,(format "- Matching case: ~a" (syntax->datum (term any_c))) (any_c any_b))]
  [(unsat-cond-data smt-line (qcons any) C_exp) 
   (,(format "- Constructor: ~a" (syntax->datum (term any))) (any))]
  [(unsat-cond-data smt-line setsizes C_exp) 
   (,(format "- Inferred set size: ~a" (term C_exp)) ())])