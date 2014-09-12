#lang racket

(provide aa-prog)

(require (for-syntax racket/list redex/reduction-semantics "aa-redex-sugar.rkt" "aa-redex-core.rkt" "aa-redex-smt.rkt" "aa-redex-proo.rkt"))

(define src (make-parameter "AA"))

(define-syntax (aa-prog stx)
  (syntax-case stx ()
    [(_ (defs ...)) 
     #;(begin (displayln (syntax->datum stx))
              (displayln ""))
     (let* ([udefs (unpack #'(defs ...))]
            [typedefs (cons '(define-type binder Atom) (cons '(define-type reference RefAtom) (filter (starts-with? 'define-type) udefs)))]
            [fundefs (filter (starts-with? 'define-fun) udefs)]
            [tdecls typedefs #;(map syntax->datum typedefs)]
            [fdecls fundefs #;(map syntax->datum fundefs)]
            [dfuns (map (compile-fun fdecls tdecls) #;(lambda (f) (term (desugar-function ,f ,fdecls ,tdecls))) fdecls)]
            [desugared-funs (map car dfuns)]
            #;[obls (parameterize ((fn-defs desugared-funs)) (foldr append '() (map (lambda (fd) (term (obls-of-fd ,fd))) desugared-funs)))]
            [failed-obls (parameterize ((fn-defs desugared-funs)) (check-program dfuns))]);(parameterize ((fn-defs desugared-funs)) (term (check-obls ,obls)))])
       #`(begin 
           ;(for-each displayln (car (quote #, (map cadr dfuns))))
           (void) #;(displayln (quote #,failed-obls))))]))

(define-for-syntax ((compile-fun fdecls tdecls) f)
  (log (format "Compiling function ~a..." (first (second f))))
  (let-values ([(dsf total real gc) (time-apply (lambda () (term (desugar-function ,f ,fdecls ,tdecls))) '())])
    (logln (format "done in ~ams (~ams real, ~ams GC)" total real gc))
    (first dsf)))

(define-for-syntax (unpack stx)
  (if (syntax? stx)
      (if (syntax-line stx)
          stx
          (if (syntax->list stx)
              (map unpack (syntax->list stx))
              (syntax->datum stx)))
      stx))


#;(define-syntax (aa-prog stx)
    (syntax-case stx ()
      [(_ (defs ...)) 
       (let* ([typedefs (cons (datum->syntax #f '(define-type binder Atom) '(define-type ref RefAtom)) (filter (starts-with? 'define-type) (syntax->list #'(defs ...))))]
              [fundefs (filter (starts-with? 'define-fun) (syntax->list #'(defs ...)))]
              [tdecls typedefs #;(map syntax->datum typedefs)]
              [fdecls fundefs #;(map syntax->datum fundefs)]
              [desugared-funs (map (lambda (f) (car (term (desugar-function ,f ,fdecls ,tdecls)))) fdecls)]
              [obls (parameterize ((fn-defs desugared-funs)) (foldr append '() (map (lambda (fd) (term (obls-of-fd ,fd))) desugared-funs)))]
              [failed-obls (parameterize ((fn-defs desugared-funs)) (term (check-obls ,obls)))])
         #`(begin (displayln (quote #,failed-obls))))]))


(define-for-syntax ((starts-with? sym) stx)
  (equal? (car stx) sym))

