#lang racket

(require parser-tools/lex)
(require parser-tools/yacc)
(require syntax/readerr)

(provide read read-syntax get-info #%module-begin)

(define-tokens aa-tokens (absurd invalid comment type fun id down up opar cpar end if match fresh open split is where let arrow darrow colon returns with in atom eof and emptyset fa fx fr fb subset eq neq setdiff union dsj intersect true then else comma let/infer shadow dsj-union number))

(define-lex-abbrev aa-id (concatenation alphabetic (repetition 0 +inf.0 (union alphabetic numeric "-" "_" "+" "/" "!" "?"))))

(define aa-lexer
  (lexer-src-pos
   [(concatenation ";" (repetition 0 +inf.0 (char-complement "\n"))) (token-comment lexeme)]
   [(union whitespace) 'ws]
   [(eof) (token-eof 'eof)]
   ["type" (token-type lexeme)]
   ["fun" (token-fun lexeme)]
   ["(" (token-opar lexeme)]
   [")" (token-cpar lexeme)]
   ["is" (token-is lexeme)]
   ["returns" (token-returns lexeme)]
   [":" (token-colon lexeme)]
   ["|" (token-split lexeme)]
   ["if" (token-if lexeme)]
   ["match" (token-match lexeme)]
   ["with" (token-with lexeme)]
   ["->" (token-arrow lexeme)]
   ["=>" (token-darrow lexeme)]
   ["where" (token-where lexeme)]
   ["end." (token-end lexeme)]
   [(union "↓" "<") (token-down lexeme)]
   [(union "↑" ">") (token-up lexeme)]
   ["fresh" (token-fresh lexeme)]
   ["in" (token-in lexeme)]
   ["open" (token-open lexeme)]
   ["let" (token-let lexeme)]
   #;["atom" (token-atom lexeme)]
   ["true" (token-true lexeme)]
   ["then" (token-then lexeme)]
   ["else" (token-else lexeme)]
   ["," (token-comma lexeme)]
   ["ilet" (token-let/infer lexeme)]
   ["absurd" (token-absurd lexeme)]
   [(union "&&" "∧") (token-and lexeme)]
   ["@" (token-shadow lexeme)]
   [(union "⊎" "#+") (token-dsj-union lexeme)]
   [(repetition 1 +inf.0 numeric) (token-number (string->number lexeme))]
   [(union "0" "∅" "()") (token-emptyset lexeme)]
   [(concatenation (union "fx" "ℱx") " " (union aa-id "·")) (token-fx (get-f-var-name lexeme))]
   [(concatenation (union "fr" "ℱr") " " (union aa-id "·")) (token-fr (get-f-var-name lexeme))]
   [(concatenation (union "fb" "ℱb") " " (union aa-id "·")) (token-fb (get-f-var-name lexeme))]
   [(concatenation (union "fa" "f" "ℱa" "ℱ") " " (union aa-id "·")) (token-fa (get-f-var-name lexeme))]
   [(union "+" "∪") (token-union lexeme)]
   [(union "&" "∩") (token-intersect lexeme)]
   [(union "\\" "∖") (token-setdiff lexeme)]
   ["=" (token-eq lexeme)]
   [(union "!=" "≠") (token-neq lexeme)]
   [(union "#") (token-dsj lexeme)]
   [(union "<=" "⊆") (token-subset lexeme)]
   [aa-id (token-id lexeme)]
   [any-char (token-invalid lexeme)]))

(define (get-f-var-name lex)
  (string->symbol (string-trim (first (regexp-match #px"\\s+(.*)" lex)))))

(define (aa-read in [so-far empty])
  (let ([next (aa-lexer in)])
    (if (equal? next 'eof)
        (reverse so-far)
        (aa-read in (if (equal? next 'ws) so-far (cons next so-far))))))

(define ((aa-parser-error src) tok-ok? tok-name tok-value start-pos end-pos)
  (if tok-ok?
      (raise-read-error (format "parsing error at ~a (identified as ~a-token)" tok-value tok-name)
                        src (position-line start-pos) (position-col start-pos) (position-offset start-pos)
                        (- (position-offset end-pos) (position-offset start-pos)))
      (raise-read-error (format "bad syntax, found ~a-token: ~a" tok-name tok-value)
                        src (position-line start-pos) (position-col start-pos) (position-offset start-pos)
                        (- (position-offset end-pos) (position-offset start-pos)))))

(define (make-gen port [comments? #f])
  (letrec ([gen
            (lambda () (let ([next (aa-lexer port)])
                         (if (or (equal? (position-token-token next) 'ws) (and (not comments?) (equal? (token-name (position-token-token next)) 'comment)))
                             (gen)
                             next)))])
    gen))

(define (mk-src-pos src start end)
  (list src (position-line start) 
        (position-col start) 
        (position-offset start) 
        (- (position-offset end) (position-offset start))))

(define (mk-syntax v src start end [mk-datum #t])
  (if mk-datum
      v
      (list v (datum->syntax #f #;'a v (mk-src-pos src start end)))))

(define (replace-with-dot sym constraint)
  (match constraint #;(syntax->list constraint)
    [(list op arg1 arg2) (list op (replace-with-dot sym arg1) (replace-with-dot sym arg2))]
    [(list (list op arg1 arg2) stx) (list (list op (replace-with-dot sym arg1) (replace-with-dot sym arg2)) stx)]
    [(list f arg) (if (equal? arg sym #;(syntax->datum arg) #;(syntax->datum sym)) 
                      (list f '·)
                      (list f arg))]
    [t t]))

(define (aa-parser src)
  (parser
   (tokens aa-tokens)
   (src-pos)
   (start prog)
   (end eof)
   (error (aa-parser-error src))
   (precs (left and)
          (left setdiff)
          (left intersect)
          (left union)
          (left shadow)
          (left dsj-union))
   (grammar
    (prog ((decl) (list $1))
          ((decl prog) (cons $1 $2)))
    (decl ((fun-decl) $1)
          ((type-decl) $1))
    (ident-option ((id) $1)
                  ((type) $1)
                  ((fun) $1)
                  ((is) $1)
                  ((returns) $1)
                  #;((match) $1)
                  #;((with) $1))
    (ident ((ident-option) (mk-syntax (string->symbol $1) src $1-start-pos $1-end-pos)))
    (var ((ident) (mk-syntax $1 src $1-start-pos $1-end-pos #f)))
    (fun-decl ((fun var opar arg-decls cpar returns ident is expr end)
               (mk-syntax (list 'define-fun $2 $4 (mk-syntax 'true src $2-start-pos $2-end-pos #f) $7 (mk-syntax 'true src $2-start-pos $2-end-pos #f) $9) src $1-start-pos $10-end-pos))
              ((fun var opar arg-decls cpar returns ident where constraint arrow constraint is expr end)
               (mk-syntax (list 'define-fun $2 $4 $9 $7 $11 $13) src $1-start-pos $14-end-pos))
              ((fun var opar arg-decls cpar returns ident colon ident where constraint arrow constraint is expr end)
               (mk-syntax (list 'define-fun $2 $4 $11 $9 (replace-with-dot $7 $13) $15) src $1-start-pos $14-end-pos)))
    (arg-decls (() empty)
               ((arg-decls/ne) $1))
    (arg-decls/ne ((var colon ident) (list (mk-syntax (list $1 $3) src $1-start-pos $3-end-pos)))
                  ((var colon ident arg-decls/ne) (cons (mk-syntax (list $1 $3) src $1-start-pos $3-end-pos) $4))
                  ((var colon ident comma arg-decls/ne) (cons (mk-syntax (list $1 $3) src $1-start-pos $3-end-pos) $5)))
    (constraint ((true) (mk-syntax 'true src $1-start-pos $1-end-pos #f))
                ((opar constraint cpar) $2)
                ((constraint and constraint) (mk-syntax `(∧ ,$1 ,$3) src $1-start-pos $3-end-pos))
                ((set subset set) (mk-syntax `(⊆ ,$1 ,$3) src $1-start-pos $3-end-pos #f))
                ((set eq set) (mk-syntax `(= ,$1 ,$3) src $1-start-pos $3-end-pos #f))
                ((set neq set) (mk-syntax `(≠ ,$1 ,$3) src $1-start-pos $3-end-pos #f))
                ((set dsj set) (mk-syntax `(dsj ,$1 ,$3) src $1-start-pos $3-end-pos #f)))
    (set ((emptyset) (mk-syntax `∅ src $1-start-pos $1-end-pos))
         ((fa) (mk-syntax `(ℱ ,$1) src $1-start-pos $1-end-pos))
         ((fx) (mk-syntax `(ℱx ,$1) src $1-start-pos $1-end-pos))
         ((fr) (mk-syntax `(ℱr ,$1) src $1-start-pos $1-end-pos))
         ((fb) (mk-syntax `(ℱb ,$1) src $1-start-pos $1-end-pos))
         ((opar set cpar) $2)
         ((set union set) (mk-syntax `(∪ ,$1 ,$3) src $1-start-pos $3-end-pos))
         ((set intersect set) (mk-syntax `(∩ ,$1 ,$3) src $1-start-pos $3-end-pos))
         ((set setdiff set) (mk-syntax `(∖ ,$1 ,$3) src $1-start-pos $3-end-pos)))
    (arg-expr ((var) $1)
              ((ident opar arg-exprs cpar) (mk-syntax (cons $1 $3) src $1-start-pos $4-end-pos #f))
              ((ident emptyset) (mk-syntax (list $1) src $1-start-pos $2-end-pos #f)))
    (expr ((arg-expr) $1)
          ((absurd) (mk-syntax 'absurd src $1-start-pos $1-end-pos))
          ((fresh vars in expr) (mk-syntax (append '(fresh) $2 (list $4)) src $1-start-pos $4-end-pos))
          ((if arg-expr eq arg-expr then expr else expr) (mk-syntax `(ifeq ,$2 ,$4 ,$6 ,$8) src $1-start-pos $8-end-pos))
          ((let let-exprs in expr) (mk-syntax (cons 'let (append $2 (list $4))) src $1-start-pos $4-end-pos))
          ((let/infer let-infer-exprs in expr) (mk-syntax (cons 'let/infer (append $2 (list $4))) src $1-start-pos $4-end-pos))
          ((match arg-expr with match-cases end) (mk-syntax (cons 'match (cons $2 $4)) src $1-start-pos $5-end-pos))
          ((open arg-expr open-expr in expr) (mk-syntax (list 'open $2 $3 $5) src $1-start-pos $5-end-pos)))
    (let-exprs ((var eq expr where constraint) (list (mk-syntax (list $1 $3 $5) src $1-start-pos $5-end-pos)))
               ((var eq expr where constraint comma let-exprs) (cons (mk-syntax (list $1 $3 $5) src $1-start-pos $5-end-pos) $7)))
    (let-infer-exprs ((var eq arg-expr) (list (mk-syntax (list $1 $3) src $1-start-pos $3-end-pos)))
                     ((var eq arg-expr comma let-infer-exprs) (cons (mk-syntax (list $1 $3) src $1-start-pos $3-end-pos) $5)))
    (match-cases (() empty)
                 ((split match-case match-cases) (cons $2 $3)))
    (match-case ((open-expr darrow expr) (mk-syntax (list $1 $3) src $1-start-pos $3-end-pos)))
    (open-expr ((ident vars) (mk-syntax (cons $1 $2) src $1-start-pos $2-end-pos))
               ((ident opar vars cpar) (mk-syntax (cons $1 $2) src $1-start-pos $4-end-pos)))
    (arg-exprs (() empty)
               ((arg-exprs/ne) $1))
    (arg-exprs/ne ((arg-expr) (list $1))
                  ((arg-expr arg-exprs/ne) (cons $1 $2))
                  ((arg-expr comma arg-exprs/ne) (cons $1 $3)))
    (idents (() empty)
            ((ident idents) (cons $1 $2)))
    (vars (() empty)
          ((var vars) (cons $1 $2)))
    (type-decl ((type ident is type-cases end) (mk-syntax `(define-type ,$2 ,(cons 'union $4)) src $1-start-pos $5-end-pos)))
    (type-cases (() empty)
                ((split ident fields type-cases) (cons (mk-syntax (cons $2 (append $3 '(()))) src $1-start-pos $3-end-pos) $4))
                ((split ident fields up bindspec type-cases) (cons (mk-syntax (cons $2 (append $3 (list $5))) src $1-start-pos $5-end-pos) $6)))
    (fields (() empty)
            ((ident down bindspec fields) (cons (mk-syntax (list $1 $3) src $1-start-pos $3-end-pos) $4))
            ((ident fields) (cons (mk-syntax (list $1 '()) src $1-start-pos $1-end-pos) $2)))
    (bindspec ((number) (mk-syntax $1 src $1-start-pos $1-end-pos))
              ((bindspec shadow bindspec) (mk-syntax (list '@ $1 $3) src $1-start-pos $3-end-pos))
              ((bindspec dsj-union bindspec) (mk-syntax (list 'U $1 $3) src $1-start-pos $3-end-pos))))))

(define (read in)
  (syntax->datum (read-syntax #f in)))

(define (read-syntax src in)
  (datum->syntax #f `(module anything racket (require alpha-agnostic/aa-checker) (aa-prog ,((aa-parser src) (make-gen in))))))


(define (get-info in mod line col pos)
  (lambda (key default)
    (case key
      [(color-lexer)
       (lambda (in) 
         (let* ([token ((make-gen in #t))]
                [start (position-offset (position-token-start-pos token))]
                [end (position-offset (position-token-end-pos token))]
                [tok (position-token-token token)]
                [tn (token-name tok)])
           (cond
             [(equal? tn 'eof) (values #f 'eof #f #f #f)]
             [(member tn '(opar)) (values tok 'parenthesis '|(| start end)]
             [(member tn '(cpar)) (values tok 'parenthesis '|)| start end)]
             [(member tn '(number)) (values tok 'constant #f start end)]
             [(member tn '(comment)) (values tok 'comment #f start end)]
             [(member tn '(error)) (values tok 'error #f start end)]
             [else (values tok 'keyword #f start end)])))]
      [else default])))
