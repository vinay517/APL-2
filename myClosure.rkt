

;vinay mohan behara(U00851261) and Swapnika Pasunuri(U00843540)




#lang eopl

;; Last modified by t.k.prasad@wright.edu on 9/29/2014

;;;;;;;;;;;;;;;; top level and tests ;;;;;;;;;;;;;;;;

(define run
  (lambda (string)
    (eval-program (scan&parse string))))

;; needed for testing
(define equal-external-reps? equal?)

;;;;;;;;;;;;;;;; grammatical specification ;;;;;;;;;;;;;;;;

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
      (letter (arbno (or letter digit "_" "-" "?")))
      symbol)
    (integer (digit (arbno digit)) number)))

(define the-grammar
  '((program (expression) a-program)
    (expression (integer) lit-exp)
    (expression (identifier) var-exp)   
    (expression
      (primitive "(" (separated-list expression ",") ")")
      primapp-exp)
    (expression
      ("if" expression "then" expression "else" expression)
      if-exp)
    (expression
      ("let" (arbno  identifier "=" expression) "in" expression)
      let-exp)
    (expression
      ("proc" "(" (separated-list identifier ",") ")" expression)
      proc-exp)
    (expression
      ("(" expression (arbno expression) ")")
      app-exp)
    (expression
      (
       "begin"
       expression (arbno ";" expression)
       "end"
       )
      begin-exp)

    (primitive ("+")     add-prim)
    (primitive ("-")     subtract-prim)
    (primitive ("*")     mult-prim)
    (primitive ("add1")  incr-prim)
    (primitive ("sub1")  decr-prim)
    (primitive ("zero?") zero-test-prim)
    
    ))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;

(define eval-program 
  (lambda (pgm)
    (cases program pgm
      (a-program (body)
        (eval-expression body (init-env))))))


(define eval-expression 
  (lambda (exp env)
    (cases expression exp
      (lit-exp (datum) datum)
      (var-exp (id) (apply-env env id))
      (primapp-exp (prim rands)
        (let ((args (eval-rands rands env)))
          (apply-primitive prim args)))
      (if-exp (test-exp true-exp false-exp) ;\new4
        (if (true-value? (eval-expression test-exp env))
          (eval-expression true-exp env)
          (eval-expression false-exp env))) 
      (let-exp (ids rands body)  ;\new3
        (let ((args (eval-rands rands env)))
          (eval-expression body (extend-env ids args env))))
      (proc-exp (ids body) (closure ids body env)) ;\new1
      (app-exp (rator rands) ;\new7
        (let ((proc (eval-expression rator env))
              (args (eval-rands rands env)))
          (if
           (procedure? proc)
            (proc args)
            (eopl:error 'eval-expression
              "Attempt to apply non-procedure ~s" proc)
            )
          )
        )      
      (else (eopl:error 'eval-expression "Not here:~s" exp))
      )))

;;;; Right now a prefix must appear earlier in the file.

(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-rand x env)) rands)))

(define eval-rand
  (lambda (rand env)
    (eval-expression rand env)))

(define apply-primitive
  (lambda (prim args)
    (cases primitive prim
      (add-prim  () (+ (car args) (cadr args)))
      (subtract-prim () (- (car args) (cadr args)))
      (mult-prim  () (* (car args) (cadr args)))
      (incr-prim  () (+ (car args) 1))
      (decr-prim  () (- (car args) 1))      
      (zero-test-prim () (if (zero? (car args)) 1 0))
      )))

(define init-env 
  (lambda ()
    (extend-env
      '(i v x)
      '(1 5 10)
      (empty-env))))

;;;;;;;;;;;;;;;; booleans ;;;;;;;;;;;;;;;;

(define true-value?
  (lambda (x)
    (not (zero? x))))

;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;

(define-datatype procval procval?
  (closurerac 
    (ids (list-of symbol?)) 
    (body expression?)
    (env environment?)))
;Uses closurerac to to provide values for new closure definition
(define apply-procval
  (lambda (proc args)
    (cases procval proc
      (closurerac (values body env)
        (eval-expression body (extend-env values args env))))))
;Closure definition
(define closure
  (lambda (value body env)
    (let ((freevars (difference (free-vars body) value)))
       (let ((saved-env
                    (extend-env  
                          freevars 
                          (map  (lambda (s) (apply-env env s)) freevars)
                          (empty-env))))
          (lambda (args)
                   (eval-expression body (extend-env value args saved-env))
            )))))

;;;;;;;;;;;;;;;; environments ;;;;;;;;;;;;;;;;

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
    (syms (list-of symbol?))
    (vec vector?)              ; can use this for anything.
    (env environment?))
  )

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms (list->vector vals) env)))

(define apply-env
  (lambda (env sym)
    (cases environment env
      (empty-env-record ()
        (eopl:error 'apply-env "No binding for ~s" sym))
      (extended-env-record (syms vals env)
        (let ((position (rib-find-position sym syms)))
          (if (number? position)
              (vector-ref vals position)
              (apply-env env sym)))))))

(define rib-find-position 
  (lambda (sym los)
    (list-find-position sym los)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (sym1) (eqv? sym1 sym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
      ((null? ls) #f)
      ((pred (car ls)) 0)
      (else (let ((list-index-r (list-index pred (cdr ls))))
              (if (number? list-index-r)
                (+ list-index-r 1)
                #f))))))

(define iota
  (lambda (end)
    (let loop ((next 0))
      (if (>= next end) '()
        (cons next (loop (+ 1 next)))))))
; Find 
(define difference
  (lambda (set1 set2)
    (cond
      ((null? set1) '())
      ((memv (car set1) set2)
       (difference (cdr set1) set2))
      (else (cons (car set1) (difference (cdr set1) set2))))))


; Defining free-vars

(define free-vars                                                               
    (lambda (expressions)
      (let ((concat (lambda (x) (apply append x))))
       (cases expression expressions                                                        
       (lit-exp (datum) (list))                                                  
       (primapp-exp (primitives rands)                                                
                   (concat((lambda (x) (map free-vars x)) rands)))                                                  
       (var-exp (ids) (list ids))                                                  
       (if-exp                                                                   
                  (test-of-exp true-of-exp false-of-exp)                                     
                  (concat(free-vars (list test-of-exp true-of-exp false-of-exp))))                                                                 
       (let-exp (ids rands body)                                                 
                
                (concat(cons (difference body ids) ((lambda (x) (map free-vars x)) rands))))                          
       (app-exp (op-rator op-rands)                                                     
               (apply append (free-vars (cons op-rator op-rands))))
       (proc-exp (ids body)                                                      
                (difference (free-vars body) ids ))                   
       (else
       (eopl:error 'eval-expression "free-vars not available" exp)
       )
     )
    )
      )
  )

;----------------------------------TEST CASES------------------------------------------------

(run "10")
; should give 10

(run "v")
;should give 5

(run "add1(+(5,i))")
;should give 7

(run "sub1(+(5,i))")
;should give 5

(run "if 55 then let f = proc(x) *(x,v) in (f 11) else let in 110")
;should give 55

(run "let f=proc(x) +(v,x) in (f 10)")
;should give 15

(run "let f=proc(x) *(v,x) in let g=proc(x) add1(x) in (f(g 100))")
;should give 505




