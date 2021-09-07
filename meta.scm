;; Louise Thompson
;; CS220 Spring 2020
;; metacircular interpreter for a subset of scheme

(load-option 'format)

;; An environment is a list of one element.  That element is an association
;; list.  This allows us to add a binding to an environment.

(define (popl-error string)
  "Output a given error message and abort the program.  This one just calls
   scheme's error function.  TODO: We will make this better, later."
   (format #t "ERROR: ~A~%" string)
   (*LOOPTOP* 'dontcare))


(define (popl-bind symbol value env)
  "Add a binding from symbol to value in the given environment.
   Shadows any previous binding of the same symbol, perhaps permanently."
  (let ((bindings (car env)))
    (set-car! env (cons (list symbol value) bindings)))
  symbol)

(define (popl-get-binding symbol env)
  "Look up the binding for a symbol in the environment.
   Used internally by env-value and popl-set! "
  (assoc symbol (car env)))

(define (env-value symbol env)
  "Return the value of a symbol bound in the given environment.  Throws an
   error if the symbol is not bound."
  (let ((pr (popl-get-binding symbol env)))
    (if pr
        (cadr pr)
        (popl-error (format #f "Undefined variable ~A" symbol)))))

(define (popl-define symbol value env)
  "Implementation of define special form.  Adds new binding to environment
   and returns the symbol that was defined."
  (popl-bind symbol value env)
  symbol)

(define (popl-set! symbol value env)
  "Find existing binding for symbol, and change its value to something new.
   Throws error if given symbol is not bound."
  (let ((pr (popl-get-binding symbol env)))
    ;;(format #t pr)
    (if (not pr) (popl-error (format #f "Unbound variable ~A" symbol)))
    (let ((old (env-value symbol env)))
      (set-car! (cdr pr) value)
      old)))

(define *LOOPTOP* #!unspecific)

(define *TOP-ENVIRONMENT*
  (list (list)))

(popl-define 'car car *TOP-ENVIRONMENT*)
(popl-define 'cdr cdr *TOP-ENVIRONMENT*)
(popl-define 'cons cons *TOP-ENVIRONMENT*)
(popl-define 'format format *TOP-ENVIRONMENT*)
(popl-define 'eq? eq? *TOP-ENVIRONMENT*)
(popl-define 'equal? equal? *TOP-ENVIRONMENT*)
(popl-define 'null? null? *TOP-ENVIRONMENT*)
(popl-define '+ + *TOP-ENVIRONMENT*)
(popl-define '- - *TOP-ENVIRONMENT*)
(popl-define '* * *TOP-ENVIRONMENT*)
(popl-define '/ / *TOP-ENVIRONMENT*)
(popl-define '= = *TOP-ENVIRONMENT*)

(define (popl-apply function arguments)
  "Implementation of function-calling lambdas.
   Extracts the pieces of the lambda and copies the environment,
   binds each parameter, recursively evaluates each form in the body in
   the copied environment."
  (let* ((lambda-parameters (first function))
         (lambda-body (second function))
         (lambda-env (third function))
         (env (list (first lambda-env))))
  	;; check if function is given correct number of parameters
    (if (not (eq? (length arguments) (length lambda-parameters)))
        (popl-error (format #f "Function expected ~A arguments, but ~A given" (length lambda-parameters) (length arguments))))
    ;; bind parameters in enviorment
    (for-each (lambda (pair) (popl-bind (car pair) (cadr pair) env))
       (zip lambda-parameters arguments))
    ;; return the evaluated result of function body
    (let ((result #!unspecific))
      (for-each (lambda (form) (set! result (popl-eval form env)))
          lambda-body)
      result)))

(define (popl-eval-let bindings forms env)
   "Evaluation of let statements."
  (let ((env2 (list (car env)))) ;; copy of enviorment
       ;; bind bindings in enviorment
       (for-each (lambda (pair) (popl-bind (car pair) (popl-eval (cadr pair) env) env2)) bindings)
       ;; return the evaluated result of the forms
       (let ((result #!unspecific))
          (for-each (lambda (expr) (set! result (popl-eval expr env2))) forms)
          result)))

(define (popl-eval-let* bindings forms env)
  "Evaluation of let* statements."
  (if (eq? (length bindings) 1)
      (popl-eval-let bindings forms env)
      (popl-eval-let (list (car bindings)) ;; constructs a nested let recursively
                     (list (cons 'let* (cons (cdr bindings) forms))) env)))

(define (popl-eval-cond conditions env)
  "Evaluation of cond statement."
  (let ((head (car conditions))
        (rest (cdr conditions)))
    (if (or (eq? (car head) 'else) (popl-eval (car head) env))
        (popl-eval (cadr head) env)
        (popl-eval-cond rest env))))

(define (popl-eval-list elements env)
  "Evaluation of list statement"
  (if (null? elements) ()
      (cons (popl-eval (car elements) env) (popl-eval-list (cdr elements) env))))

(define (member? item lst)
  "Function that returns boolean true if the item is in the list,
   false otherwise"
  (cond ((null? lst) #f)
        ((equal? (car lst) item) #t)
        (else (member? item (cdr lst)))))

(define (duplicates lst)
  "Function that returns boolean true if there are duplicate
   members of the list, false otherwise."
  (cond ((null? lst) #f)
        ((member? (car lst) (cdr lst)) #t)
        (else (duplicates (cdr lst)))))

(define (popl-eval expr env)
  "This is the main evaluator.  It is where you will add code to implement
   more features of our-lisp. You may also add helper functions
   in the spirit of popl-define, popl-set!, and popl-apply."
  ; (format #t "DEBUG: Eval ~A~%" expr)
  (cond ((or (number? expr) (boolean? expr) (null? expr))
         ;; numbers, booleans, null list all just evaluate to themselves
         expr)
        ((symbol? expr)
         ;; If you have a symbol to evaluate, look it up!
         (env-value expr env))
        ((pair? expr)
         ;; pair could be a lot of things.  Check each special form...
         (cond ((eq? (first expr) 'define)
         	    ;; check if no assignment for symbol
                (if (null? (cddr expr)) (popl-error (format #f "Ill-formed special form: ~A" expr)))
                (let ((sym (second expr))
                      (val (popl-eval (third expr) env)))
                  (popl-define sym val env)))
               ((eq? (first expr) 'quote)
                (second expr))
               ((eq? (first expr) 'set!)
                (popl-set! (second expr) (popl-eval (third expr) env) env))
               ((eq? (first expr) 'list)
                (popl-eval-list (cdr expr) env))
               ((eq? (first expr) 'lambda)
               	;; checks if no body of lambda expression
                (if (null? (cddr expr)) (popl-error (format #f "Ill-formed special form: ~A" expr)))
                ;; checks if parameters are duplicatively defined
                (if (duplicates (second expr)) (popl-error (format #f "Ill-formed special form: ~A" expr)))
                (list (second expr) ;; formal parameters
                      (cddr expr)   ;; body
                      env))         ;; environment
               ((eq? (first expr) 'let)  ;; (let BINDINGS FORM1 FORM2......)
                (popl-eval-let (second expr) (cddr expr) env))
               ((eq? (first expr) 'let*)
                (popl-eval-let* (second expr) (cddr expr) env))
               ((eq? (first expr) 'if)
                (if (popl-eval (second expr) env)
                    (popl-eval (third expr) env)
                    (popl-eval (fourth expr) env)))
               ((eq? (first expr) 'cond)
                 (popl-eval-cond (cdr expr) env))
               (else
                 ;; ...but if not a special form, must be a function call.
                 (let* ((items (map (lambda (form) (popl-eval form env)) expr))
                        (function (first items)))
                   ;; TODO:  perhaps some error checking here to make sure
                   ;; that the function is callable.
                    (if (procedure? function) ;; if function is built in.
                        (apply function (cdr items))
                        (popl-apply function (cdr items)))))))
        (else "I don't know")))


(define (popl-repl)
  "Finally, this version of popl-repl makes the tail recursion explicit by
   using a 'let loop'"
  (call-with-current-continuation (lambda (here) (set! *LOOPTOP* here)))
  (let loop ()
    (format #t "H]=> ")
    (let ((expr (read)))
      (cond ((equal? expr '(exit)) (format #t "~A~%" "Bye then"))
            (else (format #t "~A~%" (popl-eval expr *TOP-ENVIRONMENT*))
                  (loop))))))




;; end of file
