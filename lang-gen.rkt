#lang racket

(require (for-syntax syntax/parse)
         rackcheck)

(provide lang-generator
         (struct-out TAny)
         (struct-out TBot)
         (struct-out TInt)
         (struct-out TNat)
         (struct-out TBool)
         (struct-out TChar)
         (struct-out TEOF)
         (struct-out TFun)
         T->)

;; Type Structs
(struct TAny () #:prefab)
(struct TBot () #:prefab)

(struct TInt () #:prefab)
(struct TNat () #:prefab)
(struct TBool () #:prefab)
(struct TChar () #:prefab)
(struct TEOF () #:prefab)

(struct TFun (domain optional rest? codomain) #:prefab #:extra-constructor-name T->*)

(define-syntax-rule (T-> domain ... codomain)
  (TFun (list domain ...) '() #f codomain))


;; Type subsumption relation (subtyping)
;; Produces true if t1 subsumes t2
(define (type-subsumes? t1 t2)
  (match* (t1 t2)
    ;; Any subsumes all
    [((TAny) _) #t]
    ;; All subsumes Bot
    [(_ (TBot)) #t]

    ;; Reflexivity
    [(t t) #t]

    ;; Integers subsume the naturals
    [((TInt) (TNat)) #t]

    ;; Functions subsume if domains match
    [((TFun d1 d1-opt d1-rest? c1) (TFun d2 d2-opt d2-rest? c2))
     (and (type-subsumes? c1 c2)
          (domain-subsumes? t2 t1))]
    
    [(_ _) #f]))

(define (domain-subsumes? tfun1 tfun2)
  (error "not yet implemented (good luck)"))

(define (base-type? t)
  (match t
    [(TInt) #t]
    [(TNat) #t]
    [(TBool) #t]
    [(TEOF) #t]
    [_ #f]))

;; Environment helper functions
(define (env-add id type env)
  (cons (cons id type) env))

(define (env-add* ids types env)
  (append (map cons ids types) env))

(define (filter-env f env)
  (filter (λ (m) (f (cdr m)))
          (remove-duplicates env #:key car)))

(define (gen:simple-expr gen:val env type)
  (let ([env-candidates (map car (filter-env (λ (t) (and (base-type? t)
                                                         (type-subsumes? type t)))
                                             env))])
    (if (empty? env-candidates)
        (gen:val type)
        (gen:choice (gen:val type) (gen:one-of env-candidates)))))

(define (gen:function-domain tf)
  (match-let ([(TFun domain opt rest? _) tf])
    (cond
      [(and (empty? opt) (false? rest?)) (gen:const domain)]
      [(false? rest?) (gen:let ([m (gen:integer-in 0 (length opt))])
                               (append domain (take opt m)))]
      [else
       (gen:let ([n (gen:map gen:natural (compose exact-ceiling sqrt))]
                 [m (gen:integer-in 0 (length opt))])
                (append domain
                        (take opt (min (+ n m) (length opt)))
                        (make-list (max 0 (- (+ n m) (length opt))) rest?)))])))

(define (gen:app gen:expr env codomain)
  (let ([candidates (filter-env (λ (t)
                                  (and (TFun? t)
                                       (type-subsumes? codomain (TFun-codomain t))))
                                env)])
    (gen:sized
     (λ (size)
       (if (empty? candidates)
           (gen:resize (gen:expr env codomain) (quotient size 2))
           (gen:let ([m (gen:one-of candidates)]
                     [dom (gen:function-domain (cdr m))]
                     [es (gen:resize
                          (gen:tuple* (map (curry gen:expr env) dom))
                          (quotient size (add1 (length dom))))])
                    `(,(car m) ,@es)))))))

(define (gen:if gen:expr env type)
  (gen:sized
   (λ (size)
     (gen:let ([e-pred (gen:resize (gen:expr env (TAny)) (quotient size 5))]
               [e-then (gen:resize (gen:expr env type) (quotient (* 2 size) 5))]
               [e-else (gen:resize (gen:expr env type) (quotient (* 2 size) 5))])
              `(if ,e-pred ,e-then ,e-else)))))

(define (gen:let-exp gen:expr gen:base-type env type)
  (gen:sized
   (λ (size)
     (let ([id-gen (gen:map gen:char-letter (compose string->symbol string))])
       (gen:let ([n (gen:integer-in 0 (exact-floor (sqrt size)))]
                 [ids (gen:map (gen:list-len id-gen n) remove-duplicates)]
                 [val-types (gen:list-len gen:base-type (length ids))]
                 [e-vals (gen:resize
                          (gen:tuple* (map (curry gen:expr env) val-types))
                          (quotient size (* 4 (add1 (length ids)))))]
                 [e-body (gen:resize
                          (gen:expr (env-add* ids val-types env) type)
                          (quotient size (* 2 (add1 (length ids)))))])
                `(let ,(map list ids e-vals) ,e-body))))))

(define (gen:let1-exp gen:expr gen:base-type env type)
  (gen:sized
   (λ (size)
     (gen:let ([val-type gen:base-type]
               [id (gen:map gen:char-letter (compose string->symbol string))]
               [e-val (gen:resize (gen:expr env val-type) (quotient size 3))]
               [e-body (gen:resize (gen:expr (env-add id val-type env) type)
                                   (quotient (* size 2) 3))])
              `(let ([,id ,e-val]) ,e-body)))))

(define (gen:let*-exp gen:expr gen:base-type env type)
  (gen:sized
   (λ (size)
     (let ([id-gen (gen:map gen:char-letter (compose string->symbol string))])
       (gen:let
        ([n (gen:map gen:natural (compose exact-floor sqrt))]
         [ids (gen:list-len id-gen n)]
         [val-types (gen:list-len gen:base-type n)])
        (let ([envs (foldl (λ (id t acc)
                             (cons (env-add id t (first acc)) acc))
                           (list env) ids val-types)])
          (gen:let
           ([e-vals (gen:resize
                     (gen:tuple* (map gen:expr (reverse (rest envs)) val-types))
                     (quotient size (* 4 (add1 n))))]
            [e-body (gen:resize
                     (gen:expr (first envs) type)
                     (quotient size (* 2 (add1 n))))])
           `(let* ,(map list ids e-vals) ,e-body))))))))

(define (gen:cond gen:expr env type)
  (gen:sized
   (λ (size)
     (gen:let ([n (gen:map gen:natural (compose exact-floor sqrt))])
              (let ([pred-gen (gen:resize (gen:expr env (TAny))
                                          (quotient size (* 4 (max 1 n))))]
                    [body-gen (gen:resize (gen:expr env type)
                                          (quotient (* size 3) (* 4 (max 1 n))))])
                (gen:let ([e-preds (gen:list-len pred-gen n)]
                          [e-bodies (gen:list-len body-gen n)]
                          [e-else body-gen])
                         `(cond ,@(map (λ (p b) `[,p ,b]) e-preds e-bodies)
                                [else ,e-else])))))))

; TODO: better datum selection
(define (gen:case gen:expr gen:val env type)
  (gen:sized
   (λ (size)
     (gen:let ([n (gen:map gen:natural (compose exact-floor sqrt))])
              (let ([datum-gen (gen:map (gen:list (gen:val (TAny)) #:max-length n)
                                        (λ (l) (filter (λ (v) (not (equal? v 'eof)))
                                                       (remove-duplicates l))))]
                    [body-gen (gen:resize (gen:expr env type)
                                          (quotient (* size 3) (* 4 (max 1 n))))])
                (gen:let ([datums (gen:list-len datum-gen n)]
                          [e-bodies (gen:list-len body-gen n)]
                          [e-pred body-gen]
                          [e-else body-gen])
                          `(case ,e-pred ,@(map list datums e-bodies)
                             [else ,e-else])))))))

(define (gen:begin gen:expr env type)
  (gen:sized
   (λ (size)
     (gen:let ([e1 (gen:resize (gen:expr env (TAny)) (quotient size 4))]
               [e2 (gen:resize (gen:expr env type) (quotient (* 3 size) 4))])
              `(begin ,e1 ,e2)))))

(begin-for-syntax
  
  (define-syntax-class value-type
    (pattern (~or* (~datum 'integers)
                   (~datum 'booleans)
                   (~datum 'characters)
                   (~datum 'eof))))

  (define-syntax-class expr-form
    (pattern (~or* (~datum 'app)
                   (~datum 'if)
                   (~datum 'cond)
                   (~datum 'case)
                   (~datum 'let1)
                   (~datum 'let)
                   (~datum 'let*)
                   (~datum 'begin))))

  (define-syntax-class expr-op
    (pattern (~or* 'add1 'sub1 'abs 'not 'zero? 'integer? 'boolean? 'char? 'eof-object?
                   'unary- 'binary- 'un/binary- 'binary+ '+
                   'integer->char 'char->integer))))

(define-syntax (lookup-op stx)
  (syntax-parse stx
    [(_ (~datum 'add1)) #'(cons 'add1 (T-> (TInt) (TInt)))]
    [(_ (~datum 'sub1)) #'(cons 'sub1 (T-> (TInt) (TInt)))]
    [(_ (~datum 'abs)) #'(cons 'abs (T-> (TInt) (TInt)))]
    [(_ (~datum 'not)) #'(cons 'not (T-> (TAny) (TBool)))]
    [(_ (~datum 'zero?)) #'(cons 'zero? (T-> (TInt) (TBool)))]
    [(_ (~datum 'integer?)) #'(cons 'integer? (T-> (TAny) (TBool)))]
    [(_ (~datum 'boolean?)) #'(cons 'boolean? (T-> (TAny) (TBool)))]
    [(_ (~datum 'char?)) #'(cons 'char? (T-> (TAny) (TBool)))]
    [(_ (~datum 'eof-object?)) #'(cons 'eof-object? (T-> (TAny) (TBool)))]
    [(_ (~datum 'unary-)) #'(cons '- (T-> (TInt) (TInt)))]
    [(_ (~datum 'binary-)) #'(cons '- (T-> (TInt) (TInt) (TInt)))]
    [(_ (~datum 'un/binary-)) #'(cons '- (T->* (list (TInt)) (list (TInt)) #f (TInt)))]
    [(_ (~datum 'binary+)) #'(cons '+ (T-> (TInt) (TInt) (TInt)))]
    [(_ (~datum '+)) #'(cons '+ (T->* '() '() (TInt) (TInt)))]
    [(_ (~datum 'integer->char)) #'(cons 'integer->char (T-> (TInt) (TChar)))]
    [(_ (~datum 'char->integer)) #'(cons 'char->integer (T-> (TChar) (TInt)))]))

(define-syntax (lookup-type stx)
  (syntax-parse stx
    [(_ (~datum 'integers)) #'(TInt)]
    [(_ (~datum 'booleans)) #'(TBool)]
    [(_ (~datum 'characters)) #'(TChar)]
    [(_ (~datum 'eof)) #'(TEOF)]))

(define-match-expander lookup-type-match
  (lambda (stx)
    (syntax-parse stx
      [(_ (~datum 'integers)) #'(TInt)]
      [(_ (~datum 'booleans)) #'(TBool)]
      [(_ (~datum 'characters)) #'(TChar)]
      [(_ (~datum 'eof)) #'(TEOF)])))

(define-syntax (make-value-gen stx)
  (syntax-parse stx
    [(_ (~datum 'integers))
     #'(gen:let ([x gen:real]
                 [sign (gen:map gen:real (λ (y) (if (<= y 0.5) -1 1)))])
                (* sign (exact-floor (* (- (/ 1 x) 1) 2))))]
    
    [(_ (~datum 'booleans)) #'gen:boolean]

    ;; TODO: wider character range
    [(_ (~datum 'characters)) #'gen:char-alphanumeric]

    [(_ (~datum 'eof)) #'(gen:const 'eof)]))

(define-syntax-rule (make-gen:val gen:base-type gen:val vts ...)
  (lambda (type)
    (match type
      [(TAny) (gen:bind gen:base-type gen:val)]
      [(lookup-type-match vts) (make-value-gen vts)] ...
      [(TBot) (error "wat")])))

(define-syntax-rule (make-gen:simple-expr gen:val)
  (lambda (env type)
    (let ([env-candidates
           (map car (filter-env
                     (λ (t)
                       (and (base-type? t)
                            (type-subsumes? type t)))
                     env))])
      (if (empty? env-candidates)
          (gen:val type)
          (gen:choice (gen:val type)
                      (gen:one-of env-candidates))))))

(define-syntax (lookup-form-freq stx)
  (syntax-parse stx
    [(_ size (~datum 'app)) #'(* 2 size)]
    [(_ size (~datum 'if)) #'(quotient size 2)]
    [(_ size (~datum 'let1)) #'size]
    [(_ size (~datum 'let)) #'(quotient size 2)]
    [(_ size (~datum 'let*)) #'(quotient size 2)]
    [(_ size (~datum 'cond)) #'(quotient size 4)]
    [(_ size (~datum 'case)) #'(quotient size 4)]
    [(_ size (~datum 'begin)) #'(quotient size 2)]))
  
(define-syntax (lookup-form-gen stx)
  (syntax-parse stx
    [(_ ge _ _ (~datum 'app)) #'(curry gen:app ge)]
    [(_ ge _ _ (~datum 'if)) #'(curry gen:if ge)]
    [(_ ge gbt _ (~datum 'let1)) #'(curry gen:let1-exp ge gbt)]
    [(_ ge gbt _ (~datum 'let)) #'(curry gen:let-exp ge gbt)]
    [(_ ge gbt _ (~datum 'let*)) #'(curry gen:let*-exp ge gbt)]
    [(_ ge _ _ (~datum 'cond)) #'(curry gen:cond ge)]
    [(_ ge _ gval (~datum 'case)) #'(curry gen:case ge gval)]
    [(_ ge _ _ (~datum 'begin)) #'(curry gen:begin ge)]))

(define-syntax-rule (make-gen:expr gen:expr gen:base-type gen:val fs ...)
  (lambda (env type)
    (gen:no-shrink
     (gen:sized
      (lambda (size)
        (gen:frequency
         (filter
          (λ (freq) (> (car freq) 0))
          (cons (cons 1 ((make-gen:simple-expr gen:val) env type))
                (list (cons (lookup-form-freq size fs)
                            ((lookup-form-gen gen:expr gen:base-type gen:val fs)
                             env type))
                      ...)))))))))

;; define a lambda that takes an env and a type
;; inside that lambda is a letrec that defines gen:expr and all the forms
;; also defines gen:base-type and gen:val based on #:values

;; TODO: errors for incompatible choices
(define-syntax (lang-generator stx)
  (syntax-parse stx
    [(_ #:values vts:value-type ...+
        #:forms fs:expr-form ...
        #:ops ops:expr-op ...)
     #'(lambda (initial-env type)
         (letrec ([gen:base-type (gen:one-of (list (lookup-type vts) ...))]
                  [gen:val (make-gen:val gen:base-type gen:val vts ...)]
                  [gen:expr (make-gen:expr gen:expr gen:base-type gen:val fs ...)])
           (gen:expr (append initial-env (list (lookup-op ops) ...)) type)))]))
    