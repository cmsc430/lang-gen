#lang racket

(require (for-syntax syntax/parse)
         rackcheck)

;; thoughts:
;; * separate out the application of builtin primitives from generalized application?
;; * how to handle read-byte
;;   - generate a construct that let-binds it, and discriminates on the let-binding
;;     (let ([x (read-byte)])
;;       (if (char? x)
;;           (... generate an expression with x is char ...)
;;           (... generate an expression with x is eof ...)))
;;   - could add a "narrow" form that takes a variable in the environment that is a
;;     TOr and scrutinizes it and narrows the types in the sub-terms.
;; strings, vectors

(provide build-gen:expr
         (struct-out TAny)
         (struct-out TBot)
         (struct-out TVoid)
         (struct-out TInt)
         (struct-out TNat)
         (struct-out TBool)
         (struct-out TChar)
         (struct-out TEOF))

;; Type Structs
(struct TAny () #:prefab)
(struct TBot () #:prefab)

(struct TInt () #:prefab)
(struct TNat () #:prefab)
(struct TBool () #:prefab)
(struct TChar () #:prefab)
(struct TEOF () #:prefab)

(struct TVoid () #:prefab)

(struct TPair (left right) #:prefab)
(struct TList (type) #:prefab)
(struct TEmpty () #:prefab)

(struct TBox (type) #:prefab)

(define var-form
  (λ (k size env type)
    (let ([env-candidates (filter-env (λ (t) (type-subsumes? type t)) env)])
      (if (not (empty? env-candidates))
          (cons (length env-candidates)
                (gen:one-of (map car env-candidates)))
          #f))))

(define (val-form val-type val-gen)
  (λ (k size env type)
    (if (type-subsumes? type val-type)
        (cons 1 val-gen)
        #f)))

(define (prim1-form id arg result)
  (λ (k size env type)
    (if (and (not (assoc id env)) (type-subsumes? type result))
        (cons size
              (gen:let
               ([e (gen:resize ((knot-expr k) env arg) (quotient size 2))])
               `(,id ,e)))
        #f)))

(define (prim2-form id arg1 arg2 result)
  (λ (k size env type)
    (if (and (not (assoc id env)) (type-subsumes? type result))
        (cons size
              (gen:let
               ([e1 (gen:resize ((knot-expr k) env arg1) (quotient size 2))]
                [e2 (gen:resize ((knot-expr k) env arg2) (quotient size 2))])
               `(,id ,e1 ,e2)))
        #f)))

(define (primN-form id args result)
  (λ (k size env type)
    (if (and (not (assoc id env)) (type-subsumes? type result))
        (cons size
              (gen:let
               ([n (gen:map gen:natural (compose exact-ceiling sqrt))]
                [es (gen:list-len (gen:resize ((knot-expr k) env args)
                                              (quotient size (add1 n)))
                                  n)])
               `(,id ,@es)))
        #f)))

(define if-form
  (λ (k size env type)
    (cons size
          (gen:let
           ([pred-type (gen:one-of (list (TBool) (TAny)))]
            [e-pred (gen:resize ((knot-expr k) env pred-type) (quotient size 5))]
            [e-then (gen:resize ((knot-expr k) env type) (quotient (* size 2) 5))]
            [e-else (gen:resize ((knot-expr k) env type) (quotient (* size 2) 5))])
           `(if ,e-pred ,e-then ,e-else)))))

(define let1-form
  (λ (k size env type)
    (cons size
          (gen:let
           ([id gen:id]
            [val-type (knot-type k)]
            [e1 (gen:resize ((knot-expr k) env val-type) (quotient size 3))]
            [e2 (gen:resize ((knot-expr k) (env-add id val-type env) type)
                            (quotient (* size 2) 3))])
           `(let ([,id ,e1])
              ,e2)))))

(define let-form
  (λ (k size env type)
    (cons size
          (gen:let
           ([n (gen:integer-in 0 (exact-floor (sqrt size)))]
            [ids (gen:map (gen:list-len gen:id n) remove-duplicates)]
            [val-types (gen:list-len (knot-type k) (length ids))]
            [e-vals (gen:resize
                     (gen:tuple* (map (curry (knot-expr k) env) val-types))
                     (quotient size (* 4 (add1 (length ids)))))]
            [e-body (gen:resize
                     ((knot-expr k) (env-add* ids val-types env) type)
                     (quotient size (* 2 (add1 (length ids)))))])
           `(let ,(map list ids e-vals) ,e-body)))))

(define let*-form
  (λ (k size env type)
    (cons size
          (gen:let
           ([n (gen:map gen:natural (compose exact-floor sqrt))]
            [ids (gen:list-len gen:id n)]
            [val-types (gen:list-len (knot-type k) n)])
           (let ([envs (foldl (λ (id t acc)
                                (cons (env-add id t (first acc)) acc))
                              (list env) ids val-types)])
             (gen:let
              ([e-vals (gen:resize
                        (gen:tuple* (map (knot-expr k) (reverse (rest envs)) val-types))
                        (quotient size (* 4 (add1 n))))]
               [e-body (gen:resize
                        ((knot-expr k) (first envs) type)
                        (quotient size (* 2 (add1 n))))])
              `(let* ,(map list ids e-vals) ,e-body)))))))

(define cond-form
  (λ (k size env type)
    (cons (quotient size 4)
          (gen:let
           ([n (gen:map gen:natural (compose exact-floor sqrt))])
           (let ([pred-gen (gen:resize (gen:bind (gen:one-of (list (TBool) (TAny)))
                                                 (λ (t) ((knot-expr k) env t)))
                                       (quotient size (* 4 (max 1 n))))]
                 [body-gen (gen:resize ((knot-expr k) env type)
                                       (quotient (* size 3) (* 4 (max 1 n))))])
             (gen:let
              ([e-preds (gen:list-len pred-gen n)]
               [e-bodies (gen:list-len body-gen n)]
               [e-else body-gen])
              `(cond ,@(map (λ (p b) `[,p ,b]) e-preds e-bodies)
                     [else ,e-else])))))))

(define case-form
  (λ (k size env type)
    (cons (quotient size 4)
          (gen:let
           ([n (gen:map gen:natural (compose exact-floor sqrt))])
           (let ([datum-gen (gen:map (gen:list (gen:quotable k) #:max-length n)
                                     remove-duplicates)]
                 [body-gen (gen:resize ((knot-expr k) env type)
                                       (quotient (* size 3) (* 4 (max 1 n))))])
             (gen:let
              ([datums (gen:list-len datum-gen n)]
               [e-bodies (gen:list-len body-gen n)]
               [e-pred (gen:resize ((knot-expr k) env (TAny))
                                   (quotient size (* 4 (max 1 n))))]
               [e-else body-gen])
              `(case ,e-pred ,@(map list datums e-bodies)
                 [else ,e-else])))))))

(define begin-form
  (λ (k size env type)
    (cons (quotient size 2)
          (gen:let
           ([e1 (gen:resize ((knot-expr k) env (TAny)) (quotient size 4))]
            [e2 (gen:resize ((knot-expr k) env type) (quotient (* 3 size) 4))])
           `(begin ,e1 ,e2)))))

(define cons-form
  (λ (k size env type)
    (if (type-subsumes? type (TPair (TBot) (TBot)))
        (cons size
              (match type
                [(TAny)
                 (gen:let
                  ([t2 (gen:one-of (list (TList (TAny)) (TAny)))]
                   [e1 (gen:resize ((knot-expr k) env (TAny)) (quotient size 2))]
                   [e2 (gen:resize ((knot-expr k) env t2) (quotient size 2))])
                  `(cons ,e1 ,e2))]
                [(TPair l r)
                 (gen:let
                  ([e1 (gen:resize ((knot-expr k) env l) (quotient size 2))]
                   [e2 (gen:resize ((knot-expr k) env r) (quotient size 2))])
                  `(cons ,e1 ,e2))]
                [(TList t)
                 (gen:let
                  ([e1 (gen:resize ((knot-expr k) env t) (quotient size 2))]
                   [e2 (gen:resize ((knot-expr k) env (TList t)) (quotient size 2))])
                  `(cons ,e1 ,e2))]))
        #f)))

(define car-form
  (λ (k size env type)
    (let ([env-candidates (filter-env (λ (t) (type-subsumes? (TPair type (TAny)) t)) env)])
      (if (not (empty? env-candidates))
          (cons (length env-candidates)
                (gen:let
                 ([x (gen:one-of (map car env-candidates))])
                 `(car ,x)))
          #f))))

(define cdr-form
  (λ (k size env type)
    (let ([env-candidates (filter-env (λ (t) (type-subsumes? (TPair (TAny) type) t)) env)])
      (if (not (empty? env-candidates))
          (cons (length env-candidates)
                (gen:let
                 ([x (gen:one-of (map car env-candidates))])
                 `(cdr ,x)))
          #f))))

(define box-form
  (λ (k size env type)
    (if (type-subsumes? type (TBox (TBot)))
        (cons size
              (gen:let
                  ([e (gen:resize ((knot-expr k) env
                                                 (if (TAny? type)
                                                     (TAny)
                                                     (TBox-type type)))
                                  (quotient size 2))])
                  `(box ,e)))
        #f)))

(define unbox-form
  (λ (k size env type)
    (let ([env-candidates (filter-env (λ (t) (type-subsumes? (TBox type) t)) env)])
      (if (not (empty? env-candidates))
          (cons (length env-candidates)
                (gen:let
                 ([x (gen:one-of env-candidates)])
                 `(unbox ,x)))
          #f))))

(define weaken-form
  (λ (k size env type)
    (if (not (TAny? type))
        (cons (quotient size 8)
              ((knot-expr k) env (TAny)))
        #f)))

(define integer->char-form
  (λ (k size env type)
    (if (type-subsumes? type (TChar))
        (cons size
              (gen:let
               ([e (gen:resize ((knot-expr k) env (TInt)) (quotient size 2))])
               (if (and (integer? e)
                        (or (<= 0 e 55295)
                            (<= 57344 e 1114111)))
                   `(integer->char ,e)
                   `(integer->char (let ([n ,e])
                                     (if (< n 55296)
                                         (if (< -1 n)
                                             n
                                             0)
                                         55295))))))
        #f)))

(define form-table
  (list
   (cons 'var var-form)
   
   (cons 'add1 (prim1-form 'add1 (TInt) (TInt)))
   (cons 'sub1 (prim1-form 'sub1 (TInt) (TInt)))
   (cons 'abs (prim1-form 'abs (TInt) (TInt)))
   (cons 'unary- (prim1-form '- (TInt) (TInt)))
   (cons 'binary- (prim2-form '- (TInt) (TInt) (TInt)))
   (cons 'binary+ (prim2-form '+ (TInt) (TInt) (TInt)))
   (cons '+ (primN-form '+ (TInt) (TInt)))
   
   (cons '< (prim2-form '< (TInt) (TInt) (TBool)))
   (cons '= (prim2-form '= (TInt) (TInt) (TBool)))
   (cons 'zero? (prim1-form 'zero? (TInt) (TBool)))
   
   (cons 'not (prim1-form 'not (TAny) (TBool)))
   
   (cons 'integer? (prim1-form 'integer? (TAny) (TBool)))
   (cons 'boolean? (prim1-form 'boolean? (TAny) (TBool)))
   (cons 'char? (prim1-form 'char? (TAny) (TBool)))
   (cons 'eof-object? (prim1-form 'eof-object? (TAny) (TBool)))
   (cons 'cons? (prim1-form 'cons? (TAny) (TBool)))
   (cons 'empty? (prim1-form 'empty? (TAny) (TBool)))
   (cons 'box? (prim1-form 'box? (TAny) (TBool)))

   (cons 'char->integer (prim1-form 'char->integer (TChar) (TInt)))
   (cons 'integer->char integer->char-form)

   (cons 'cons cons-form)
   (cons 'car car-form)
   (cons 'cdr cdr-form)

   (cons 'box box-form)
   (cons 'unbox unbox-form)
   
   (cons 'if if-form)
   (cons 'let1 let1-form)
   (cons 'let let-form)
   (cons 'let* let*-form)
   (cons 'cond cond-form)
   (cons 'case case-form)
   (cons 'begin begin-form)))

(define (build-gen:expr #:values vts #:forms fs)
  (letrec ([gen:expr (λ (env type)
                       (gen:no-shrink
                        (gen:sized
                         (λ (size)
                           (gen:frequency
                            (cons (cons 1 (gen:val k type))
                                  (filter-map (λ (f) (f k size env type)) forms)))))))]
           [gen:type (gen:no-shrink
                      (gen:delay
                       (apply gen:choice (map (λ (g) (g k)) type-gens))))]
           [forms (map (λ (f) (cdr (assoc f form-table))) fs)]
           [type-gens (map type-gen vts)]
           [base-types (append-map type-base-types vts)]
           [k (knot gen:expr gen:type base-types)])
    gen:expr))

(define (quotable? t)
  (match t
    [(or (TInt) (TNat) (TBool) (TChar)) #t]
    [_ #f]))

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

    ;; Short-circuit these cases after reflexivity.
    [(_ (TAny)) #f]
    [((TBot) _) #f]

    ;; Integers subsume the naturals
    [((TInt) (TNat)) #t]

    [((TPair l1 r1) (TPair l2 r2)) (and (type-subsumes? l1 l2)
                                        (type-subsumes? r1 r2))]
    [((TList t1) (TList t2)) (type-subsumes? t1 t2)]
    [((TList t) (TEmpty)) #t]

    [((TList t1) (TPair l r)) (and (type-subsumes? t1 l)
                                   (type-subsumes? (TList t1) r))]

    [((TBox t1) (TBox t2)) (type-subsumes? t1 t2)]

    #;[((TFun d1 d1-opt d1-rest? c1) (TFun d2 d2-opt d2-rest? c2))
     (and (type-subsumes? c1 c2)
          (domain-subsumes? t2 t1))]
    
    [(_ _) #f]))

(define (domain-subsumes? tfun1 tfun2)
  (error "not yet implemented (good luck)"))

(define (base-type? k t)
  (and (member t (knot-base-types k)) #t))

;; Environment helper functions
(define (env-add id type env)
  (cons (cons id type) env))

(define (env-add* ids types env)
  (append (map cons ids types) env))

(define (foldl-env f base env)
  (foldl (λ (m acc) (f (car m) (cdr m) acc))
         base
         (remove-duplicates env #:key car)))

(define (foldr-env f base env)
  (foldr (λ (m acc) (f (car m) (cdr m) acc))
         base
         (remove-duplicates env #:key car)))

(define (filter-env f env)
  (filter (λ (m) (f (cdr m)))
          (remove-duplicates env #:key car)))

(struct knot (expr type base-types))

(define (gen:base-type k [f (const #t)])
  (gen:one-of (filter f (knot-base-types k))))

(define (gen:val k type)
  (match type
    [(TAny) (gen:bind (gen:base-type k) (λ (t) (gen:val k t)))]
    [(TNat) (gen:map gen:real (λ (x) (exact-floor (* (- (/ 1 x) 1) 2))))]
    [(TInt) (gen:let ([n (gen:val k (TNat))]
                      [neg? gen:boolean])
                     (if neg? (- n) n))]
    [(TBool) gen:boolean]
    ;; TODO: wider character range
    [(TChar) gen:char-alphanumeric]
    [(TEOF) (gen:const 'eof)]
    ;; a bit of a hack, since void is technically a procedure
    [(TVoid) (gen:const '(void))]
    [(TPair l r) (gen:let ([lv (gen:val k l)]
                           [rv (gen:val k r)])
                          `(cons ,lv ,rv))]
    [(TList _) (gen:const ''())]
    [(TEmpty) (gen:const ''())]
    [(TBot) (error "wat")]))

(define gen:id
  (gen:map gen:char-letter (compose string->symbol string)))

(define (gen:quotable k)
  (gen:bind (gen:base-type k quotable?)
            (λ (t) (gen:val k t))))

(define (gen:read-op k env type)
  (gen:sized
   (λ (size)
     (gen:let ([id gen:id]
               [read-op (gen:one-of (list 'read-byte 'peek-byte))]
               [e1 (gen:resize ((knot-expr k) (env-add id (TEOF) env) type)
                               (quotient size 2))]
               [e2 (gen:resize ((knot-expr k) (env-add id (TChar) env) type)
                               (quotient size 2))])
              `(let ([,id (,read-op)])
                 (if (eof-object? ,id)
                     ,e1
                     ,e2))))))

(define (gen:write-op k env type)
  (gen:sized
   (λ (size)
     (gen:let ([id gen:id]
               [e1 (gen:resize ((knot-expr k) env (TNat)) (quotient size 4))]
               [e2 (gen:resize ((knot-expr k) env type) (quotient (* 3 size) 4))])
              `(begin
                 (let ([,id ,e1])
                   (if (< ,id 256)
                       (write-byte ,id)
                       #f))
                 ,e2)))))

(define (type-gen t)
  (match t
    ['integers (λ (k) (gen:one-of (list (TInt) (TNat))))]
    ['booleans (λ (k) (gen:const (TBool)))]
    ['characters (λ (k) (gen:const (TChar)))]
    ['eof (λ (k) (gen:const (TEOF)))]
    ['void (λ (k) (gen:const (TVoid)))]
    ['pairs (λ (k) (gen:let ([t1 (knot-type k)]
                             [t2 (knot-type k)])
                            (TPair t1 t2)))]
    ['lists (λ (k) (gen:choice
                    (gen:const (TEmpty))
                    (gen:map (knot-type k) TList)))]))

(define (type-base-types t)
  (match t
    ['integers (list (TInt) (TNat))]
    ['booleans (list (TBool))]
    ['characters (list (TChar))]
    ['eof (list (TEOF))]
    ['void (list (TVoid))]
    ['pairs '()]
    ['lists (list (TEmpty))]))

(define arith-ops
  '(add1 sub1 abs + un/binary- zero? integer?))

(define char-ops
  '(integer->char char->integer char?))

(define list-ops
  '(cons car cdr cons? empty?))

(define box-ops
  '(box unbox box?))

#;(define arith-lang
    ((build-gen:expr #:values (list 'integers 'booleans)
                     #:forms (list 'app 'if 'let 'let* 'cond))
     (build-env (list 'add1 'sub1 '+ '- 'zero? 'not))
     (TAny)))
    