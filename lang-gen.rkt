#lang racket

(require "free.rkt" rackcheck)

(define gen:tuple* (curry apply gen:tuple))
(define gen:list-len (compose gen:tuple* make-list))

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

(struct TFun (domain rest? codomain) #:prefab)

(define var-form
  (λ (k size env type)
    (let ([env-candidates (filter-env (λ (t) (and (not (TFun? t)) (type-subsumes? type t))) env)])
      (if (not (empty? env-candidates))
          (cons (length env-candidates)
                (gen:one-of (map car env-candidates)))
          #f))))

(define (val-form val-type val-gen)
  (λ (k size env type)
    (if (type-subsumes? type val-type)
        (cons 1 val-gen)
        #f)))

(define (prim0-form id result)
  (λ (k size env type)
    (if (and (not (dict-has-key? env id)) (type-subsumes? type result))
        (cons 1 `(,id))
        #f)))

(define (prim1-form id arg result)
  (λ (k size env type)
    (if (and (not (dict-has-key? env id)) (type-subsumes? type result))
        (cons size
              (gen:let
               ([e (gen:resize ((knot-expr k) env arg) (quotient size 2))])
               `(,id ,e)))
        #f)))

(define (prim2-form id arg1 arg2 result)
  (λ (k size env type)
    (if (and (not (dict-has-key? env id)) (type-subsumes? type result))
        (cons size
              (gen:let
               ([e1 (gen:resize ((knot-expr k) env arg1) (quotient size 2))]
                [e2 (gen:resize ((knot-expr k) env arg2) (quotient size 2))])
               `(,id ,e1 ,e2)))
        #f)))

(define (primN-form id args result)
  (λ (k size env type)
    (if (and (not (dict-has-key? env id)) (type-subsumes? type result))
        (cons (* 2 size)
              (gen:let
               ([n (gen:map gen:natural (compose exact-ceiling sqrt))]
                [es (gen:list-len n (gen:resize ((knot-expr k) env args)
                                                (quotient size (add1 n))))])
               `(,id ,@es)))
        #f)))

(define if-zero?-form
  (λ (k size env type)
    (cons (quotient size 2)
          (gen:let
           ([e-pred (gen:resize ((knot-expr k) env (TInt)) (quotient size 5))]
            [e-then (gen:resize ((knot-expr k) env type) (quotient (* size 2) 5))]
            [e-else (gen:resize ((knot-expr k) env type) (quotient (* size 2) 5))])
           `(if (zero? ,e-pred) ,e-then ,e-else)))))

(define if-form
  (λ (k size env type)
    (cons (quotient size 2)
          (gen:let
           ([pred-type (gen:one-of (cons (TAny) (make-list 3 (TBool))))]
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

(define let-form-naive
  (λ (k size env type)
    (cons size
          (gen:let
           ([n (gen:integer-in 0 (exact-floor (sqrt size)))]
            [ids (gen:map (gen:list-len n (gen:id env)) remove-duplicates)]
            [val-types (gen:list-len (length ids) (knot-type k))]
            [e-vals (gen:resize
                     (gen:tuple* (map (curry (knot-expr k) env) val-types))
                     (quotient size (* 4 (add1 (length ids)))))]
            [e-body (gen:resize
                     ((knot-expr k) (env-add* ids val-types env) type)
                     (quotient size (* 2 (add1 (length ids)))))])
           `(let ,(map list ids e-vals) ,e-body)))))

(define let-form
  (λ (k size env type)
    (cons (if (<= size 4) 0 size)
          (gen:let
           ([ids (gen:unique-ids env (add1 (exact-floor (log (add1 size)))))]
            [val-types (gen:list-len (length ids) (knot-type k))]
            [e-body (gen:resize
                     ((knot-expr k) (env-add* ids val-types env) type)
                     (quotient size 2))])
           (let* ([free (free-vars e-body)]
                  [used (filter (λ (m) (member (car m) free)) (map cons ids val-types))])
             (gen:let
              ([e-vals (gen:resize
                        (gen:tuple* (map (curry (knot-expr k) env) (map cdr used)))
                        (quotient size (add1 (length used))))])
              `(let ,(map list (map car used) e-vals) ,e-body)))))))

(define let*-form-naive
  (λ (k size env type)
    (cons (quotient size 3)
          (gen:let
           ([n (gen:map gen:natural (compose add1 exact-floor log add1))]
            [ids (gen:list-len n (gen:id env))]
            [val-types (gen:list-len n (knot-type k))])
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

;; pick an id that is free in the body
;; create a binding expression for it
;; add the free variables in the generated expression to the free
;; repeat until there are no ids that are free in the body

(define (gen:let*-vars k env n)
  (if (zero? n)
      (gen:const '())
      (gen:let
       ([id (gen:id env)]
        [type (knot-type k)]
        [rst (gen:let*-vars k (env-add id type env) (sub1 n))])
       (env-add id type rst))))

(define (gen:let*-binds k env vars free)
  (let ([var? (findf (λ (m) (set-member? free (car m))) vars)])
    (match var?
      [#f (gen:const '())]
      [(cons id type)
       (let ([new-vars (dict-remove vars id)])
         (gen:let
          ([e-val ((knot-expr k) (append new-vars env) type)]
           [rst (gen:let*-binds k env new-vars (set-union free (free-vars e-val)))])
          (cons (list id e-val) rst)))])))

(define let*-form
  (λ (k size env type)
    (cons (if (<= size 4) 0 size)
          (gen:let
           ([n (gen:map gen:natural (compose exact-floor log add1))]
            [vars (gen:let*-vars k env n)]
            [e-body (gen:resize ((knot-expr k) (append vars env) type)
                                (quotient size 2))]
            [binds (gen:resize (gen:let*-binds k env vars (free-vars e-body))
                               (quotient size (* 2 (add1 n))))])
           `(let* ,(reverse binds) ,e-body)))))

(define cond-form
  (λ (k size env type)
    (cons (quotient size 4)
          (gen:let
           ([n (gen:map gen:natural (compose exact-floor sqrt))])
           (let ([pred-gen (gen:resize (gen:bind (gen:one-of (cons (TAny) (make-list 3 (TBool))))
                                                 (λ (t) ((knot-expr k) env t)))
                                       (quotient size (* 4 (max 1 n))))]
                 [body-gen (gen:resize ((knot-expr k) env type)
                                       (quotient (* size 3) (* 4 (max 1 n))))])
             (gen:let
              ([e-preds (gen:list-len n pred-gen)]
               [e-bodies (gen:list-len n body-gen)]
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
              ([datums (gen:list-len n datum-gen)]
               [e-bodies (gen:list-len n body-gen)]
               [e-pred (gen:resize ((knot-expr k) env (TAny))
                                   (quotient size (* 4 (max 1 n))))]
               [e-else body-gen])
              `(case ,e-pred ,@(map list datums e-bodies)
                 [else ,e-else])))))))

(define begin-form
  (λ (k size env type)
    (cons (quotient size 2)
          (gen:let
           ([t0 (gen:one-of (list (TAny) (TVoid)))]
            [e1 (gen:resize ((knot-expr k) env t0) (quotient size 4))]
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

(define discrim-list-form
  (λ (k size env type)
    (let ([env-candidates (filter-env (λ (t) (TList? t)) env)])
      (if (not (empty? env-candidates))
          (cons (* size (length env-candidates))
                (gen:let
                 ([m (gen:one-of env-candidates)]
                  [e1 (gen:resize ((knot-expr k)
                                   (env-add (car m) (TPair (TList-type (cdr m)) (cdr m)) env)
                                   type)
                                  (quotient size 2))]
                  [e2 (gen:resize ((knot-expr k) (env-add (car m) (TEmpty) env) type)
                                  (quotient size 2))]
                  [dir gen:boolean])
                 (if dir
                     `(if (cons? ,(car m)) ,e1 ,e2)
                     `(if (empty? ,(car m)) ,e2 ,e1))))
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
        (cons (quotient size 4)
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

(define read-form
  (λ (k size env type)
    (cons size
          (gen:let
           ([id (gen:id env)]
            [read-op (gen:one-of (list 'read-byte 'peek-byte))]
            [e1 (gen:resize ((knot-expr k) (env-add id (TEOF) env) type)
                            (quotient size 2))]
            [e2 (gen:resize ((knot-expr k) (env-add id (TInt) env) type)
                            (quotient size 2))])
           `(let ([,id (,read-op)])
              (if (eof-object? ,id)
                  ,e1
                  ,e2))))))

(define write-form
  (λ (k size env type)
    (if (type-subsumes? type (TVoid))
        (let ([env-candidates (filter-env (λ (t) (type-subsumes? (TInt) t)) env)])
          (cons 1
                (gen:frequency
                 (list (cons 1 (gen:let ([n (gen:integer-in 0 255)])
                                        `(write-byte ,n)))
                       (cons (length env-candidates)
                             (gen:let
                              ([id (gen:map (gen:one-of env-candidates) car)]
                               [e (gen:resize ((knot-expr k) env (TInt)) (quotient size 2))])
                              `(if (< ,id 256)
                                   (if (< -1 ,id)
                                       (write-byte ,id)
                                       (void))
                                   (void))))))))
        #f)))

(define app-form
  (λ (k size env type)
    (let ([env-candidates (filter-env (λ (t) (type-subsumes? (TFun '() (TBot) type) t)) env)])
      (if (not (empty? env-candidates))
          (cons (* size (length env-candidates))
                (gen:let ([m (gen:one-of env-candidates)]
                          [dom (gen:function-domain (TFun-domain (cdr m)) (TFun-rest? (cdr m)))]
                          [args (gen:resize (gen:tuple* (map (λ (t) ((knot-expr k) env t)) dom))
                                            (quotient size (add1 (length dom))))])
                         `(,(car m) ,@args)))
          #f))))

(define form-table
  (list
   (cons 'var var-form)
   (cons 'app app-form)
   
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
   (cons 'discrim-list discrim-list-form)

   (cons 'box box-form)
   (cons 'unbox unbox-form)

   (cons 'if-zero? if-zero?-form)
   (cons 'if if-form)
   (cons 'let1 let1-form)
   (cons 'let let-form)
   (cons 'let* let*-form)
   (cons 'cond cond-form)
   (cons 'case case-form)
   (cons 'begin begin-form)

   (cons 'io-read read-form)
   (cons 'io-write write-form)

   (cons 'weaken weaken-form)))

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
           [forms (map (λ (f) (dict-ref form-table f)) fs)]
           [type-gens (map type-gen vts)]
           [base-types (append-map type-base-types vts)]
           [k (knot gen:expr gen:type base-types)])
    (values gen:expr gen:type)))

(define (gen:define gen:expr gen:type env id)
  (gen:let
   ([n (gen:map gen:natural (compose exact-floor log add1))]
    [args (gen:unique-ids env n)]
    [domain (gen:list-len n gen:type)]
    [codomain gen:type]
    [e-body (gen:expr (env-add* args domain env) codomain)])
   (let* ([free (free-vars e-body)]
          [used (filter (λ (m) (set-member? free (car m))) (map cons args domain))])
     (list
      (TFun (map cdr used) #f codomain)
      `(define (,id ,@(map car used))
         ,e-body)))))

(define (gen:defines gen:expr gen:type env ids)
  (match ids
    ['() (gen:const '())]
    [(cons id rst)
     (gen:let
      ([def (gen:define gen:expr gen:type env id)]
       [defs (gen:defines gen:expr gen:type (env-add id (first def) env) rst)])
      (cons def defs))]))

(define (gen:tfun gen:type)
  (gen:let
   ([t1 gen:type]
    [t2 gen:type])
   (TFun (list t1) #f t2)))

(define (gen:define-binds gen:expr vars free)
  (let ([var? (findf (λ (m) (set-member? free (car m))) vars)])
    (match var?
      [#f (gen:const '())]
      [(cons id type)
       (let ([new-vars (dict-remove vars id)])
         (gen:let
          ([args (gen:unique-ids new-vars (length (TFun-domain type)))]
           [e-body (gen:expr (env-add* args (TFun-domain type) new-vars) (TFun-codomain type))]
           [rst (gen:define-binds gen:expr new-vars
                                  (set-union free (set-remove (free-vars e-body) args)))])
          (cons `(define (,id ,@args) ,e-body) rst)))])))

(define (gen:program^ gen:expr gen:type type)
  (gen:let
   ([n (gen:map gen:natural (compose exact-floor sqrt add1))]
    [ids (gen:unique-ids '() n)]
    [defs (gen:defines gen:expr gen:type '() ids)]
    [e (gen:expr (map (λ (id def) (cons id (first def))) ids defs) type)])
   `(,@(map second defs) ,e)))

(define (gen:program gen:expr gen:type type)
  (gen:sized
   (λ (size)
     (gen:let
      ([n (gen:map gen:natural (compose exact-floor sqrt add1))]
       [ids (gen:unique-ids '() n)]
       [tfs (gen:list-len n (gen:tfun gen:type))]
       [e (gen:expr (map cons ids tfs) type)]
       [defs (gen:resize (gen:define-binds gen:expr (map cons ids tfs) (free-vars e))
                         (quotient size (add1 n)))])
      `(,@defs
        ,e)))))

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

    [((TFun d1 d1-rest? c1) (TFun d2 d2-rest? c2))
     (and (type-subsumes? c1 c2)
          (cond
            [(= (length d1) (length d2)) (andmap type-subsumes? d2 d1)]
            [(< (length d1) (length d2))
             (match d1-rest?
               [#f #f]
               [d1-rest
                (let-values ([(d2-l d2-r) (split-at d2 (length d1))])
                  (and (andmap type-subsumes? d2-l d1)
                       (andmap (curryr type-subsumes? d1-rest) d2-r)))])]
            [else
             (match d2-rest?
               [#f #f]
               [d2-rest
                (let-values ([(d1-l d1-r) (split-at d1 (length d2))])
                  (and (andmap type-subsumes? d2 d1-l)
                       (andmap (curry type-subsumes? d2-rest) d1-r)))])]))]
    
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
    [(TPair l r) (gen:sized
                  (λ (size)
                    (gen:let ([lv (gen:resize (gen:val k l) (quotient size 2))]
                              [rv (gen:resize (gen:val k r) (quotient size 2))])
                             `(cons ,lv ,rv))))]
    [(TList t) (gen:sized
                (λ (size)
                  (gen:frequency
                   (list (cons 1 (gen:const ''()))
                         (cons size (gen:let
                                     ([v (gen:val k t)]
                                      [vl (gen:resize (gen:val k (TList t))
                                                      (quotient size 2))])
                                     `(cons ,v ,vl)))))))]
    [(TEmpty) (gen:const ''())]
    [(TBot) (error "wat")]))

;; TODO: don't generate primop ids
(define (gen:id env)
  (gen:frequency
   (list (cons 1 (gen:let ([n (gen:integer-in 0 4)]
                           [fst gen:char-letter]
                           [rst (gen:list-len n gen:char-alphanumeric)])
                          (string->symbol (list->string (cons fst rst)))))
         (cons (quotient (length env) 4)
               (gen:map (gen:one-of env) car)))))

;; TODO: this algorithm is cursed
(define (gen:unique-ids env n)
  (if (zero? n)
      (gen:const '())
      (gen:let
       ([ids (gen:unique-ids env (sub1 n))])
       (let loop ()
         (gen:let
          ([id (gen:id env)])
          (if (set-member? ids id)
              (loop)
              (gen:const (cons id ids))))))))

(define (gen:quotable k)
  (gen:bind (gen:base-type k quotable?)
            (λ (t) (gen:val k t))))

(define (gen:function-domain domain rest?)
  (match rest?
    [#f (gen:const domain)]
    [rst (gen:sized
          (λ (size)
            (gen:let ([n (gen:integer-in 0 (exact-floor (sqrt size)))])
                     (append domain
                             (make-list n rst)))))]))

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
    ['lists (λ (k) (gen:map (knot-type k) TList))]))

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
  '(add1 sub1 abs + unary- binary- zero? integer?))

(define char-ops
  '(integer->char char->integer char?))

(define list-ops
  '(cons car cdr cons? empty?))

(define box-ops
  '(box unbox box?))
    