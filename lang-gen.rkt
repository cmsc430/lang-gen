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
;; lists, pairs, strings, vectors

;; read-byte
;; peek-byte
;; write-byte

(provide build-gen:expr
         build-env
         (struct-out TAny)
         (struct-out TBot)
         (struct-out TVoid)
         (struct-out TInt)
         (struct-out TNat)
         (struct-out TBool)
         (struct-out TChar)
         (struct-out TEOF)
         (struct-out TFun)
         (struct-out TCaseFun)
         T->)

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

(struct TFun (domain optional rest? codomain) #:prefab
  #:extra-constructor-name T->*)

;; types must all be TFuns
(struct TCaseFun (types) #:prefab)

(define-syntax-rule (T-> domain ... codomain)
  (TFun (list domain ...) '() #f codomain))

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

    ;; Short-circuit these cases after reflexivity and or.
    [(_ (TAny)) #f]
    [((TBot) _) #f]

    ;; Integers subsume the naturals
    [((TInt) (TNat)) #t]

    [((TPair l1 r1) (TPair l2 r2)) (and (type-subsumes? l1 l2)
                                        (type-subsumes? r1 r2))]
    [((TList t1) (TList t2)) (type-subsumes? t1 t2)]
    ;; Not sure if this is needed
    [((TList t) (TEmpty)) #t]

    [((TList t1) (TPair l r)) (and (type-subsumes? t1 l)
                                   (type-subsumes? (TList t1) r))]

    [((TFun d1 d1-opt d1-rest? c1) (TFun d2 d2-opt d2-rest? c2))
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
    ;[(TQuotable) (gen:bind (gen:base-type k quotable?) (λ (t) (gen:val k t)))]
    ;[(TOr l r) (gen:bind gen:boolean (λ (side) (gen:val k (if side l r))))]
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

(define (gen:simple-expr k env type)
  (let ([env-candidates
         (map car (filter-env
                   (λ (t) (and (base-type? k t)
                               (type-subsumes? type t)))
                   env))])
    (if (empty? env-candidates)
        (gen:val k type)
        (gen:choice (gen:val k type)
                    (gen:one-of env-candidates)))))

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

(define (funs-with-codomain codomain env)
  (foldl-env
   (λ (id type acc)
     (cond
       [(TFun? type)
        (if (type-subsumes? codomain (TFun-codomain type))
            (cons (cons id type) acc)
            acc)]
       [(TCaseFun? type)
        ;; filter to all the cases that produce the correct codomain
        (let ([sigs (filter (λ (t) (type-subsumes? codomain (TFun-codomain t)))
                            (TCaseFun-types type))])
          (append (map (curry cons id) sigs) acc))]
       [else acc]))
   '()
   env))

(define (gen:app k env codomain)
  (let ([candidates (funs-with-codomain codomain env)])
    (gen:sized
     (λ (size)
       (if (empty? candidates)
           (gen:resize ((knot-expr k) env codomain) (quotient size 2))
           (gen:let ([m (gen:one-of candidates)]
                     [dom (gen:function-domain (cdr m))]
                     [es (gen:resize
                          (gen:tuple* (map (curry (knot-expr k) env) dom))
                          (quotient size (add1 (length dom))))])
                    `(,(car m) ,@es)))))))

(define (gen:if k env type)
  (gen:sized
   (λ (size)
     (gen:let ([e-pred (gen:resize ((knot-expr k) env (TAny)) (quotient size 5))]
               [e-then (gen:resize ((knot-expr k) env type) (quotient (* 2 size) 5))]
               [e-else (gen:resize ((knot-expr k) env type) (quotient (* 2 size) 5))])
              `(if ,e-pred ,e-then ,e-else)))))

(define gen:id
  (gen:map gen:char-letter (compose string->symbol string)))

(define (gen:let-exp k env type)
  (gen:sized
   (λ (size)
     (gen:let ([n (gen:integer-in 0 (exact-floor (sqrt size)))]
               [ids (gen:map (gen:list-len gen:id n) remove-duplicates)]
               [val-types (gen:list-len (knot-type k) (length ids))]
               [e-vals (gen:resize
                        (gen:tuple* (map (curry (knot-expr k) env) val-types))
                        (quotient size (* 4 (add1 (length ids)))))]
               [e-body (gen:resize
                        ((knot-expr k) (env-add* ids val-types env) type)
                        (quotient size (* 2 (add1 (length ids)))))])
              `(let ,(map list ids e-vals) ,e-body)))))

(define (gen:let1-exp k env type)
  (gen:sized
   (λ (size)
     (gen:let ([val-type (knot-type k)]
               [id gen:id]
               [e-val (gen:resize ((knot-expr k) env val-type) (quotient size 3))]
               [e-body (gen:resize ((knot-expr k) (env-add id val-type env) type)
                                   (quotient (* size 2) 3))])
              `(let ([,id ,e-val]) ,e-body)))))

(define (gen:let*-exp k env type)
  (gen:sized
   (λ (size)
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

(define (gen:cond k env type)
  (gen:sized
   (λ (size)
     (gen:let ([n (gen:map gen:natural (compose exact-floor sqrt))])
              (let ([pred-gen (gen:resize ((knot-expr k) env (TAny))
                                          (quotient size (* 4 (max 1 n))))]
                    [body-gen (gen:resize ((knot-expr k) env type)
                                          (quotient (* size 3) (* 4 (max 1 n))))])
                (gen:let ([e-preds (gen:list-len pred-gen n)]
                          [e-bodies (gen:list-len body-gen n)]
                          [e-else body-gen])
                         `(cond ,@(map (λ (p b) `[,p ,b]) e-preds e-bodies)
                                [else ,e-else])))))))

(define (gen:quotable k)
  (gen:bind (gen:base-type k quotable?)
            (λ (t) (gen:val k t))))

; TODO: better datum selection
(define (gen:case k env type)
  (gen:sized
   (λ (size)
     (gen:let ([n (gen:map gen:natural (compose exact-floor sqrt))])
              (let ([datum-gen (gen:map (gen:list (gen:quotable k) #:max-length n)
                                        remove-duplicates)]
                    [body-gen (gen:resize ((knot-expr k) env type)
                                          (quotient (* size 3) (* 4 (max 1 n))))])
                (gen:let ([datums (gen:list-len datum-gen n)]
                          [e-bodies (gen:list-len body-gen n)]
                          [e-pred (gen:resize ((knot-expr k) env (TAny))
                                              (quotient size (* 4 (max 1 n))))]
                          [e-else body-gen])
                          `(case ,e-pred ,@(map list datums e-bodies)
                             [else ,e-else])))))))

(define (gen:begin k env type)
  (gen:sized
   (λ (size)
     (gen:let ([e1 (gen:resize ((knot-expr k) env (TAny)) (quotient size 4))]
               [e2 (gen:resize ((knot-expr k) env type) (quotient (* 3 size) 4))])
              `(begin ,e1 ,e2)))))

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

;; builds and let-binds an inductive data type
(define (gen:inductive k env type)
  'TODO)

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

(define (form-frequency f)
  (match f
    ['app   (λ (size) (* 2 size))]
    ['if    (λ (size) (quotient size 2))]
    ['let1  (λ (size) size)]
    ['let   (λ (size) (quotient size 2))]
    ['let*  (λ (size) (quotient size 2))]
    ['cond  (λ (size) (quotient size 4))]
    ['case  (λ (size) (quotient size 4))]
    ['begin (λ (size) (quotient size 2))]
    ['read  (λ (size) (quotient size 2))]))

(define (form-gen f)
  (match f
    ['app   gen:app]
    ['if    gen:if]
    ['let1  gen:let1-exp]
    ['let   gen:let-exp]
    ['let*  gen:let*-exp]
    ['cond  gen:cond]
    ['case  gen:case]
    ['begin gen:begin]
    ['read  gen:read-op]))

(define (build-env ops)
  (define (lookup-op op)
    (match op
      ['add1          (cons 'add1 (TCaseFun
                                   (list (T-> (TNat) (TNat))
                                         (T-> (TInt) (TInt)))))]
      ['sub1          (cons 'sub1 (T-> (TInt) (TInt)))]
      ['abs           (cons 'abs (T-> (TInt) (TNat)))]
      ['not           (cons 'not (T-> (TAny) (TBool)))]
      ['zero?         (cons 'zero? (T-> (TInt) (TBool)))]
      ['integer?      (cons 'integer? (T-> (TAny) (TBool)))]
      ['boolean?      (cons 'boolean? (T-> (TAny) (TBool)))]
      ['char?         (cons 'char? (T-> (TAny) (TBool)))]
      ['eof-object?   (cons 'eof-object? (T-> (TAny) (TBool)))]
      ['unary-        (cons '- (T-> (TInt) (TInt)))]
      ['binary-       (cons '- (T-> (TInt) (TInt) (TInt)))]
      ['un/binary-    (cons '- (T->* (list (TInt)) (list (TInt)) #f (TInt)))]
      ['-             (cons '- (T->* (list (TInt)) '() (TInt) (TInt)))]
      ['binary+       (cons '+ (TCaseFun
                                (list (T-> (TNat) (TNat) (TNat))
                                      (T-> (TInt) (TInt) (TInt)))))]
      ['+             (cons '+ (TCaseFun
                                (list (T->* '() '() (TNat) (TNat))
                                      (T->* '() '() (TInt) (TInt)))))]
      ['integer->char (cons 'integer->char (T-> (TNat) (TChar)))]
      ['char->integer (cons 'char->integer (T-> (TChar) (TNat)))]

      ;; TODO: these need forall types
      ['cons          (cons 'cons (T-> 'A 'B (TPair 'A 'B)))]
      ['car           (cons 'car (T-> (TPair 'A 'B) 'A))]
      ['cdr           (cons 'cdr (T-> (TPair 'A 'B) 'B))]
      ['cons?         (cons 'cons? (T-> (TAny) (TBool)))]
      ['empty?        (cons 'empty? (T-> (TAny) (TBool)))]

      ['box           (cons 'box (T-> 'A (TBox 'A)))]
      ['unbox         (cons 'unbox (T-> (TBox 'A) 'A))]
      ['box?          (cons 'box? (T-> (TAny) (TBool)))]))
  (map lookup-op ops))

(define (build-gen:expr #:values vts #:forms fs)
  (letrec ([gen:expr (λ (env type)
                       (gen:no-shrink
                        (gen:sized
                         (λ (size)
                           (gen:frequency
                            (cons (cons 1 (gen:simple-expr k env type))
                                  (map cons
                                       (map (λ (f) (f size)) f-freqs)
                                       (map (λ (g) (g k env type)) f-gens))))))))]
           [gen:type (gen:no-shrink
                      (gen:delay
                       (apply gen:choice (map (λ (g) (g k)) t-gens))))]
           [f-freqs (map form-frequency fs)]
           [f-gens (map form-gen fs)]
           [t-gens (map type-gen vts)]
           [base-types (append-map type-base-types vts)]
           [k (knot gen:expr gen:type base-types)])
    gen:expr))

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
