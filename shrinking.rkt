#lang racket

(require rackcheck)

(provide shrink-expr)

(define (value? e)
  (or (boolean? e) (number? e)))

(define (free-vars e)
  (match e
    [(? value? v) empty]
    [(? symbol? id) (list id)]
    [`(if ,e1 ,e2 ,e3)
     (set-union (free-vars e1)
                (free-vars e2)
                (free-vars e3))]
    [`(let ([,ids ,e-vals] ...) ,e-body)
     (set-union (apply set-union (map free-vars e-vals))
                (foldl (λ (id acc) (set-remove acc id))
                       (free-vars e-body)
                       ids))]
    [`(let* ([,id ,e-val] [,ids ,e-vals] ...) ,e-body)
     (free-vars `(let ([,id ,e-val])
                   (let* ,(map list ids e-vals) ,e-body)))]
    [`(let* () ,e-body)
     (free-vars e-body)]
    [`(cond [,e-preds ,e-bodies] ... [else ,e-else])
     (set-union (apply set-union (map free-vars e-preds))
                (apply set-union (map free-vars e-bodies))
                (free-vars e-else))]
    [`(case ,e-pred [(,vals ...) ,e-bodies] ... [else ,e-else])
     (set-union (free-vars e-pred)
                (apply set-union (map free-vars e-bodies))
                (free-vars e-else))]
    [(list (? symbol? p) e-args ...)
     (apply set-union (map free-vars e-args))]))

(define (substitute e id v)
  (let ([sub (λ (e) (substitute e id v))])
    (match e
      [(? value? v) v]
      [(? symbol? sid) (if (symbol=? id sid) v sid)]
      [`(if ,e1 ,e2 ,e3)
       `(if ,(sub e1) ,(sub e2) ,(sub e3))]
      [`(let ([,b-ids ,e-vals] ...) ,e-body)
       `(let ,(map list b-ids (map sub e-vals))
          ,(if (set-member? b-ids id)
               e-body
               (sub e-body)))]
      [`(cond [,e-preds ,e-bodies] ... [else ,e-else])
       `(cond ,@(map list (map sub e-preds) (map sub e-bodies))
              [else ,(sub e-else)])]
      [`(case ,e-pred [(,vals ...) ,e-bodies] ... [else ,e-else])
       `(case ,(substitute e-pred id v)
          ,(map list vals (map sub e-bodies))
          [else ,(sub e-else)])]
      [(list (? symbol? p) e-args ...)
       (cons p (map sub e-args))])))

(define (shrink-expr e)
  (match e
    [(? value? v) empty]
    [(? symbol? id) empty]
    
    [`(if ,e1 ,e2 ,e3)
     (append
      (list e2 e3)
      (map (λ (s) `(if ,s ,e2 ,e3)) (shrink-expr e1))
      (map (λ (s) `(if ,e1 ,s ,e3)) (shrink-expr e2))
      (map (λ (s) `(if ,e1 ,e2 ,s)) (shrink-expr e3)))]

    ;; keep this here to avoid violating pre-fraud+ language expectations
    ;; avoids shrinking single let statements into empty ones
    [`(let ([,id ,e-val]) ,e-body)
     (append
      (cond
        [(not (set-member? (free-vars e-body) id)) (list e-body)]
        [(value? e-val) (list (substitute e-body id e-val))]
        [else empty])
      (map (λ (s) `(let ([,id ,s]) ,e-body)) (shrink-expr e-val))
      (map (λ (s) `(let ([,id ,e-val]) ,s)) (shrink-expr e-body)))]

    [`(let ([,ids ,e-vals] ...) ,e-body)
     (let ([free (free-vars e-body)])
       
       (define (cull/sub-one binds)
         (match binds
           ['() (values '() '())]
           [(cons (list id e) binds)
            (let*-values ([(binds* bodies) (cull/sub-one binds)]
                          [(binds*) (map (curry cons (list id e)) binds*)])
              (cond
                [(not (set-member? free id))
                 (values (cons binds binds*)
                         (cons e-body bodies))]
                [(value? e)
                 (values (cons binds binds*)
                         (cons (substitute e-body id e) bodies))]
                [else (values binds* bodies)]))]))
       
       (append
        (if (set-empty? (set-intersect ids free))
            (list e-body)
            empty)
        (let-values ([(binds* bodies) (cull/sub-one (map list ids e-vals))])
          (for/list ([binds binds*]
                     [body bodies])
            `(let ,binds ,body)))
        (for/list ([new-vals (shrink-one shrink-expr e-vals)])
          `(let ,(map list ids new-vals) ,e-body))
        (for/list ([new-body (shrink-expr e-body)])
          `(let ,(map list ids e-vals) ,new-body))))]

    [`(let* ([,ids ,e-vals] ...) ,e-body)
     (append
      (if (empty? ids)
          (list e-body)
          (list `(let ([,(first ids) ,(first e-vals)])
                   (let* ,(map list (rest ids) (rest e-vals))
                     ,e-body))))
      (for/list ([new-vals (shrink-one shrink-expr e-vals)])
        `(let* ,(map list ids new-vals) ,e-body))
      (for/list ([new-body (shrink-expr e-body)])
        `(let* ,(map list ids e-vals) ,new-body)))]
    
    [`(cond [,e-preds ,e-bodies] ... [else ,e-else])
     (append
      e-bodies
      (list e-else)
      (for/list ([branches (list-cuts (map list e-preds e-bodies))])
        `(cond ,@branches [else ,e-else]))
      (for/list ([new-preds (shrink-one shrink-expr e-preds)])
        `(cond ,@(map list new-preds e-bodies) [else ,e-else]))
      (for/list ([new-bodies (shrink-one shrink-expr e-bodies)])
        `(cond ,@(map list e-preds new-bodies) [else ,e-else]))
      (for/list ([new-else (shrink-expr e-else)])
        `(cond ,@(map list e-preds e-bodies) [else ,new-else])))]

    [`(case ,e-pred [(,vals ...) ,e-bodies] ... [else ,e-else])
     (append
      e-bodies
      (list e-else)
      (for/list ([new-pred (shrink-expr e-pred)])
        `(case ,new-pred ,@(map list vals e-bodies) [else ,e-else]))
      (for/list ([branches (list-cuts (map list vals e-bodies))])
        `(case ,e-pred ,@branches [else ,e-else]))
      (for/list ([new-vals (shrink-one list-cuts vals)])
        `(case ,e-pred ,@(map list new-vals e-bodies) [else ,e-else]))
      (for/list ([new-bodies (shrink-one shrink-expr e-bodies)])
        `(case ,e-pred ,@(map list vals new-bodies) [else ,e-else]))
      (for/list ([new-else (shrink-expr e-else)])
        `(case ,e-pred ,@(map list vals e-bodies) [else ,new-else])))]
    
    [(list (? symbol? p) e-args ...)
     (append
      (if (andmap value? e-args)
          (list (eval (cons p e-args) (make-base-namespace)))
          empty)
      (for/list ([new-args (shrink-one shrink-expr e-args)])
        (cons p new-args)))]))