#lang racket

(provide free-vars)

(define (value? v)
  (or (integer? v)
      (boolean? v)
      (char? v)
      (equal? 'eof v)
      (equal? '(void) v)
      (equal? ''() v)))

(define (free-vars e)
  (match e
    [(? value? v) empty]
    [(? symbol? id) (list id)]
    [`(if ,e1 ,e2 ,e3)
     (set-union (free-vars e1)
                (free-vars e2)
                (free-vars e3))]
    [`(let ([,ids ,e-vals] ...) ,e-body)
     (apply set-union (set-subtract (free-vars e-body) ids) (map free-vars e-vals))]
    [`(let* ([,id ,e-val] [,ids ,e-vals] ...) ,e-body)
     (free-vars `(let ([,id ,e-val])
                   (let* ,(map list ids e-vals) ,e-body)))]
    [`(let* () ,e-body)
     (free-vars e-body)]
    [`(cond [,e-preds ,e-bodies] ... [else ,e-else])
     (apply set-union (free-vars e-else) (map free-vars (append e-preds e-bodies)))]
    [`(case ,e-pred [(,vals ...) ,e-bodies] ... [else ,e-else])
     (apply set-union (free-vars e-pred) (free-vars e-else)
            (map free-vars e-bodies))]
    [`(begin ,e1 ,e2) (set-union (free-vars e1) (free-vars e2))]
    [(list (? symbol? p) e-args ...)
     (apply set-union '() (map free-vars e-args))]))