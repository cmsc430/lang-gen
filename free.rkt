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
     (set-union (apply set-union '() (map free-vars e-vals))
                (set-subtract (free-vars e-body) ids))]
    [`(let* ([,id ,e-val] [,ids ,e-vals] ...) ,e-body)
     (free-vars `(let ([,id ,e-val])
                   (let* ,(map list ids e-vals) ,e-body)))]
    [`(let* () ,e-body)
     (free-vars e-body)]
    [`(cond [,e-preds ,e-bodies] ... [else ,e-else])
     (set-union (apply set-union '() (map free-vars e-preds))
                (apply set-union '() (map free-vars e-bodies))
                (free-vars e-else))]
    [`(case ,e-pred [(,vals ...) ,e-bodies] ... [else ,e-else])
     (set-union (free-vars e-pred)
                (apply set-union '() (map free-vars e-bodies))
                (free-vars e-else))]
    [`(begin ,e1 ,e2) (set-union (free-vars e1) (free-vars e2))]
    [(list (? symbol? p) e-args ...)
     (apply set-union '() (map free-vars e-args))]))