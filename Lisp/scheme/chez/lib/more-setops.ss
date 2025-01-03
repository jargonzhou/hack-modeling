(library (more-setops)
  (export quoted-set set-cons set-remove)
  (import (list-tools setops) (rnrs base) (rnrs syntax-case))
  
  (define-syntax quoted-set
    (lambda (x)
      (syntax-case x ()
        [(k elt ...)
          #`(quote
            #,(datum->syntax #'k
              (list->set
                (syntax->datum #'(elt ...)))))])))

  (define set-cons
    (lambda (opt optset)
      (union (set opt) optset)))

  (define set-remove
    (lambda (opt optset)
      (difference optset (set opt)))))