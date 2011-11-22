#lang r6rs

(library
 (fk)
 (export)
 (import (rnrs))

 (define-syntax CONS
   (syntax-rules ()
     ((_ a d) (cons a d))))

 (define-syntax inc
   (syntax-rules ()
     ((_ e) (lambdaf@ () e))))

 (define-syntax var
   (syntax-rules ()
     ((_ x) (vector x))))

 (define-syntax var?
   (syntax-rules ()
     ((_ x) (vector? x))))

 (define empty-s '())

 (define ext-s-no-check
   (lambda (x v s)
     (cons (cons x v) s)))

 (define lhs car)

 (define rhs cdr)

 (define walk
   (lambda (v s)
     (cond
       ((var? v)
        (let ((a (assq v s)))
          (cond
            (a (walk (rhs a) s))
            (else v))))
       (else v))))

 (define occurs-check
   (lambda (x v s)
     (let ((v (walk v s)))
       (cond
         ((var? v) (eq? v x))
         ((pair? v)
          (or (occurs-check x (car v) s)
              (occurs-check x (cdr v) s)))
         (else #f)))))

 (define ext-s
   (lambda (x v s)
     (cond
       ((occurs-check x v s) #f)
       (else (ext-s-no-check x v s)))))

 (define unify
   (lambda (u v s)
     (let ((u (walk u s))
           (v (walk v s)))
       (cond
         ((eq? u v) s)
         ((var? u) (cond
                     ((var? v) (ext-s-no-check u v s))
                     (else (ext-s u v s))))
         ((var? v) (ext-s v u s))
         ((and (pair? u) (pair? v))
          (let ((s (unify (car u) (car v) s)))
            (and s (unify (cdr u) (cdr v) s))))
         ((equal? u v) s)
         (else #f)))))

 (define unify-no-check
   (lambda (u v s)
     (let ((u (walk u s))
           (v (walk v s)))
       (cond
         ((eq? u v) s)
         ((var? u) (ext-s-no-check u v s))
         ((var? v) (ext-s-no-check v u s))
         ((and (pair? u) (pair? v))
          (let ((s (unify-no-check (car u) (car v) s)))
            (and s (unify-no-check (cdr u) (cdr v) s))))
         ((equal? u v) s)
         (else #f)))))

 (define reify
   (lambda (v s)
     (let ((v (walk* v s)))
       (walk* v (reify-s v empty-s)))))

 (define walk*
   (lambda (v s)
     (let ((v (walk v s)))
       (cond
         ((var? v) v)
         ((pair? v) (cons (walk* (car v) s)
                          (walk* (cdr v) s)))
         (else v)))))

 (define reify-name
   (lambda (n)
     (string->symbol (string-append "_." (number->string n)))))

 (define reify-s
   (lambda (v s)
     (let ((v (walk v s)))
       (cond
         ((var? v) (ext-s v (reify-name (length s)) s))
         ((pair? v) (reify-s (cdr v) (reify-s (car v) s)))
         (else s)))))

 (define-syntax lambdag@
   (syntax-rules ()
     ((_ (s) e) (lambda (s) e))))

 (define-syntax lambdaf@
   (syntax-rules ()
     ((_ () e) (lambda () e))))

 (define succeed
   (lambdag@ (a) a))

 (define fail
   (lambdag@ (a) (mzero)))

 (define-syntax mzero
   (syntax-rules ()
     ((_) #f)))

 (define-syntax unit
   (syntax-rules ()
     ((_ a) a)))

 (define-syntax choice
   (syntax-rules ()
     ((_ a f) (cons a f))))

 (define-syntax ==
   (syntax-rules ()
     ((_ u v)
      (lambdag@ (a)
        (cond
          ((unify u v a) => (lambda (a) (unit a)))
          (else (mzero)))))))

 (define-syntax ==-no-check
   (syntax-rules ()
     ((_ u v)
      (lambdag@ (a)
        (cond
          ((unify-no-check u v a) => (lambda (a) (unit a)))
          (else (mzero)))))))

 (define-syntax case-inf  ;;; changed.
   (syntax-rules ()
     ((_ e (() e0) ((fp) e1) ((gp app) e2) ((ap) e3) ((a f) e4))
      (let ((a-inf e))
        (cond
          ((not a-inf) e0)
          ((procedure? a-inf) (let ((fp a-inf)) e1))
          ((and (pair? a-inf) (procedure? (car a-inf)))
           (let ((gp (car a-inf)) (app (cdr a-inf))) e2))
          ((and (pair? a-inf) (procedure? (cdr a-inf)))
           (let ((a (car a-inf)) (f (cdr a-inf))) e4))
          (else (let ((ap a-inf)) e3)))))))

 (define-syntax run ;;; changed
   (syntax-rules ()
     ((_ n (x) g0 g ...)
      (let ((x (var 'x)))
        (map (lambda (a) (reify x a))
             (take n
                   (lambdaf@ ()
                     ((fresh () g0 g ...) empty-s))))))))

 (define take ;;; changed
   (lambda (n f)
     (display "take: ") (display (f)) (display "\n")
     (if (and n (zero? n))
         '()
         (case-inf (f)
           (() '())
           ((f) (take n f))
           ((gp ap) (take n (lambda () (bind ap gp))))
           ((a) (list a))
           ((a f) (cons a (take (and n (- n 1)) f)))))))

 (define-syntax fresh ;;; changed
   (syntax-rules ()
     ((_ (x ...) g0 g ...)
      (lambdag@ (a)
        (let ((gq (lambda (a)
                    (let ((x (var 'x)) ...)
                      (let ((gp (lambdag@ (a) (bind* (g0 a) g ...))))
                        (CONS gp (unit a)))))))
          (inc (CONS gq a)))))))

 (define-syntax fresh* ;;; added
   (syntax-rules ()
     ((_ (x ...) g0 g1 ...)
      (lambdag@ (a)
        (inc
         (let ((x (var 'x)) ...)
           (bind-seq* (bind a (take* g0)) g1 ...)))))))

 (define-syntax bind* ;;; changed
   (syntax-rules ()
     ((_ e) e)
     ((_ e g0 g1 ...)
      (let ((gq (lambdag@ (a) (bind* (g0 a) g1 ...))))
        (CONS gq e)))))

 (define-syntax bind-seq* ;;; added
   (syntax-rules ()
     ((_ e) e)
     ((_ e g0 g1 ...)
      (bind-seq* (bind e g0) g1 ...))))

 (define bind ;;; changed
   (lambda (a-inf g)
     (case-inf a-inf
       (() (mzero))
       ((f) (inc (bind (f) g)))
       ((gp ap) (CONS gp (inc (bind ap g))))
       ((a) (g a))
       ((a f) (mplus (g a) (lambdaf@ () (bind (f) g)))))))

 (define-syntax conde ;;; changed
   (syntax-rules ()
     ((_ (g0 g ...) (g1 gp ...) ...)
      (lambdag@ (a)
        (let ((gq (lambda (a)
                    (mplus* ((fresh () g0 g ...) a)
                            ((fresh () g1 gp ...) a)
                            ...))))
          (inc (CONS gq (unit a))))))))

 (define-syntax mplus*
   (syntax-rules ()
     ((_ e) e)
     ((_ e0 e ...) (mplus e0 (lambdaf@ () (mplus* e ...))))))

 (define mplus ;;; changed
   (lambda (a-inf f)
     (case-inf a-inf
       (() (f))
       ((fp) (inc (mplus (f) fp)))
       ((gp ap) (inc (mplus (f) (lambdaf@ () (bind ap gp)))))
       ((a) (choice a f))
       ((a fp) (choice a (lambdaf@ () (mplus (f) fp)))))))

 (define take*
   (lambda (g)
     (lambdag@ (a)
       (force* (g a)))))

 (define force* ;;; added
   (lambda (a-inf)
     (case-inf a-inf
       (() (mzero))
       ((f) (force* (f)))
       ((gp ap) (force* (bind ap gp)))
       ((a) a)
       ((a f) (choice a (lambdaf@ () (force* (f))))))))
 )
