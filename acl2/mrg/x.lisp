(in-package "ACL2")
(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/top" :dir :system)

(set-induction-depth-limit 1)

(set-well-founded-relation l<)
(fty::deftypes expr
  (fty::defprod expr
    ((filename stringp "")
     (linenum natp :default 0)
     (value value-p))
    :measure (list (acl2-count x) 2)
    )

  (fty::deflist expr-list
    :elt-type expr-p
    :true-listp t
    :measure (list (acl2-count x) 0)
    )

  (fty::deftagsum value
    (:int-const ((val integerp)))
    (:fun-call ((fsym symbolp)
		(args expr-list-p)))
    :measure (list (acl2-count x) 1)))

(defrule car-of-expr-list-fix
  (implies (consp x)
	   (equal (car (expr-list-fix x)) (expr-fix (car x))))
  :expand (expr-list-fix x))

(defrule cdr-of-expr-list-fix
  (equal (cdr (expr-list-fix xl)) (expr-list-fix (cdr xl)))
  :expand (expr-list-fix xl))

; some functions for measuring expr-p, expr-list-p and value-p objects
(defines expr-measure
  :hints(("Goal"  ; for measure theorem
	  :in-theory (enable expr-fix expr->value value-fix value-fun-call->args)))
  (define expr-measure ((x expr-p))
    :returns (m posp)
    :measure (list (acl2-count (expr-fix x)) 2)
    (+ 4 (value-measure (expr->value x))))

  (define expr-list-measure ((xl expr-list-p))
    :returns (m posp)
    :measure (list (acl2-count (expr-list-fix xl)) 0)
    (b* ((xl (expr-list-fix xl))
	 ((if (endp xl)) 1)
	 ((cons hd tl) xl))
      (+ (expr-measure hd) (expr-list-measure tl))))

  (define value-measure ((v value-p))
    :returns (m posp)
    :measure (list (acl2-count (value-fix v)) 1)
    (value-case v
      :int-const 2
      :fun-call (1+ (expr-list-measure v.args))))
  ///
  (defrule expr-measure-of-expr-fix
    (equal (expr-measure (expr-fix x))
	   (expr-measure x))
    :expand (expr-measure x))

  (defrule expr-list-measure-of-expr-list-fix
    (equal (expr-list-measure (expr-list-fix xl))
	   (expr-list-measure xl))
    :expand (expr-list-measure xl))

  (defrule value-measure-of-value-fix
    (equal (value-measure (value-fix v))
	   (value-measure v))
    :expand (value-measure v))

  (defrule expr->value-decreases-measure
    (< (value-measure (expr->value x))
       (expr-measure x)))

  (defrule car-of-expr-list-decreases-measure
    (implies
      (consp x)
      (< (expr-measure (car x)) (expr-list-measure x)))
    :expand ((expr-list-measure x)
	     (expr-measure (car x))))

  (defrule cdr-of-expr-list-decreases-measure
    (implies
      (consp xl)
      (< (expr-list-measure (cdr xl)) (expr-list-measure xl)))
    :expand ((expr-list-measure xl)))

  (defrule value-fun-call->args-decreases-measure
    (< (expr-list-measure (value-fun-call->args v))
       (value-measure v))
    :in-theory (enable value-fun-call->args)))

(set-well-founded-relation o<)

(defines eval-expr
  :verify-guards nil ; We'll verify guards after the :returns theorems are proven
  (define eval-expr ((x expr-p))
    :returns (v integerp)
    :measure (expr-measure x)
    (eval-value (expr->value (expr-fix x))))

  (define eval-expr-list ((xl expr-list-p))
    :returns (vl integer-listp)
    :measure (expr-list-measure xl)
    (b* ((xl (expr-list-fix xl))
	 ((if (endp xl)) nil)
	 ((cons hd tl) xl))
      (cons (eval-expr hd) (eval-expr-list tl))))

  (define eval-value ((v value-p))
    :returns (v2 integerp)
    :measure (value-measure v)
    (let ((v (value-fix v)))
      (value-case v
        :int-const v.val
        :fun-call
          (b* ((args (eval-expr-list v.args))
              ((unless (and (consp args) (consp (cdr args)) (null (cddr args)))) 0)
              ((unless (mbt (integer-listp args))) 0))
            (case v.fsym
              (+ (+ (car args) (cadr args)))
              (- (- (car args) (cadr args)))
              (* (* (car args) (cadr args)))
              (otherwise 0))))))
  ///
  (local (defrule crock-car
    (implies (and (integer-listp x) (consp x) (consp (cdr x)))
	     (acl2-numberp (car x)))))
  (local (defrule crock-cadr
    (implies (and (integer-listp x) (consp x) (consp (cdr x)))
	     (acl2-numberp (cadr x)))))
  (verify-guards eval-expr))


(define one-plus-one ()
  :returns (x expr-p)
  :guard-debug t
  (b* ((fname "imaginary-file")
       (one-value (make-value-int-const :val 1))
       (one (make-expr :filename fname :linenum 0 :value one-value))
       (one-plus-one-value
	 (make-value-fun-call :fsym '+ :args (list one one))))
    (change-expr one :value one-plus-one-value)))

(defrule one-plus-one--equals--two
  (equal (eval-expr (one-plus-one)) 2))

