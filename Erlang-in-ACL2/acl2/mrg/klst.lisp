(in-package "ACL2")

(include-book "std/util/top" :dir :system)

(set-induction-depth-limit 1)

(defrule integerp-of-natp-powers-of-2
  (implies (and (integerp k) (<= 0 k))
	   (and (integerp (expt 2 k)))))

(defrule powers-of-2->-0 (< 0 (expt 2 k)) :rule-classes (:rewrite :linear))

(encapsulate
  (((k-p *) => *)       ; recognizer for continuations
   ((k->fuel *) => *)   ; the fuel for this continuation
   ((k-list-p *) => *)  ; recognizer for lists of continuations
   ((k-list-op *) => *)) ;

  ; witness functions
  (local (defun k-p (x) (posp x)))
  (local (defun k->fuel (k) (pos-fix k)))
  (local (defun k-list-p (x)
    (if (consp x)
      (and (k-p (car x)) (k-list-p (cdr x)))
      (null x))))
  (local (defun k-list-op (klst) (cdr klst)))

  ; constraints
  (defthm booleanp-of-k-p (booleanp (k-p x)))
  (defthm integerp-of-k->fuel (integerp (k->fuel k)))
  (defthm k->fuel->-0 (< 0 (k->fuel k)))
  (defthm booleanp-of-k-list-p (booleanp (k-list-p x)))
  (defthm true-listp-when-k-list-p
    (implies (k-list-p klst) (true-listp klst)))
  (defthm car-when-k-listp
    (implies (and klst (k-list-p klst)) (k-p (car klst))))
  (defthm cdr-when-k-listp
    (implies (k-list-p klst) (k-list-p (cdr klst))))
  (defthm k-list-p-of-cons
    (implies (and (k-p k) (k-list-p klst))
	     (k-list-p (cons k klst))))
  (defthm k-list-p-k-list-op
    (implies (k-list-p klst) (k-list-p (k-list-op klst))))
  (defthm constraint-for-k-list-op
    (implies
      (and klst (k-list-p klst))
      (let ((y (k-list-op klst)))
        (or (equal y (cdr klst))
	    (and (consp y)
		 (equal (k->fuel (car y)) (- (k->fuel (car klst)) 1))
		 (consp (cdr y))
	         (equal (k->fuel (cadr y)) (- (k->fuel (car klst)) 1))
	         (equal (cddr y) (cdr klst))))))))

(local (defrule consp-when-k-list-p-and-not-nil
    (implies (and klst (k-list-p klst)) (consp klst))
    :cases ((true-listp klst))))

(define k-list-measure-1 ((klst k-list-p))
  :returns m
  (if (consp klst)
      (+ (expt 2 (k->fuel (car klst)))
	 (k-list-measure-1 (cdr klst)))
      0)
  ///
  (local (defrule crock-1
    (implies (integerp (k-list-measure-1 (cdr klst)))
	     (integerp
	       (+ (k-list-measure-1 (cdr klst))
		  (expt 2 (k->fuel (car klst))))))
   :in-theory (disable integerp-of-natp-powers-of-2)
   :use((:instance integerp-of-natp-powers-of-2 (k (k->fuel (car klst)))))))
  (more-returns
    (m :name integerp-of-k-list-measure-1
       (and (integerp m) (<= 0 m)))
    (m :name posp-of-k-list-measure-1
       (<= 0 m)
       :rule-classes (:rewrite :linear)))
  (defrule measure-1-when-k-list-op-is-cdr
    (implies
      (and klst (k-list-p klst))
      (< (k-list-measure-1 (cdr klst)) (k-list-measure-1 klst))))
  (defrule measure-1-when-k-list-op-is-not-cdr
    (implies
      (and klst (k-list-p klst) (not (equal (k-list-op klst) (cdr klst))))
      (= (k-list-measure-1 (k-list-op klst)) (k-list-measure-1 klst)))
    :do-not-induct t
    :in-theory (disable constraint-for-k-list-op)
    :use((:instance constraint-for-k-list-op))))

(defrule fuel-of-car-when-k-list-op-is-not-cdr
  (implies
    (and klst (k-list-p klst) (not (equal (k-list-op klst) (cdr klst))))
    (and (consp (k-list-op klst))
	 (= (k->fuel (car (k-list-op klst))) (- (k->fuel (car klst)) 1))))
  :in-theory (disable constraint-for-k-list-op)
  :use((:instance constraint-for-k-list-op)))

(define k-list-measure-p (m)
  :returns (ok booleanp)
  (and (consp m)
       (consp (cdr m))
       (natp (car m))
       (natp (cadr m))
       (not (cddr m))))

(local (in-theory (enable k-list-measure-p)))
(define k-list-measure ((klst k-list-p))
  :returns (m k-list-measure-p)
  (list (k-list-measure-1 klst)
	(if (consp klst)
	  (k->fuel (car klst))
	  0)))

(local (in-theory (enable k-list-measure)))
(defrule k-list-op-decreases-k-list-measure
  (implies (and klst (k-list-p klst))
	   (l< (k-list-measure (k-list-op klst))
	       (k-list-measure klst)))
  :cases ((equal (k-list-op klst) (cdr klst)))
  :prep-lemmas(
    (defrule lemma-1
      (implies (and klst (k-list-p klst) (equal (k-list-op klst) (cdr klst)))
	       (l< (k-list-measure (k-list-op klst))
		   (k-list-measure klst))))
    (defrule lemma-2
      (implies (and klst (k-list-p klst) (not (equal (k-list-op klst) (cdr klst))))
	       (l< (k-list-measure (k-list-op klst))
		   (k-list-measure klst))))))
