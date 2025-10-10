(in-package "ACL2")
(include-book "std/util/top" :dir :system)
(set-induction-depth-limit 1)

;; Theorems to help prove termination of apply-k

(defrule integerp-of-natp-powers-of-2
  (implies (and (integerp k) (<= 0 k))
	         (and (integerp (expt 2 k)))))

(defrule powers-of-2->-0 (< 0 (expt 2 k)) :rule-classes (:rewrite :linear))

;; calls to eval-k either return a tuple of two contunuations, or an empty list
(defret eval-k-decreases-fuel
  :hyp (and (erl-k-p k) (erl-value-p val))
  (b* ((klst (erl-val-klst->klst kv)))
      (or (null klst)
          (and (tuplep 2 klst)
               (equal (erl-k->fuel (car klst)) (- (erl-k->fuel k) 1))
               (equal (erl-k->fuel (cadr klst)) (- (erl-k->fuel k) 1))
               (equal (cdr klst) (cons (cadr klst) nil)))))
  :fn eval-k
  :hints (("Goal" :in-theory (enable eval-k))))

;; the sum of (expt 2 fuel) for all continuations in the list
(define k-list-measure-1 ((klst erl-k-list-p))
  :returns m
  (if (consp klst)
      (+ (expt 2 (erl-k->fuel (car klst)))
	       (k-list-measure-1 (cdr klst)))
      0)
  ///
  ;; the sum is an integer
  (local (defrule crock-1
    (implies 
      (integerp (k-list-measure-1 (cdr klst)))
	    (integerp (+ (k-list-measure-1 (cdr klst)) (expt 2 (erl-k->fuel (car klst))))))
   :in-theory (disable integerp-of-natp-powers-of-2)
   :use((:instance integerp-of-natp-powers-of-2 (k (erl-k->fuel (car klst)))))))
  ;; k-list-measure-1 is distributive over append
  (local (defrule crock-2
    (implies
      (and klst1 klst 2 (erl-k-list-p klst1) (erl-k-list-p klst2))
      (equal (k-list-measure-1 (append klst1 klst2))
             (+ (k-list-measure-1 klst1) (k-list-measure-1 klst2))))))
  ;; k-list-measure-1 returns natp
  (more-returns
    (m :name integerp-of-k-list-measure-1
       (and (integerp m) (<= 0 m)))
    (m :name posp-of-k-list-measure-1
       (<= 0 m)
       :rule-classes (:rewrite :linear)))
  ;; k-list-measure-1 decreases on (cdr klst)
  (defrule measure-1-when-eval-k-returns-nil
    (implies
      (and klst (erl-k-list-p klst))
      (< (k-list-measure-1 (cdr klst)) (k-list-measure-1 klst))))
  ;; k-list-measure-1 does not change after non-empty eval-k
  (defrule measure-1-when-eval-k-returns-list
    (implies 
      (and klst
          (erl-k-list-p klst)
          (erl-value-p val)
          (not (null (erl-val-klst->klst (eval-k (car klst) val)))))
      (equal (k-list-measure-1 (append (erl-val-klst->klst (eval-k (car klst) val)) (cdr klst)))
             (k-list-measure-1 klst)))
    :do-not-induct t
    :in-theory (disable eval-k-decreases-fuel)
    :use((:instance eval-k-decreases-fuel (k (car klst)) (val val)))))

;; when eval-k returns nil continuation, the fuel of (car klat) decreases
(defrule fuel-of-car-when-eval-k-returns-list
  (implies
    (and klst
         (erl-k-list-p klst)
         (erl-value-p val)
         (not (null (erl-val-klst->klst (eval-k (car klst) val)))))
    (let ((new-klst (append (erl-val-klst->klst (eval-k (car klst) val)) (cdr klst))))
      (and (consp new-klst)
           (equal (erl-k->fuel (car new-klst)) 
                  (- (erl-k->fuel (car klst)) 1)))))
  :in-theory (disable eval-k-decreases-fuel)
  :use((:instance eval-k-decreases-fuel (k (car klst)))))

;; measure for klst
(define k-list-measure ((klst erl-k-list-p))
  :returns m
  (list (k-list-measure-1 klst)
	      (if (consp klst)
	          (+ 1 (erl-k->fuel (car klst)))
	          0)))

;; propeties of the result of k-list-measure
(defret k-list-measure-well-formed
  (and (consp m)
       (consp (cdr m))
       (natp (car m))
       (natp (cadr m))
       (not (cddr m))
       (equal (len (k-list-measure x)) 2)
       (nat-listp (k-list-measure x)))
  :fn k-list-measure
  :hints (("Goal" :in-theory (enable eval-k))))

;; show that eval-k decrases k-list-measure
(local (in-theory (enable k-list-measure)))
(defrule eval-k-decreases-k-list-measure
    (b* ((klst (erl-k-list-fix klst))
         (val (erl-value-fix val))
         ((if (null klst)) t))
      (l< (k-list-measure (append (erl-val-klst->klst (eval-k (car klst) val))
                                  (cdr klst)))
          (k-list-measure klst)))
  :use((:instance fuel-of-car-when-eval-k-returns-list (klst (erl-k-list-fix klst)) (val (erl-value-fix val)))))