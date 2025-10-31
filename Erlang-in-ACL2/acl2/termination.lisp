(in-package "ACL2")
(include-book "erl-kont")

; Termination Proof for Apply-k ------------------------------------------------

(set-induction-depth-limit 1)

(defrule integerp-of-natp-powers-of-2
  (implies (and (integerp k) (<= 0 k))
	         (and (integerp (expt 2 k)))))

(defrule powers-of-2->-0 (< 0 (expt 2 k)) :rule-classes (:rewrite :linear))

(encapsulate
  ; Evaluation function and a recognizer for its return value
  (((eval-op * *) => *)
   ((eval-result-p *) => *)
   ((eval-result->klst *) => *)
   ((make-eval-result * *) => *)
   ((erl-result-p *) => *)
   ((erl-result-fix *) => *))
  ; Witness functions
  (local (defun eval-result-p (x)
    (and (consp x)
         (erl-klst-p (cadr x))
         (null (caddr x)))))
  (local (defun eval-result->klst (x) (cadr x)))
  (local (defun make-eval-result (v klst) (list v klst)))
  (local (defun erl-result-p (ps) (consp ps)))
  (local (defun erl-result-fix (ps) (cons ps nil)))

  (local (defun eval-op (k x)
    (if (<= (erl-k->fuel k) 0)
        (make-eval-result x nil)
        (make-eval-result 
          x
          (list (make-erl-k :fuel (1- (erl-k->fuel k)) :kont (erl-k->kont k))
                (make-erl-k :fuel (1- (erl-k->fuel k)) :kont (erl-k->kont k)))))))

  ; Constraints
  (defthm eval-result-of-eval-op
    (implies (erl-k-p k) (eval-result-p (eval-op k x))))
  (defthm eval-op-decreases-fuel
    (implies 
      (and (erl-k-p k) (erl-result-p x))
      (or (null (eval-result->klst (eval-op k x)))
          (and (tuplep 2 (eval-result->klst (eval-op k x)))
               (equal (erl-k->fuel (car (eval-result->klst (eval-op k x)))) 
                      (- (erl-k->fuel k) 1))
               (equal (erl-k->fuel (cadr (eval-result->klst (eval-op k x)))) 
                      (- (erl-k->fuel k) 1))
               (equal (cdr (eval-result->klst (eval-op k x))) 
                      (cons (cadr (eval-result->klst (eval-op k x))) nil))))))
  (defthm erl-result-of-erl-result-fix
    (erl-result-p (erl-result-fix x))))


; The sum of (expt 2 fuel) for all continuations in the list
(define klst-measure-1 ((klst erl-klst-p))
  :returns m
  (if (consp klst)
      (+ (expt 2 (erl-k->fuel (car klst)))
	       (klst-measure-1 (cdr klst)))
      0)
  ///
  ; The sum is an integer
  (local (defrule crock-1
    (implies 
      (integerp (klst-measure-1 (cdr klst)))
	    (integerp (+ (klst-measure-1 (cdr klst)) (expt 2 (erl-k->fuel (car klst))))))
   :in-theory (disable integerp-of-natp-powers-of-2)
   :use((:instance integerp-of-natp-powers-of-2 (k (erl-k->fuel (car klst)))))))
  ; klst-measure-1 is distributive over append
  (local (defrule crock-2
    (implies
      (and klst1 klst2 (erl-klst-p klst1) (erl-klst-p klst2))
      (equal (klst-measure-1 (append klst1 klst2))
             (+ (klst-measure-1 klst1) (klst-measure-1 klst2))))))
  ; klst-measure-1 returns natp
  (more-returns
    (m :name integerp-of-klst-measure-1
       (and (integerp m) (<= 0 m)))
    (m :name posp-of-klst-measure-1
       (<= 0 m)
       :rule-classes (:rewrite :linear)))
  ; klst-measure-1 decreases on (cdr klst)
  (defrule measure-1-when-eval-op-returns-nil
    (implies
      (and klst (erl-klst-p klst))
      (< (klst-measure-1 (cdr klst)) (klst-measure-1 klst))))
  ; klst-measure-1 does not change after non-empty eval-k
  (defrule measure-1-when-eval-op-returns-list
    (implies 
      (and klst
          (erl-result-p x)
          (erl-klst-p klst)
          (not (null (eval-result->klst (eval-op (car klst) x)))))
      (equal (klst-measure-1 (append (eval-result->klst (eval-op (car klst) x)) 
                                     (cdr klst)))
             (klst-measure-1 klst)))
    :do-not-induct t
    :in-theory (disable eval-op-decreases-fuel)
    :use((:instance eval-op-decreases-fuel (k (car klst)) (x x)))))           

; When eval-op returns an empty continuation list, the fuel of (car klst) decreases
(defrule fuel-of-car-when-eval-op-returns-list
  (implies
    (and klst
         (erl-klst-p klst)
         (erl-result-p x)
         (not (null (eval-result->klst (eval-op (car klst) x)))))
    (let ((new-klst (append (eval-result->klst (eval-op (car klst) x)) (cdr klst))))
      (and (consp new-klst)
           (equal (erl-k->fuel (car new-klst)) 
                  (- (erl-k->fuel (car klst)) 1)))))
  :in-theory (disable eval-op-decreases-fuel)
  :use((:instance eval-op-decreases-fuel (k (car klst)))))

; Measure for klst
(define klst-measure ((klst erl-klst-p))
  :returns m
  (list (klst-measure-1 klst)
	      (if (consp klst)
	          (+ 1 (erl-k->fuel (car klst)))
	          0)))

; Properties of the klst-measure
(defret klst-measure-well-formed
  (and (consp m)
       (consp (cdr m))
       (natp (car m))
       (natp (cadr m))
       (not (cddr m))
       (equal (len (klst-measure x)) 2)
       (nat-listp (klst-measure x)))
  :fn klst-measure
  :hints (("Goal" :in-theory (enable klst-measure))))

; Eval-op decreases the klst-measure
(defrule eval-op-decreases-klst-measure
    (b* ((klst (erl-klst-fix klst))
          (x (erl-result-fix x))
         ((if (null klst)) t))
      (l< (klst-measure (append (eval-result->klst (eval-op (car klst) x))
                                (cdr klst)))
          (klst-measure klst)))
  :enable klst-measure
  :use((:instance fuel-of-car-when-eval-op-returns-list 
    (klst (erl-klst-fix klst)) 
    (x (erl-result-fix x)))))
