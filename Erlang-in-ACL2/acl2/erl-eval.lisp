(in-package "ACL2")
(include-book "centaur/fty/top" :DIR :SYSTEM)
(include-book "std/util/top" :DIR :SYSTEM)
(set-induction-depth-limit 1)

(ld "erl-ast.lisp")
(ld "erl-value.lisp")
(ld "erl-kont.lisp")
(ld "eval-theorems.lisp")
(ld "erl-op.lisp")

;; ------------------------------- Erlang Evaluator ----------------------------------------------

(defines eval-expr
  :flag-local nil
  (define eval-expr ((x expr-p) (k erl-k-p) (fuel natp))
    :flag eval
    :returns (v erl-value-p)
    :measure (nfix fuel)
    (b* ((x (expr-fix x))
         (k (erl-k-fix k))
         (fuel (nfix fuel))
         ((if (<= fuel 0)) '(:fault out-of-fuel)))
        (node-case x 
          (:integer (apply-k (make-erl-value-integer :val x.val) k (1- fuel)))
          (:atom    (apply-k (make-erl-value-atom :val x.val) k (1- fuel)))
          (:string  (apply-k (make-erl-value-string :val x.val) k (1- fuel)))
          (:binary-op
            (eval-expr x.left 
                       (make-erl-k-binary-op-expr1 :op x.op 
                                                   :expr2 x.right 
                                                   :k k)
                       (1- fuel)))
          (:fault '(:fault bad-ast))
          (otherwise (apply-k '(:error not-implemented) k (1- fuel))))))
  
  (define apply-k ((val erl-value-p) (k erl-k-p) (fuel natp))
    :flag apply
    :returns (v erl-value-p)
    :measure (nfix fuel)
    (b* ((val (erl-value-fix val))
         (k (erl-k-fix k))
         (fuel (ifix fuel))
         ((if (<= fuel 0)) '(:fault out-of-fuel)))
        (erl-k-case k
          (:init val)
          (:binary-op-expr1
            (eval-expr k.expr2
                       (make-erl-k-binary-op-expr2 :op k.op
                                                   :result val 
                                                   :k k.k)
                       (1- fuel)))
          (:binary-op-expr2
            (case k.op
              (+ (apply-k (erl-add k.result val) k.k (1- fuel)))
              (- (apply-k (erl-sub k.result val) k.k (1- fuel)))
              (* (apply-k (erl-mul k.result val) k.k (1- fuel)))
              (div (apply-k (erl-div k.result val) k.k (1- fuel)))
              (otherwise '(:fault bad-op))))
          (otherwise '(:fault bad-kont))))))


;;-------------------------------------- Theorems --------------------------------------------------

(defun more-fuel-hint (clause)
  (cond 
    ((acl2::occur-lst '(flag-is 'eval) clause)
	   '(:expand ((eval-expr x k 0)
		            (eval-expr x k 1)
		            (eval-expr x k fuel)
		            (eval-expr x k (1+ fuel))
                (eval-expr x k (+ fuel z)))))
	  ((acl2::occur-lst '(flag-is 'apply) clause)
	  '(:expand ((apply-k val k 1)
		           (apply-k val k 0)
		           (apply-k val k fuel)
		           (apply-k val k (1+ fuel))
               (apply-k val k (+ fuel z)))))
	  (t nil)))

(defthm-eval-expr-flag adding-more-fuel-is-good
  (defthm adding-more-fuel-is-good-for-eval
    (implies (and (expr-p x)
		              (erl-k-p k) 
		              (natp fuel)
                  (natp z)
		              (not (equal (erl-value-kind (eval-expr x k fuel)) :fault)))
	           (equal (eval-expr x k fuel)
		                (eval-expr x k (+ fuel z))))
    :flag eval)

  (defthm adding-more-fuel-is-good-for-apply
    (implies (and (erl-value-p val)
	                (erl-k-p k)
	                (natp fuel)
                  (natp z)
	                (not (equal (erl-value-kind (apply-k val k fuel)) :fault)))
             (equal (apply-k val k fuel) (apply-k val k (+ fuel z))))
    :flag apply)
    :hints((more-fuel-hint clause)))

(defrule more-fuel-is-good-for-apply-lemma
  (implies
      (and (erl-value-p val)
	         (erl-k-p k)
	         (natp fuel1)
           (natp fuel2)
           (natp z)
           (equal fuel2 (+ fuel1 z))
	         (not (equal (erl-value-kind (apply-k val k fuel1)) :fault)))
       (equal (apply-k val k fuel2) (apply-k val k fuel1))))

(in-theory (disable adding-more-fuel-is-good-for-apply))
(in-theory (disable more-fuel-is-good-for-apply-lemma))

(defrule more-fuel-is-good-for-apply
  (implies
      (and (erl-value-p val)
        (erl-k-p k)
        (natp fuel1)
        (natp fuel2)
        (> fuel2 fuel1)
        (not (equal (erl-value-kind (apply-k val k fuel1)) :fault)))
      (equal (apply-k val k fuel2) (apply-k val k fuel1)))
  :use ((:instance more-fuel-is-good-for-apply-lemma
          (val val)
          (k k)
          (fuel1 fuel1)
          (fuel2 fuel2)
          (z (- fuel2 fuel1)))))

(defrule more-fuel-is-good-for-eval-lemma
  (implies
      (and (expr-p x)
           (erl-k-p k)
           (natp fuel1)
           (natp fuel2)
           (natp z)
           (equal fuel2 (+ fuel1 z))
	         (not (equal (erl-value-kind (eval-expr x k fuel1)) :fault)))
       (equal (eval-expr x k fuel2) (eval-expr x k fuel1))))

(in-theory (disable adding-more-fuel-is-good-for-eval))
(in-theory (disable more-fuel-is-good-for-eval-lemma))


(defrule more-fuel-is-good-for-eval
  (implies
      (and (expr-p x)
           (erl-k-p k)
           (natp fuel1)
           (natp fuel2)
           (> fuel2 fuel1)
           (not (equal (erl-value-kind (eval-expr x k fuel1)) :fault)))
      (equal (eval-expr x k fuel2) (eval-expr x k fuel1)))
  :use ((:instance more-fuel-is-good-for-eval-lemma
          (x x)
          (k k)
          (fuel1 fuel1)
          (fuel2 fuel2)
          (z (- fuel2 fuel1)))))           

;; ============================================================================================
;; Done till this point
;; ============================================================================================

;; probably need some fuel assertions, relating them to different k


(defrule lemma-init-k-returns-as-is-when-term
  (implies (and (expr-p x) 
                (or (equal (node-kind x) :integer)
                    (equal (node-kind x) :string)
                    (equal (node-kind x) :atom)
                    (equal (node-kind x) :fault))
                (erl-k-p k) 
                (natp fuel)
                (not (equal (erl-value-kind (eval-expr x k fuel)) :fault)))
           (equal (eval-expr x k fuel)
                  (apply-k (eval-expr x :init fuel) k fuel)))
  :expand ((eval-expr x k fuel) 
           (eval-expr x :init fuel)
           (apply-k (erl-value-string (node-string->val x)) '(:init) (+ -1 fuel))
           (apply-k (erl-value-string (node-string->val x)) k 0)
           (apply-k (erl-value-atom (node-atom->val x)) '(:init) (+ -1 fuel))
           (apply-k (erl-value-atom (node-atom->val x)) k 0)
           (apply-k (erl-value-integer (node-integer->val x)) '(:init) (+ -1 fuel))
           (apply-k (erl-value-integer (node-integer->val x)) k 0)))



(defrule lemma-init-k-returns-as-is-binop-step-1
  (implies (and (erl-value-p val) 
                (erl-k-p k)
                (equal k (make-erl-k-binary-op-expr2 :op op :result result :k k_next))
                (natp fuel)
                (not (equal (erl-value-kind (apply-k val k fuel)) :fault)))
           (equal (apply-k val k fuel)
                  (apply-k (apply-k val (make-erl-k-binary-op-expr2 :op op :result result :k :init) fuel) k_next fuel)))
  :expand ())


(defrule init-k-returns-as-is
  (implies (and (expr-p x) 
                (erl-k-p k) 
                (natp fuel)
                (not (equal (erl-value-kind (eval-expr x k fuel)) :fault)))
           (equal (eval-expr x k fuel)
                  (apply-k (eval-expr x :init fuel) k fuel))))


;; TODO: turn the following into test cases
;; AST Examples

'(:integer 1)
'(:unary-op - (:integer 1))

'(:binary-op + (:integer 1) (:integer 2))

'(:binary-op + (:binary-op * (:integer 3) (:integer 4)) (:integer 2))
'(:if  (((cases) (guards (:atom true)) (body :atom true))
        ((cases) (guards (:atom true)) (body :atom false))))



;; Evaluation examples
(eval-expr '(:integer 1) '(:init) 100)
(eval-expr '(:atom abc) '(:init) 100)
(eval-expr '(:string "abc") '(:init) 100)

(eval-expr '(:binary-op + (:integer 1) (:integer 2)) '(:init) 100)

(eval-expr '(:binary-op + (:binary-op * (:integer 3) (:integer 4)) (:integer 2))
           '(:init)
           100)

(eval-expr '(:binary-op div (:integer 10) (:integer 2)) '(:init) 100)
(eval-expr '(:binary-op div (:integer 3) (:integer 2)) '(:init) 100)