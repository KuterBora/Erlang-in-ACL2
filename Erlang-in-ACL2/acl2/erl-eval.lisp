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
          (otherwise '(:fault not-implemented)))))
  
  (define apply-k ((val erl-value-p) (k erl-k-p) (fuel natp))
    :flag apply
    :returns (v erl-value-p)
    :measure (nfix fuel)
    (b* ((val (erl-value-fix val))
         (k (erl-k-fix k))
         (fuel (ifix fuel))
         ((if (<= fuel 0)) '(:fault out-of-fuel))
         ((if (equal (erl-value-kind val) :fault)) val))
        (erl-k-case k
          (:init val)
          (:binary-op-expr1
            (eval-expr k.expr2
                       (make-erl-k-binary-op-expr2 :op k.op
                                                   :result val 
                                                   :k k.k)
                       (1- fuel)))
          (:binary-op-expr2 (apply-k (apply-erl-binop k.op k.result val) k.k (1- fuel)))
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

(defrule lemma-init-k-returns-as-is-when-term
  (implies (and (expr-p x) 
                (or (equal (node-kind x) :integer)
                    (equal (node-kind x) :string)
                    (equal (node-kind x) :atom)
                    (equal (node-kind x) :fault)
                    (equal (node-kind x) :error))
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

(defrule lemma-init-k-returns-as-is-binop-step-1.1
  (implies (and (erl-value-p val) 
                (erl-k-p k)
                (equal (erl-k-kind k) :binary-op-expr2)
                (natp fuel)
                (not (equal (erl-value-kind (apply-k val k fuel)) :fault)))
           (let ((op (erl-k-binary-op-expr2->op k))
                 (result (erl-k-binary-op-expr2->result k))
                 (k_next (erl-k-binary-op-expr2->k k)))
                (equal (apply-k val k fuel)
                       (apply-k (apply-k val (make-erl-k-binary-op-expr2 :op op :result result :k :init) fuel) k_next fuel))))
  :expand ((apply-k val k fuel)
           (apply-k val (make-erl-k-binary-op-expr2 :op op :result result :k :init) fuel)
           (APPLY-K (APPLY-ERL-BINOP (ERL-K-BINARY-OP-EXPR2->OP K) (ERL-K-BINARY-OP-EXPR2->RESULT K) VAL) (ERL-K-BINARY-OP-EXPR2->K K) (+ -1 FUEL))
           (APPLY-K VAL (ERL-K-BINARY-OP-EXPR2 (ERL-K-BINARY-OP-EXPR2->OP K) (ERL-K-BINARY-OP-EXPR2->RESULT K) NIL '(:INIT)) FUEL)
           (APPLY-K (APPLY-ERL-BINOP (ERL-K-BINARY-OP-EXPR2->OP K) (ERL-K-BINARY-OP-EXPR2->RESULT K) VAL) '(:INIT) (+ -1 FUEL))))

;; ============================================================================================
;; Done till this point
;; ============================================================================================

; 1/10'''
; Subgoal *1/4.42'
(in-theory (disable more-fuel-is-good-for-apply))

(defrule fuel-good
  (implies (and (erl-value-p val)
                (erl-k-p k)
                (natp (+ z fuel))
                (integerp z)
                (< z 0)
                (natp fuel)
                (not (equal (erl-value-kind (apply-k val k (+ z fuel))) :fault)))
           (equal (apply-k val k (+ z fuel)) (apply-k val k fuel)))
  :use ((:instance more-fuel-is-good-for-apply
          (val val)
          (k k)
          (fuel1 (+ z fuel))
          (fuel2 fuel))))


(defrule stupid-x
  (implies (and ())
           ()))

(defun step1-hint (clause)
  (cond 
    ((acl2::occur-lst '(flag-is 'eval) clause)
	   '(:expand ((eval-expr x k fuel)
                (EVAL-EXPR X K 0)
                    )))
	  ((acl2::occur-lst '(flag-is 'apply) clause)
	  '(:expand ((APPLY-K VAL K FUEL)
               (APPLY-K VAL K 0)
               (APPLY-K (APPLY-ERL-BINOP (ERL-K-BINARY-OP-EXPR2->OP K) (ERL-K-BINARY-OP-EXPR2->RESULT K) VAL) (ERL-K-BINARY-OP-EXPR2->K K) (+ -1 FUEL))
               (APPLY-K VAL (ERL-K-BINARY-OP-EXPR2 (ERL-K-BINARY-OP-EXPR2->OP K) (ERL-K-BINARY-OP-EXPR2->RESULT K) NIL '(:INIT)) FUEL)
               (APPLY-K (APPLY-ERL-BINOP (ERL-K-BINARY-OP-EXPR2->OP K) (ERL-K-BINARY-OP-EXPR2->RESULT K) VAL) '(:INIT) (+ -1 FUEL))
               (APPLY-K VAL (ERL-K-BINARY-OP-EXPR1 (ERL-K-BINARY-OP-EXPR1->OP K) (ERL-K-BINARY-OP-EXPR1->EXPR2 K) NIL '(:INIT)) FUEL)
               (EVAL-EXPR (ERL-K-BINARY-OP-EXPR1->EXPR2 K) (ERL-K-BINARY-OP-EXPR2 (ERL-K-BINARY-OP-EXPR1->OP K) VAL NIL (ERL-K-BINARY-OP-EXPR1->K K)) (+ -1 FUEL))
               (EVAL-EXPR (ERL-K-BINARY-OP-EXPR1->EXPR2 K) (ERL-K-BINARY-OP-EXPR2 (ERL-K-BINARY-OP-EXPR1->OP K) VAL NIL '(:INIT)) (+ -1 FUEL))
               (APPLY-K '(:FAULT OUT-OF-FUEL) (ERL-K-BINARY-OP-EXPR1->K K) 2)
               (EVAL-EXPR (ERL-K-BINARY-OP-EXPR1->EXPR2 K) :INIT 1)
               (APPLY-K '(:FAULT OUT-OF-FUEL) (ERL-K-BINARY-OP-EXPR2 (ERL-K-BINARY-OP-EXPR1->OP K) VAL NIL (ERL-K-BINARY-OP-EXPR1->K K)) 1)
               (EVAL-EXPR (ERL-K-BINARY-OP-EXPR1->EXPR2 K) :INIT (+ -1 FUEL))
               (APPLY-K '(:FAULT OUT-OF-FUEL) (ERL-K-BINARY-OP-EXPR1->K K) (+ -1 FUEL)) 
              ;; integer
               (APPLY-K (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (ERL-K-BINARY-OP-EXPR1->EXPR2 K))) (ERL-K-BINARY-OP-EXPR2 (ERL-K-BINARY-OP-EXPR1->OP K) VAL NIL '(:INIT)) (+ -2 FUEL))
               (APPLY-K (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (ERL-K-BINARY-OP-EXPR1->EXPR2 K))) '(:INIT) 0)
               (APPLY-K (APPLY-ERL-BINOP (ERL-K-BINARY-OP-EXPR1->OP K) VAL (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (ERL-K-BINARY-OP-EXPR1->EXPR2 K)))) '(:INIT) (+ -3 FUEL)) 
               (APPLY-K (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (ERL-K-BINARY-OP-EXPR1->EXPR2 K))) (ERL-K-BINARY-OP-EXPR2 (ERL-K-BINARY-OP-EXPR1->OP K) VAL NIL (ERL-K-BINARY-OP-EXPR1->K K)) FUEL)
              ;;atom
               (APPLY-K (ERL-VALUE-ATOM (NODE-ATOM->VAL (ERL-K-BINARY-OP-EXPR1->EXPR2 K))) (ERL-K-BINARY-OP-EXPR2 (ERL-K-BINARY-OP-EXPR1->OP K) VAL NIL '(:INIT)) (+ -2 FUEL))
               (APPLY-K (ERL-VALUE-ATOM (NODE-ATOM->VAL (ERL-K-BINARY-OP-EXPR1->EXPR2 K))) '(:INIT) 0)
               (APPLY-K (APPLY-ERL-BINOP (ERL-K-BINARY-OP-EXPR1->OP K) VAL (ERL-VALUE-ATOM (NODE-ATOM->VAL (ERL-K-BINARY-OP-EXPR1->EXPR2 K)))) '(:INIT) (+ -3 FUEL)) 
               (APPLY-K (ERL-VALUE-ATOM (NODE-ATOM->VAL (ERL-K-BINARY-OP-EXPR1->EXPR2 K))) (ERL-K-BINARY-OP-EXPR2 (ERL-K-BINARY-OP-EXPR1->OP K) VAL NIL (ERL-K-BINARY-OP-EXPR1->K K)) FUEL)

              ;;string
               (APPLY-K (ERL-VALUE-STRING (NODE-STRING->VAL (ERL-K-BINARY-OP-EXPR1->EXPR2 K))) (ERL-K-BINARY-OP-EXPR2 (ERL-K-BINARY-OP-EXPR1->OP K) VAL NIL '(:INIT)) (+ -2 FUEL))
               (APPLY-K (ERL-VALUE-STRING (NODE-STRING->VAL (ERL-K-BINARY-OP-EXPR1->EXPR2 K))) '(:INIT) 0)
               (APPLY-K (APPLY-ERL-BINOP (ERL-K-BINARY-OP-EXPR1->OP K) VAL (ERL-VALUE-STRING (NODE-STRING->VAL (ERL-K-BINARY-OP-EXPR1->EXPR2 K)))) '(:INIT) (+ -3 FUEL)) 
               (APPLY-K (ERL-VALUE-STRING (NODE-STRING->VAL (ERL-K-BINARY-OP-EXPR1->EXPR2 K))) (ERL-K-BINARY-OP-EXPR2 (ERL-K-BINARY-OP-EXPR1->OP K) VAL NIL (ERL-K-BINARY-OP-EXPR1->K K)) FUEL)

              ;; new
              (APPLY-K VAL K FUEL)
              (APPLY-K VAL :INIT FUEL)
              (APPLY-K (APPLY-ERL-BINOP (ERL-K-BINARY-OP-EXPR2->OP K) (ERL-K-BINARY-OP-EXPR2->RESULT K) VAL) (ERL-K-BINARY-OP-EXPR2->K K) FUEL)
              (EVAL-EXPR (ERL-K-BINARY-OP-EXPR1->EXPR2 K) (ERL-K-BINARY-OP-EXPR2 (ERL-K-BINARY-OP-EXPR1->OP K) VAL NIL (ERL-K-BINARY-OP-EXPR1->K K)) 0)
              (EVAL-EXPR (ERL-K-BINARY-OP-EXPR1->EXPR2 K) (ERL-K-BINARY-OP-EXPR2 (ERL-K-BINARY-OP-EXPR1->OP K) VAL NIL '(:INIT)) 0)

              )))
	  (t nil)))

(defthm-eval-expr-flag init-k-returns-as-is-binop
  (defthm init-k-returns-as-is-binop-1-eval
    (implies (and (expr-p x) 
                  (erl-k-p k)
                  (equal (erl-k-kind k) :binary-op-expr2)
                  (natp fuel)
                  (not (equal (erl-value-kind (eval-expr x k fuel)) :fault)))
           (let ((op (erl-k-binary-op-expr2->op k))
                 (result (erl-k-binary-op-expr2->result k))
                 (k_next (erl-k-binary-op-expr2->k k)))
                (equal (eval-expr x k fuel)
                       (apply-k (eval-expr x (make-erl-k-binary-op-expr2 :op op :result result :k :init) fuel) k_next fuel))))
    :flag eval)
  (defthm init-k-returns-as-is-binop-2-eval
    (implies (and (expr-p x) 
                  (erl-k-p k)
                  (equal (erl-k-kind k) :binary-op-expr1)
                  (natp fuel)
                  (not (equal (erl-value-kind (eval-expr x k fuel)) :fault)))
           (let ((op (erl-k-binary-op-expr1->op k))
                 (expr2 (erl-k-binary-op-expr1->expr2 k))
                 (k_next (erl-k-binary-op-expr1->k k)))
                (equal (eval-expr x k fuel)
                       (apply-k (eval-expr x (make-erl-k-binary-op-expr1 :op op :expr2 expr2 :k :init) fuel) k_next fuel))))
    :flag eval)

  (defthm init-k-returns-as-is-binop-1-apply
    (implies (and (erl-value-p val) 
                (erl-k-p k)
                (equal (erl-k-kind k) :binary-op-expr2)
                (natp fuel)
                (not (equal (erl-value-kind (apply-k val k fuel)) :fault)))
           (let ((op (erl-k-binary-op-expr2->op k))
                 (result (erl-k-binary-op-expr2->result k))
                 (k_next (erl-k-binary-op-expr2->k k)))
                (equal (apply-k val k fuel)
                       (apply-k (apply-k val (make-erl-k-binary-op-expr2 :op op :result result :k :init) fuel) k_next fuel))))
    :flag apply)
  (defthm init-k-returns-as-is-binop-1-apply
    (implies (and (erl-value-p val) 
                (erl-k-p k)
                (equal (erl-k-kind k) :binary-op-expr1)
                (natp fuel)
                (not (equal (erl-value-kind (apply-k val k fuel)) :fault)))
           (let ((op (erl-k-binary-op-expr1->op k))
                 (expr2 (erl-k-binary-op-expr1->expr2 k))
                 (k_next (erl-k-binary-op-expr1->k k)))
                (equal (apply-k val k fuel)
                       (apply-k (apply-k val (make-erl-k-binary-op-expr1 :op op :expr2 expr2 :k :init) fuel) k_next fuel))))
    :flag apply)
  
  (defthm init-k-returns-as-is-apply
    (implies (and (erl-value-p val) 
                  (erl-k-p k)
                  (natp fuel)
                  (not (equal (erl-value-kind (apply-k val k fuel)) :fault)))
             (equal (apply-k val k fuel)
                    (apply-k (apply-k val :init fuel) k fuel)))
    :flag apply)
  (defthm init-k-returns-as-is-eval
    (implies (and (expr-p x) 
                  (erl-k-p k)
                  (natp fuel)
                  (not (equal (erl-value-kind (eval-expr x k fuel)) :fault)))
             (equal (eval-expr x k fuel)
                    (apply-k (eval-expr x :init fuel) k fuel)))
    :flag eval)
  
  :hints((step1-hint clause)))








