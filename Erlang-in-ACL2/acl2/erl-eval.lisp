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

;; ============================================================================================
;; Done till this point
;; ============================================================================================

(defrule lemma-init-k-returns-as-is-binop-expr2
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

;; may need this in main goal (expr1)
(in-theory (disable lemma-init-k-returns-as-is-when-term))
(in-theory (disable lemma-init-k-returns-as-is-binop-expr2))

; (defrule lemma-init-k-returns-as-is-binop-expr2-implies
;   (implies (and (erl-value-p val) 
;                 (erl-k-p k)
;                 (equal (erl-k-kind k) :binary-op-expr2)
;                 (natp fuel)
;                 (not (equal (erl-value-kind (apply-k val k fuel)) :fault)))
;            (let ((op (erl-k-binary-op-expr2->op k))
;                  (result (erl-k-binary-op-expr2->result k))
;                  (k_next (erl-k-binary-op-expr2->k k)))
;                 (equal (apply-k val k fuel)
;                        (apply-k (apply-k val (make-erl-k-binary-op-expr2 :op op :result result :k :init) fuel) k_next fuel)))))


(defrule crock-1
  (implies (and (erl-k-p k) (equal (erl-k-kind k) :binary-op-expr1))
           (and (equal (erl-value-kind (APPLY-K x k 1)) :fault)
                (equal (erl-value-kind (APPLY-K x k 0)) :fault)))
  :expand ((apply-k x k 1) (apply-k x k 0))
  :enable eval-expr)


(defrule crock-2
  (implies (<= fuel 0)
           (equal (erl-value-kind (eval-expr x k fuel)) :fault))
  :expand (eval-expr x k fuel))

(defrule crock-3
  (implies (not (equal (erl-value-kind (eval-expr x k fuel)) :fault))
           (and (integerp fuel) (> fuel 0)))
  :expand (eval-expr x k fuel))

(defrule crock-4
  (implies (not (equal (erl-value-kind (apply-k val k fuel)) :fault))
           (and (integerp fuel) (> fuel 0)))
  :expand (apply-k val k fuel))

(in-theory (disable crock-4))

(defrule crock-5
  (implies (<= fuel 0)
           (equal (erl-value-kind (apply-k val k fuel)) :fault))
  :expand (apply-k val k fuel))


(defrule lemma-init-k-is-equiv-for-binary-op-expr1
    (implies (and (expr-p x)
                  (equal (node-kind x) :binary-op)
                  (erl-k-p k)
                  (natp fuel))
           (let ((op (node-binary-op->op x))
                 (left (node-binary-op->left x))
                 (right (node-binary-op->right x)))
                (implies (not (equal (erl-value-kind (eval-expr left (make-erl-k-binary-op-expr1 :op op :expr2 right :k k) fuel)) :fault))
                         (equal (eval-expr left (make-erl-k-binary-op-expr1 :op op :expr2 right :k k) fuel)
                                (apply-k (eval-expr left (make-erl-k-binary-op-expr1 :op op :expr2 right :k :init) fuel) k fuel)))))
  :expand ((eval-expr left (make-erl-k-binary-op-expr1 :op op :expr2 right :k k) fuel)
           (eval-expr left (make-erl-k-binary-op-expr1 :op op :expr2 right :k :init) fuel)
            (EVAL-EXPR (NODE-BINARY-OP->LEFT X)
                    (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                          (NODE-BINARY-OP->RIGHT X)
                                          NIL K)
                    FUEL)
            (EVAL-EXPR (NODE-BINARY-OP->LEFT X)
                              (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                                      (NODE-BINARY-OP->RIGHT X)
                                                      NIL '(:INIT))
                              FUEL)
            (APPLY-K (ERL-VALUE-STRING (NODE-STRING->VAL (NODE-BINARY-OP->LEFT X)))
              (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                      (NODE-BINARY-OP->RIGHT X)
                                      NIL K)
              (+ -1 FUEL))
            (APPLY-K (ERL-VALUE-STRING (NODE-STRING->VAL (NODE-BINARY-OP->LEFT X)))
               (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                      (NODE-BINARY-OP->RIGHT X)
                                      NIL '(:INIT))
               (+ -1 FUEL))
            (APPLY-K (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
              (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                      (NODE-BINARY-OP->RIGHT X)
                                      NIL K)
              (+ -1 FUEL))
            (APPLY-K (ERL-VALUE-ATOM (NODE-ATOM->VAL (NODE-BINARY-OP->LEFT X)))
               (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                      (NODE-BINARY-OP->RIGHT X)
                                      NIL '(:INIT))
               (+ -1 FUEL))
            (APPLY-K (ERL-VALUE-INTEGER (NODE-STRING->VAL (NODE-BINARY-OP->LEFT X)))
              (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                      (NODE-BINARY-OP->RIGHT X)
                                      NIL K)
              (+ -1 FUEL))
            (APPLY-K (ERL-VALUE-INTEGER (NODE-STRING->VAL (NODE-BINARY-OP->LEFT X)))
               (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                      (NODE-BINARY-OP->RIGHT X)
                                      NIL '(:INIT))
               (+ -1 FUEL))
            (EVAL-EXPR
              (NODE-BINARY-OP->LEFT (NODE-BINARY-OP->LEFT X))
              (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP (NODE-BINARY-OP->LEFT X))
                                    (NODE-BINARY-OP->RIGHT (NODE-BINARY-OP->LEFT X))
                                    NIL
                                    (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                                            (NODE-BINARY-OP->RIGHT X)
                                                            NIL K))
              (+ -1 FUEL))
            (EVAL-EXPR
              (NODE-BINARY-OP->LEFT (NODE-BINARY-OP->LEFT X))
              (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP (NODE-BINARY-OP->LEFT X))
                                    (NODE-BINARY-OP->RIGHT (NODE-BINARY-OP->LEFT X))
                                    NIL
                                    (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                                            (NODE-BINARY-OP->RIGHT X)
                                                            NIL '(:INIT)))
              (+ -1 FUEL))
            (EVAL-EXPR (NODE-BINARY-OP->RIGHT X)
              (ERL-K-BINARY-OP-EXPR2
                   (NODE-BINARY-OP->OP X)
                   (ERL-VALUE-ATOM (NODE-ATOM->VAL (NODE-BINARY-OP->LEFT X)))
                   NIL '(:INIT))
              (+ -2 FUEL))
            (EVAL-EXPR (NODE-BINARY-OP->RIGHT X)
              (ERL-K-BINARY-OP-EXPR2
                   (NODE-BINARY-OP->OP X)
                   (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                   NIL '(:INIT))
              (+ -2 FUEL))
            (EVAL-EXPR (NODE-BINARY-OP->RIGHT X)
              (ERL-K-BINARY-OP-EXPR2
                   (NODE-BINARY-OP->OP X)
                   (ERL-VALUE-STRING (NODE-STRING->VAL (NODE-BINARY-OP->LEFT X)))
                   NIL '(:INIT))
              (+ -2 FUEL))
            (APPLY-K (ERL-VALUE-ATOM (NODE-ATOM->VAL (NODE-BINARY-OP->LEFT X)))
           (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                  (NODE-BINARY-OP->RIGHT X)
                                  NIL K)
           (+ -1 FUEL))
          (APPLY-K (ERL-VALUE-ATOM (NODE-ATOM->VAL (NODE-BINARY-OP->LEFT X)))
           (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                  (NODE-BINARY-OP->RIGHT X)
                                  NIL K)
           (+ -1 FUEL))
          (EVAL-EXPR
            (NODE-BINARY-OP->RIGHT X)
            (ERL-K-BINARY-OP-EXPR2
                  (NODE-BINARY-OP->OP X)
                  (ERL-VALUE-STRING (NODE-STRING->VAL (NODE-BINARY-OP->LEFT X)))
                  NIL K)
            (+ -2 FUEL))
          (EVAL-EXPR (NODE-BINARY-OP->RIGHT X)
             (ERL-K-BINARY-OP-EXPR2
                  (NODE-BINARY-OP->OP X)
                  (ERL-VALUE-ATOM (NODE-ATOM->VAL (NODE-BINARY-OP->LEFT X)))
                  NIL K)
             (+ -2 FUEL))
        (EVAL-EXPR (NODE-BINARY-OP->RIGHT X)
             (ERL-K-BINARY-OP-EXPR2
                  (NODE-BINARY-OP->OP X)
                  (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                  NIL K)
             (+ -2 FUEL))
      (APPLY-K (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
             (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                    (NODE-BINARY-OP->RIGHT X)
                                    NIL '(:INIT))
             (+ -1 FUEL))
      (APPLY-K (ERL-VALUE-ATOM (NODE-ATOM->VAL (NODE-BINARY-OP->LEFT X)))
             (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                    (NODE-BINARY-OP->RIGHT X)
                                    NIL '(:INIT))
             (+ -1 FUEL))
      (APPLY-K (ERL-VALUE-STRING (NODE-STRING->VAL (NODE-BINARY-OP->LEFT X)))
             (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                    (NODE-BINARY-OP->RIGHT X)
                                    NIL '(:INIT))
             (+ -1 FUEL))
    ;; 17.3 17.6
    )
    ;; 30'' and 33''
    :hints (
            ("Subgoal 30''" 
              :use ((:instance fuel-is-good-if-less-fuel-is-good-apply
                (val  (APPLY-K
                        (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->RIGHT X)))
                        (ERL-K-BINARY-OP-EXPR2
                            (NODE-BINARY-OP->OP X)
                            (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                            NIL '(:INIT))
                        (+ -3 FUEL)))
                (k k)
                (fuel fuel)
                (z -3)))
              :in-theory (enable lemma-init-k-returns-as-is-binop-expr2))
            ("Subgoal 33''" 
              :use ((:instance fuel-is-good-if-less-fuel-is-good-apply
                (val (APPLY-K
                        (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->RIGHT X)))
                        (ERL-K-BINARY-OP-EXPR2
                            (NODE-BINARY-OP->OP X)
                            (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                            NIL '(:INIT))
                        (+ -3 FUEL)))
                (k k)
                (fuel fuel)
                (z -3)))
              :in-theory (enable lemma-init-k-returns-as-is-binop-expr2))
          ("Subgoal 17.6" 
            :use ((:instance lemma-init-k-returns-as-is-binop-expr2
                    (val (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->RIGHT X))))
                    (k (ERL-K-BINARY-OP-EXPR2
                              (NODE-BINARY-OP->OP X)
                              (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                              NIL K))
                    (fuel (+ -3 fuel)))))
          ("Subgoal 17.6'''"
            :use ((:instance crock-4
                    (val (APPLY-K
                        (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->RIGHT X)))
                        (ERL-K-BINARY-OP-EXPR2
                            (NODE-BINARY-OP->OP X)
                            (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                            NIL '(:INIT))
                        (+ -3 FUEL)))
                    (k k)
                    (fuel (+ -3 fuel)))))
          ("Subgoal 17.6'5'"
              :use ((:instance fuel-is-good-if-less-fuel-is-good-apply
                (val (APPLY-K
                        (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->RIGHT X)))
                        (ERL-K-BINARY-OP-EXPR2
                            (NODE-BINARY-OP->OP X)
                            (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                            NIL '(:INIT))
                        (+ -3 FUEL)))
                (k k)
                (fuel fuel)
                (z -3)))
              :in-theory (enable lemma-init-k-returns-as-is-binop-expr2))
          ("Subgoal 17.3" 
            :use ((:instance lemma-init-k-returns-as-is-binop-expr2
                    (val (ERL-VALUE-STRING (NODE-STRING->VAL (NODE-BINARY-OP->RIGHT X))))
                    (k (ERL-K-BINARY-OP-EXPR2
                              (NODE-BINARY-OP->OP X)
                              (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                              NIL K))
                    (fuel (+ -3 fuel)))))
          ("Subgoal 17.3'''"
            :use ((:instance crock-4
                    (val (APPLY-K
                        (ERL-VALUE-STRING (NODE-STRING->VAL (NODE-BINARY-OP->RIGHT X)))
                        (ERL-K-BINARY-OP-EXPR2
                            (NODE-BINARY-OP->OP X)
                            (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                            NIL '(:INIT))
                        (+ -3 FUEL)))
                    (k k)
                    (fuel (+ -3 fuel)))))
          ("Subgoal 17.3'5'"
              :use ((:instance fuel-is-good-if-less-fuel-is-good-apply
                (val (APPLY-K
                        (ERL-VALUE-STRING (NODE-STRING->VAL (NODE-BINARY-OP->RIGHT X)))
                        (ERL-K-BINARY-OP-EXPR2
                            (NODE-BINARY-OP->OP X)
                            (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                            NIL '(:INIT))
                        (+ -3 FUEL)))
                (k k)
                (fuel fuel)
                (z -3)))
              :in-theory (enable lemma-init-k-returns-as-is-binop-expr2))
        ("Subgoal 17.2" 
            :use ((:instance lemma-init-k-returns-as-is-binop-expr2
                    (val (ERL-VALUE-ATOM (NODE-ATOM->VAL (NODE-BINARY-OP->RIGHT X))))
                    (k (ERL-K-BINARY-OP-EXPR2
                              (NODE-BINARY-OP->OP X)
                              (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                              NIL K))
                    (fuel (+ -3 fuel)))))
          ("Subgoal 17.2'''"
            :use ((:instance crock-4
                    (val (APPLY-K
                        (ERL-VALUE-ATOM (NODE-ATOM->VAL (NODE-BINARY-OP->RIGHT X)))
                        (ERL-K-BINARY-OP-EXPR2
                            (NODE-BINARY-OP->OP X)
                            (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                            NIL '(:INIT))
                        (+ -3 FUEL)))
                    (k k)
                    (fuel (+ -3 fuel)))))
          ("Subgoal 17.2'5'"
              :use ((:instance fuel-is-good-if-less-fuel-is-good-apply
                (val (APPLY-K
                        (ERL-VALUE-ATOM (NODE-ATOM->VAL (NODE-BINARY-OP->RIGHT X)))
                        (ERL-K-BINARY-OP-EXPR2
                            (NODE-BINARY-OP->OP X)
                            (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                            NIL '(:INIT))
                        (+ -3 FUEL)))
                (k k)
                (fuel fuel)
                (z -3)))
              :in-theory (enable lemma-init-k-returns-as-is-binop-expr2))
          ("Subgoal 17.1'"
            :expand (
                (EVAL-EXPR
                      (NODE-BINARY-OP->LEFT (NODE-BINARY-OP->RIGHT X))
                      (ERL-K-BINARY-OP-EXPR1
                            (NODE-BINARY-OP->OP (NODE-BINARY-OP->RIGHT X))
                            (NODE-BINARY-OP->RIGHT (NODE-BINARY-OP->RIGHT X))
                            NIL
                            (ERL-K-BINARY-OP-EXPR2
                                (NODE-BINARY-OP->OP X)
                                (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                                NIL K))
                      FUEL)
                (EVAL-EXPR
                (NODE-BINARY-OP->LEFT (NODE-BINARY-OP->RIGHT X))
                (ERL-K-BINARY-OP-EXPR1
                    (NODE-BINARY-OP->OP (NODE-BINARY-OP->RIGHT X))
                    (NODE-BINARY-OP->RIGHT (NODE-BINARY-OP->RIGHT X))
                    NIL
                    (ERL-K-BINARY-OP-EXPR2
                        (NODE-BINARY-OP->OP X)
                        (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                        NIL '(:INIT)))
                (+ -3 FUEL))
                (EVAL-EXPR
                  (NODE-BINARY-OP->LEFT (NODE-BINARY-OP->RIGHT X))
                  (ERL-K-BINARY-OP-EXPR1
                    (NODE-BINARY-OP->OP (NODE-BINARY-OP->RIGHT X))
                    (NODE-BINARY-OP->RIGHT (NODE-BINARY-OP->RIGHT X))
                    NIL
                    (ERL-K-BINARY-OP-EXPR2
                        (NODE-BINARY-OP->OP X)
                        (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                        NIL K))
                  (+ -3 FUEL))
                ))
           ("Subgoal 17.1.12''"
              :use ((:instance fuel-is-good-if-less-fuel-is-good-apply
                (val (ERL-VALUE-INTEGER  (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT (NODE-BINARY-OP->RIGHT X)))))
                (k  (ERL-K-BINARY-OP-EXPR1
                      (NODE-BINARY-OP->OP (NODE-BINARY-OP->RIGHT X))
                      (NODE-BINARY-OP->RIGHT (NODE-BINARY-OP->RIGHT X))
                      NIL
                      (ERL-K-BINARY-OP-EXPR2
                          (NODE-BINARY-OP->OP X)
                          (ERL-VALUE-INTEGER (NODE-INTEGER->VAL (NODE-BINARY-OP->LEFT X)))
                          NIL K)))
                (fuel (1- fuel))
                (z -3))))
          ))




;; ============================================================================================

(in-theory (disable more-fuel-is-good-for-apply))

(defrule fuel-is-good-if-less-fuel-is-good-apply
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

(in-theory (disable fuel-is-good-if-less-fuel-is-good-apply))

; (defrule fuel-is-not-fault-if-less-fuel-is-not-fault-apply
;   (implies (and (erl-value-p val)
;                 (erl-k-p k)
;                 (natp (+ z fuel))
;                 (integerp z)
;                 (< z 0)
;                 (natp fuel)
;                 (not (equal (erl-value-kind (apply-k val k (+ z fuel))) :fault)))
;            (not (equal (erl-value-kind (apply-k val k fuel)) :fault)))
;   :use ((:instance more-fuel-is-good-for-apply
;           (val val)
;           (k k)
;           (fuel1 (+ z fuel))
;           (fuel2 fuel))))

(in-theory (disable more-fuel-is-good-for-eval))

(defrule fuel-is-good-if-less-fuel-is-good
  (implies (and (expr-p x)
                (erl-k-p k)
                (natp (+ z fuel))
                (integerp z)
                (< z 0)
                (natp fuel)
                (not (equal (erl-value-kind (eval-expr x k (+ z fuel))) :fault)))
           (equal (eval-expr x k (+ z fuel)) (eval-expr x k fuel)))
  :use ((:instance more-fuel-is-good-for-eval
          (x x)
          (k k)
          (fuel1 (+ z fuel))
          (fuel2 fuel))))

; (defrule fuel-is-not-fault-if-less-fuel-is-not-fault-eval
;   (implies (and (expr-p x)
;                 (erl-k-p k)
;                 (natp (+ z fuel))
;                 (integerp z)
;                 (< z 0)
;                 (natp fuel)
;                 (not (equal (erl-value-kind (eval-expr x k (+ z fuel))) :fault)))
;            (not (equal (erl-value-kind (eval-expr x k fuel)) :fault)))
;   :use ((:instance more-fuel-is-good-for-eval
;           (x x)
;           (k k)
;           (fuel1 (+ z fuel))
;           (fuel2 fuel))))


;; =============================================================================================










;; ===============================================================================================
(defrule crock-0
  (implies (and (expr-p x)
                (erl-k-p k)
                (natp fuel)
                (natp (+ z fuel))
                (< z 0)
                (equal (node-kind x) :binary-op)
                (NOT (EQUAL (ERL-VALUE-KIND (EVAL-EXPR (NODE-BINARY-OP->LEFT X) 
                                                       (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X) 
                                                                              (NODE-BINARY-OP->RIGHT X) NIL K) 
                                                       (+ z FUEL)))
                            :FAULT)))
            (not (EQUAL (ERL-VALUE-KIND (EVAL-EXPR (NODE-BINARY-OP->LEFT X)
                                                   (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                                                          (NODE-BINARY-OP->RIGHT X) NIL K)
                                                   FUEL))
                 :FAULT)))
  :use ((:instance fuel-is-not-fault-if-less-fuel-is-not-fault-eval
        (x (NODE-BINARY-OP->LEFT X))
        (k (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X) (NODE-BINARY-OP->RIGHT X) NIL K))
        (fuel fuel)
        (z z))))

(defrule crock-1
  (implies (and (expr-p x)
                (erl-k-p k)
                (natp fuel)
                (natp (+ -1 fuel))
                (equal (node-kind x) :binary-op)
                (NOT (EQUAL (ERL-VALUE-KIND (EVAL-EXPR (NODE-BINARY-OP->LEFT X) 
                                                       (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X) 
                                                                              (NODE-BINARY-OP->RIGHT X) NIL K) 
                                                       (+ -1 FUEL)))
                            :FAULT)))
            (not (EQUAL (ERL-VALUE-KIND (EVAL-EXPR (NODE-BINARY-OP->LEFT X)
                                                   (ERL-K-BINARY-OP-EXPR1 (NODE-BINARY-OP->OP X)
                                                                          (NODE-BINARY-OP->RIGHT X) NIL K)
                                                   FUEL))
                 :FAULT)))
  :use ((:instance crock-0
        (x x)
        (k k)
        (fuel fuel)
        (z -1))))



(defun eval-init-hint (clause)
  (cond 
    ((acl2::occur-lst '(flag-is 'eval) clause)
	   '(:expand ((eval-expr x k fuel)
                (EVAL-EXPR X K 0)
                (EVAL-EXPR X :INIT FUEL)
              
                    )))
	  ((acl2::occur-lst '(flag-is 'apply) clause)
	  '(:expand ((APPLY-K VAL K FUEL)
               (APPLY-K VAL K 0)
               (APPLY-K VAL :INIT FUEL)
               
              )))
	  (t nil)))

(defthm-eval-expr-flag init-k-is-equiv
  (defthm init-k-is-equiv-for-binary-op
    (implies (and (expr-p x)
                  (equal (node-kind x) :binary-op)
                  (erl-k-p k)
                  (natp fuel)
                  (not (equal (erl-value-kind (eval-expr x k fuel)) :fault)))
           (let ((op (node-binary-op->op x))
                 (left (node-binary-op->left x))
                 (right (node-binary-op->right x)))
                (equal (eval-expr left (make-erl-k-binary-op-expr1 :op op :expr2 right :k k) fuel)
                       (apply-k (eval-expr left (make-erl-k-binary-op-expr1 :op op :expr2 right :k :init) fuel) k fuel))))
    :flag eval)

  (defthm init-k-is-equiv-eval
    (implies (and (expr-p x) 
                  (erl-k-p k)
                  (natp fuel)
                  (not (equal (erl-value-kind (eval-expr x k fuel)) :fault)))
              (equal (eval-expr x k fuel)
                    (apply-k (eval-expr x :init fuel) k fuel)))
    :flag eval)
    :hints((eval-init-hint clause)))