(in-package "ACL2")
(include-book "centaur/fty/top" :DIR :SYSTEM)
(include-book "std/util/top" :DIR :SYSTEM)
(set-induction-depth-limit 1)

; require erl-ast, erl-value, erl-kont
(ld "erl-ast.lisp")
(ld "erl-value.lisp")
(ld "erl-kont.lisp")
(ld "eval-theorems.lisp")
(ld "erl-op.lisp")

;; TODO: maybe have a seperate evaluator for pattern and guard to make proofs easier?

;; Erlang Evaluator

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
          (:integer (apply-k x k (1- fuel)))
          (:atom (apply-k x k (1- fuel)))
          (:string (apply-k x k (1- fuel)))
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

;; ============================================================================================
;; Done till this point
;; ============================================================================================

;; Eventually I want to prove a theorem like this, but first I think I need the theorems below
(defrule eval-erl-addition
  (implies (and (expr-p x) 
                (erl-k-p k) 
                (natp fuel)
                (equal (node-kind x) :binary-op)
                (equal '+ (node-binary-op->op x))
                (equal left (node-binary-op->left x))
                (equal right (node-binary-op->right x))
                ;; add more restrictions here that state the fuel is enough
                )
           (equal (eval-expr x k fuel)
                  (apply-k (erl-add (eval-expr left :init fuel)
                                    (eval-expr right :init fuel))
                           k
                           fuel))))

;; Show adding more fuel will not change the result if the initial fuel did not produce fault
;; I attempted proving this with flag-theorems but I got stuck
(defrule more-fuel-is-good
  (implies (and (expr-p x) 
                (erl-k-p k) 
                (natp fuel1)
                (natp fuel2)
                (> fuel2 fuel1)
                (not (equal (erl-value-kind (eval-expr x k fuel1)) :fault)))
           (equal (eval-expr x k fuel1)
                  (eval-expr x k fuel2))))

;; Show that (eval-expr x k f) == (apply-k (eval-expr x :init f) k f), if f is enough fuel
(defrule eval-with-k-is-eqiuvalent-to-apply-k-with-eval-init 
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



