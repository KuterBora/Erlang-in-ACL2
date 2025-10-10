(in-package "ACL2")
(include-book "erl-op")
(include-book "ast-theorems")
(include-book "erl-kont")

; Erlang Evaluator -------------------------------------------------------------

(set-induction-depth-limit 1)

; Each step of the evaluator returns an erl-val-klst where
; - v is the result of evaulation.
; - klst is the pair of continuations produced by eval-k.
;   If klst is nil, evaluation for the current expression is complete.
(fty::defprod erl-val-klst
  ((v erl-val-p :default (make-erl-val-nil))
   (klst erl-klst-p :default nil)))

; Evaluate the current continuation and return the next erl-val-klst
(define eval-k ((k erl-k-p) (val erl-val-p))
  :returns (kv erl-val-klst-p)
  (b* ((fuel (erl-k->fuel k))
       (k (erl-k->kont k))
       ((if (zp fuel)) (make-erl-val-klst :v (make-erl-val-fault))))
    (kont-case k
      ; Evaluate an expression.
      (:expr (let ((x k.expr))
        (node-case x
          ; if x is an atomic term, simply return its value 
          (:integer (make-erl-val-klst :v (make-erl-val-integer :val x.val)))
          (:atom    (make-erl-val-klst :v (make-erl-val-atom :val x.val)))
          (:string  (make-erl-val-klst :v (make-erl-val-string :val x.val)))
          ; if x is a binop, evaluate the first operand, save the operator and the second operand 
          (:binop
            (make-erl-val-klst 
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr x.left))
                          (make-erl-k :fuel (1- fuel) :kont (make-kont-binop-expr1 :op x.op :right x.right))))))))
      ;; Evaluate the second operand of a binop, save the operator and value of the first operand                                                    
      (:binop-expr1 
        (make-erl-val-klst 
          :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr k.right))
                      (make-erl-k :fuel (1- fuel) :kont (make-kont-binop-expr2 :op k.op :val val)))))
      ;; apply the binop to the evaluated operands
      (:binop-expr2 (make-erl-val-klst :v (apply-erl-binop k.op k.val val))))))

;; include the measure for k-list
(include-book "apply-k-termination")

;; Recursively apply the next continuation to the value produced by the previous.
(define apply-k ((val erl-value-p) (klst erl-k-list-p))
  :returns (v erl-value-p)
  :well-founded-relation l<
  :measure (k-list-measure (erl-k-list-fix klst))
  (b* ((val (erl-value-fix val))
       (klst (erl-k-list-fix klst))
       ((if (equal val (make-erl-value-fault))) val)
       ((if (endp klst)) val)
       ((cons khd ktl) klst)
       ((erl-val-klst kv) (eval-k khd val))
       ((if (equal kv.v (make-erl-value-fault))) kv.v))
    (apply-k kv.v (append kv.klst ktl)))
  :hints (("Goal" :use ((:instance eval-k-decreases-k-list-measure (klst klst) (val val)))
                  :in-theory (disable k-list-measure eval-k-decreases-k-list-measure))))


;;-------------------------------------- Theorems --------------------------------------------------

;; splitting the klst and applying the two parts in order will yield the same result
(defrule apply-k-of-append
  (implies
    (and (erl-k-list-p klst1)
         (erl-k-list-p klst2)
         (erl-value-p val)
         (equal klst (append klst1 klst2)))
    (equal
      (apply-k val klst)
      (apply-k (apply-k val klst1) klst2)))
  :in-theory (enable apply-k))

;; calling apply-k with a fault value will return fault
(defrule apply-k-of-fault
  (implies (equal (erl-value-kind val) (make-erl-value-fault))
           (equal (apply-k val klst)   (make-erl-value-fault)))
  :enable apply-k)

;; Increase the fuel of each continuation in the list by n.
(define increase-fuel ((klst erl-k-list-p) (n natp))
  :measure (len klst)
  :returns (ks erl-k-list-p)
  (b* ((klst (erl-k-list-fix klst))
       (n (nfix n))
       ((if (endp klst)) nil))
      (cons (make-erl-k :kont (erl-k->kont (car klst))
                        :fuel (+ n (erl-k->fuel (car klst))))
            (increase-fuel (cdr klst) n))))

;; A continuation that did not cause an error in eval-k will provide the
;; same result if its fuel is increased.
(defrule more-fuel-is-good-for-eval
  (implies 
    (and (erl-value-p val)
         (erl-k-p k)
         (natp z)
         (not (equal (erl-val-klst->v (eval-k k val)) (make-erl-value-fault))))
    (equal (erl-val-klst->v (eval-k (erl-k (+ z (erl-k->fuel k))
                                           (erl-k->kont k)) 
                            val))
           (erl-val-klst->v (eval-k k val))))
  :enable (eval-k))


(defrule increase-fuel-is-distributive
  (implies
    (and (erl-value-p val)
         (erl-k-list-p rest)
         (erl-k-p k)
         (natp z)
         (not (equal (erl-val-klst->v (eval-k k val)) (make-erl-value-fault))))
    (equal (increase-fuel (append (erl-val-klst->klst (eval-k k val)) rest) z)
           (append (erl-val-klst->klst (eval-k (erl-k (+ z (erl-k->fuel k))
                                                           (erl-k->kont k))
                                               val))
                   (increase-fuel rest z))))
  :in-theory (enable increase-fuel eval-k))


(defrule more-fuel-is-good-for-apply
  (implies 
    (and (erl-value-p val)
         (erl-k-list-p klst)
         (not (equal (apply-k val klst) (make-erl-value-fault)))
         (natp z))
    (equal (apply-k val (increase-fuel klst z))
           (apply-k val klst)))
  :enable (apply-k increase-fuel)
  :hints (("Subgoal *1/7'''" 
    :expand (apply-k val
                    (cons (erl-k (+ z (erl-k->fuel (car klst)))
                                (erl-k->kont (car klst)))
                          (increase-fuel (cdr klst) z))))))