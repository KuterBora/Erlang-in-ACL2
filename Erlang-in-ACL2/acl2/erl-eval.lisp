(in-package "ACL2")
(include-book "erl-op")
(include-book "ast-theorems")
(include-book "erl-kont")
(include-book "termination")

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

; calls to eval-k either return a tuple of two contunuations, or an empty list
(defrule eval-k-decreases-fuel
  (implies 
    (and (erl-val-p val) (erl-k-p k))
    (or (null (erl-val-klst->klst (eval-k k val)))
        (and (tuplep 2 (erl-val-klst->klst (eval-k k val)))
              (equal (erl-k->fuel (car (erl-val-klst->klst (eval-k k val)))) 
                    (- (erl-k->fuel k) 1))
              (equal (erl-k->fuel (cadr (erl-val-klst->klst (eval-k k val)))) 
                    (- (erl-k->fuel k) 1))
              (equal (cdr (erl-val-klst->klst (eval-k k val))) 
                    (cons (cadr (erl-val-klst->klst (eval-k k val))) nil)))))
  :enable eval-k)

; Eval-op decreases the klst-measure
(defrule eval-k-decreases-klst-measure
  (b* ((klst (erl-klst-fix klst))
        (val (erl-val-fix val))
        ((if (null klst)) t))
    (l< (klst-measure (append (erl-val-klst->klst (eval-k (car klst) val))
                              (cdr klst)))
        (klst-measure klst)))
  :enable eval-k
  :use (:functional-instance eval-op-decreases-klst-measure  
      (eval-op eval-k)
      (eval-result-p erl-val-klst-p)
      (eval-result->klst erl-val-klst->klst))) 

; Recursively apply the next continuation to the value produced by the previous.
(define apply-k ((val erl-val-p) (klst erl-klst-p))
  :returns (v erl-val-p)
  :well-founded-relation l<
  :measure (klst-measure (erl-klst-fix klst))
  (b* ((val (erl-val-fix val))
       (klst (erl-klst-fix klst))
       ((if (equal val (make-erl-val-fault))) val)
       ((if (endp klst)) val)
       ((cons khd ktl) klst)
       ((erl-val-klst kv) (eval-k khd val))
       ((if (equal kv.v (make-erl-val-fault))) kv.v))
    (apply-k kv.v (append kv.klst ktl)))
  :hints (("Goal" :use ((:instance eval-k-decreases-klst-measure (klst klst) (val val)))
                  :in-theory (disable klst-measure eval-k-decreases-klst-measure))))


; Theorems ---------------------------------------------------------------------

; Applying a concatenated continuation list equals applying each sublist in sequence.
(defrule apply-k-of-append
  (implies
    (and (erl-klst-p klst1)
         (erl-klst-p klst2)
         (erl-val-p val)
         (equal klst (append klst1 klst2)))
    (equal
      (apply-k val klst)
      (apply-k (apply-k val klst1) klst2)))
  :in-theory (enable apply-k))


; Calling apply-k with a fault value will return fault
(defrule apply-k-of-fault
  (implies (equal (erl-val-kind val) (make-erl-val-fault))
           (equal (apply-k val klst) (make-erl-val-fault)))
  :enable apply-k)


; The following theorems show that if evaluating a value and klst terminates
; without fault, then increasing the fuel of the continuations will not change the result.
; It is easier, and more elegant, for ACL2 to prove this for the more general case where 
; each k in the klst is given more fuel, rather than, for example, increasing the fuel of
; only the first k. This is why increase-fuel and the corresponding theorems are defined.

; Increase the fuel of each continuation in klst by n.
(define increase-fuel ((klst erl-klst-p) (n natp))
  :measure (len klst)
  :returns (ks erl-klst-p)
  (b* ((klst (erl-klst-fix klst))
       (n (nfix n))
       ((if (endp klst)) nil))
      (cons (make-erl-k :kont (erl-k->kont (car klst))
                        :fuel (+ n (erl-k->fuel (car klst))))
            (increase-fuel (cdr klst) n))))

; increase-fuel is distributive over append
(defrule increase-fuel-is-distributive-over-append
  (implies
    (and (erl-val-p val)
         (erl-klst-p rest)
         (erl-k-p k)
         (natp n)
         (not (equal (erl-val-klst->v (eval-k k val)) (make-erl-val-fault))))
    (equal (increase-fuel (append (erl-val-klst->klst (eval-k k val)) rest) n)
           (append (erl-val-klst->klst (eval-k (erl-k (+ n (erl-k->fuel k))
                                                           (erl-k->kont k))
                                               val))
                   (increase-fuel rest n))))
  :in-theory (enable increase-fuel eval-k))

; A continuation that did not cause an error in eval-k will produce the same result
; if its fuel is increased.
(defrule more-fuel-is-good-for-eval
  (implies 
    (and (erl-val-p val)
         (erl-k-p k)
         (natp n)
         (not (equal (erl-val-klst->v (eval-k k val)) (make-erl-val-fault))))
    (equal (erl-val-klst->v (eval-k (erl-k (+ n (erl-k->fuel k))
                                           (erl-k->kont k)) 
                                    val))
           (erl-val-klst->v (eval-k k val))))
  :enable eval-k)

; A continuation that did not cause an error in apply-k will produce the same result
; if its fuel is increased.
(defrule more-fuel-is-good-for-apply
  (implies 
    (and (erl-val-p val)
         (erl-klst-p klst)
         (not (equal (apply-k val klst) (make-erl-val-fault)))
         (natp n))
    (equal (apply-k val (increase-fuel klst n))
           (apply-k val klst)))
  :enable (apply-k increase-fuel)
  :expand (apply-k val
                  (cons (erl-k (+ n (erl-k->fuel (car klst)))
                              (erl-k->kont (car klst)))
                        (increase-fuel (cdr klst) n))))