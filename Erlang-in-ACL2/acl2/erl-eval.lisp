(in-package "ACL2")
(include-book "ast-theorems")
(include-book "erl-op")
(include-book "termination")

; Erlang Evaluator -------------------------------------------------------------

(set-induction-depth-limit 1)

; Each step of the evaluator returns an erl-s-klst where
; - s is an erl-state that is the result of evaulation.
; - klst is the pair of continuations produced by eval-k.
;   If klst is nil, evaluation for the current expression is complete.
(fty::defprod erl-s-klst
  ((s erl-state-p :default (make-erl-state))
   (klst erl-klst-p :default nil)))

; Evaluate the current continuation and return the next erl-val-klst
(define eval-k ((k erl-k-p) (s erl-state-p))
  :returns (ks erl-s-klst-p)
  (b* ((k (erl-k-fix k))
       (fuel (erl-k->fuel k))
       (k (erl-k->kont k))
       ((if (zp fuel)) (make-erl-s-klst :s (make-erl-state :in (make-erl-val-flimit))))
       (s (erl-state-fix s))
       (s.in (erl-state->in s))
       (s.bind (erl-state->bind s)))
    (kont-case k
      ; Evaluate an expression.
      (:expr (let ((x k.expr))
        (node-case x
          ; if x is an atomic term, simply return its value 
          (:integer (make-erl-s-klst :s (make-erl-state :in (make-erl-val-integer :val x.val)
                                                        :bind s.bind)))
          (:atom    (make-erl-s-klst :s (make-erl-state :in (make-erl-val-atom :val x.val)
                                                        :bind s.bind)))
          (:string  (make-erl-s-klst :s (make-erl-state :in (make-erl-val-string :val x.val)
                                                        :bind s.bind)))
          ; if x is a var, lookup its value. If the AST is well-formed, x shoudl be bound.
          (:var
            (if (omap::assoc x.id s.bind)
                (make-erl-s-klst :s (make-erl-state :in (omap::lookup x.id s.bind) 
                                                    :bind s.bind))
                (make-erl-s-klst :s (make-erl-state :in (make-erl-val-error :err "unbound variable")))))
          ; if x is a binop, evaluate the first operand, save the operator and the second operand 
          (:binop
            (make-erl-s-klst
              :s (make-erl-state :bind s.bind)
              :klst (list (make-erl-k :fuel (1- fuel) 
                                      :kont (make-kont-expr :expr x.left))
                          (make-erl-k :fuel (1- fuel) 
                                      :kont (make-kont-binop-expr1 :op x.op 
                                                                   :right x.right
                                                                   :bind0 s.bind))))))))
      ; Evaluate the second operand of a binop, save the operator and value of the first operand                                                    
      (:binop-expr1 
        (make-erl-s-klst
          :s (make-erl-state :bind k.bind0)
          :klst (list (make-erl-k :fuel (1- fuel) 
                                  :kont (make-kont-expr :expr k.right))
                      (make-erl-k :fuel (1- fuel) 
                                  :kont (make-kont-binop-expr2 :op k.op 
                                                               :val s.in
                                                               :bindL s.bind)))))
      ; apply the binop to the evaluated operands
      (:binop-expr2
        (if (omap::compatiblep s.bind k.bindL)
            (make-erl-s-klst :s (make-erl-state :in (apply-erl-binop k.op k.val s.in)
                                                :bind (omap::update* s.bind k.bindL)))
            (make-erl-s-klst :s (make-erl-state :in (make-erl-val-excpt :err 'badmatch))))))))

; calls to eval-k either return a tuple of two contunuations, or an empty list
(defrule eval-k-decreases-fuel
  (implies 
    (and (erl-state-p s) (erl-k-p k))
    (or (null (erl-s-klst->klst (eval-k k s)))
        (and (tuplep 2 (erl-s-klst->klst (eval-k k s)))
              (equal (erl-k->fuel (car (erl-s-klst->klst (eval-k k s)))) 
                    (- (erl-k->fuel k) 1))
              (equal (erl-k->fuel (cadr (erl-s-klst->klst (eval-k k s)))) 
                    (- (erl-k->fuel k) 1))
              (equal (cdr (erl-s-klst->klst (eval-k k s))) 
                    (cons (cadr (erl-s-klst->klst (eval-k k s))) nil)))))
  :enable eval-k)

; Eval-op decreases the klst-measure
(defrule eval-k-decreases-klst-measure
  (b* ((klst (erl-klst-fix klst))
        (x (erl-state-fix x))
        ((if (null klst)) t))
    (l< (klst-measure (append (erl-s-klst->klst (eval-k (car klst) x))
                              (cdr klst)))
        (klst-measure klst)))
  :enable eval-k
  :use (:functional-instance eval-op-decreases-klst-measure  
      (eval-op eval-k)
      (eval-result-p erl-s-klst-p)
      (eval-result->klst erl-s-klst->klst)
      (erl-result-p erl-state-p)
      (erl-result-fix erl-state-fix))) 

; Recursively apply the next continuation to the state produced by the previous.
(define apply-k ((s erl-state-p) (klst erl-klst-p))
  :returns (r erl-state-p)
  :well-founded-relation l<
  :measure (klst-measure (erl-klst-fix klst))
  (b* ((s (erl-state-fix s))
       (klst (erl-klst-fix klst))
       (s.in (erl-val-fix (erl-state->in s)))
       ; The evaluator has run out of fuel
       ((if (equal (erl-val-kind s.in) :flimit)) 
        (make-erl-state :in (make-erl-val-flimit)))
       ; The evaluator has encountered an internal error
       ((if (equal (erl-val-kind s.in) :error)) s)
       ; TODO: exception handling
       ((if (equal (erl-val-kind s.in) :excpt))
        (make-erl-state :in (make-erl-val-excpt)))
       ((if (endp klst)) s)
       ((cons khd ktl) klst)
       ((erl-s-klst ks) (eval-k khd s)))
    (apply-k ks.s (append ks.klst ktl)))
  :hints (("Goal" :use ((:instance eval-k-decreases-klst-measure (klst klst) (x s)))
                  :in-theory (disable klst-measure eval-k-decreases-klst-measure))))


; Theorems ---------------------------------------------------------------------

; Applying a concatenated continuation list equals applying each sublist in sequence.
(defrule apply-k-of-append
  (implies
    (and (erl-klst-p klst1)
         (erl-klst-p klst2)
         (erl-state-p s)
         (equal klst (append klst1 klst2)))
    (equal
      (apply-k s klst)
      (apply-k (apply-k s klst1) klst2)))
  :in-theory (enable apply-k))


; TODO: admit these rules after the congruence theorems are complete
; ; Calling apply-k with an flimit will return flimit
; (defrule apply-k-of-flimit
;   (implies  (and (erl-state-p s) (equal (erl-val-kind (erl-state->in s)) :flimit))
;             (equal (apply-k s klst) (make-erl-state :in (make-erl-val-flimit))))
;   :enable apply-k)

; (defrule apply-k-of-fault-direct
;   (equal (apply-k '(:fault) rest) '(:fault))
;   :enable apply-k)

; Calling apply-k with a nil klst returns val
; (defrule apply-k-of-nil
;   (implies (erl-state-p s) (equal (apply-k s nil) s))
;   :enable apply-k)

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
    (and (erl-state-p s)
         (erl-klst-p rest)
         (erl-k-p k)
         (natp n)
         (not (equal (erl-state->in (erl-s-klst->s (eval-k k s))) (make-erl-val-flimit))))
    (equal (increase-fuel (append (erl-s-klst->klst (eval-k k s)) rest) n)
           (append (erl-s-klst->klst (eval-k (erl-k (+ n (erl-k->fuel k))
                                                    (erl-k->kont k))
                                             s))
                   (increase-fuel rest n))))
  :in-theory (enable increase-fuel eval-k))

; A continuation that did not cause an error in eval-k will produce the same result
; if its fuel is increased.
(defrule more-fuel-is-good-for-eval
  (implies 
    (and (erl-val-p val)
         (erl-k-p k)
         (natp n)
         (not (equal (erl-state->in (erl-s-klst->s (eval-k k s))) (make-erl-val-flimit))))
    (equal (erl-s-klst->s (eval-k (erl-k (+ n (erl-k->fuel k))
                                         (erl-k->kont k)) 
                                  s))
           (erl-s-klst->s (eval-k k s))))
  :enable eval-k)

; ; A continuation that did not cause an error in apply-k will produce the same result
; ; if its fuel is increased.
; (defrule more-fuel-is-good-for-apply
;   (implies
;     (and (erl-state-p s)
;          (erl-klst-p klst)
;          (not (equal (erl-state->in (erl-s-klst->s (eval-k k s))) (make-erl-val-flimit)))
;          (natp n))
;     (equal (apply-k s (increase-fuel klst n))
;            (apply-k s klst)))
;   :enable (apply-k increase-fuel)
;   :expand ((apply-k s klst)
;            (apply-k s
;                     (cons (erl-k (+ n (erl-k->fuel (car klst)))
;                                  (erl-k->kont (car klst)))
;                           (increase-fuel (cdr klst) n)))))