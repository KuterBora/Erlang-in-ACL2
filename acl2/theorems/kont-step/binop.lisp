(in-package "ACL2")
(include-book "../core/eval-theorems")


; Binop Kont-Step --------------------------------------------------------------

; The following theorems show that evaluating a continuation for a binop 
; expression is equivalent to evaluating the left operand, the right operand
; and then applying the binop, as would happen in Erlang's control flow.
; There are also some rules about excpetions, rejections, etc. 

; Stepping the initial continuation
(local (defrule eval-k-of-expr-binop->klst
  (implies 
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :expr)
       (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop))
    (equal 
      (erl-s-klst->klst (eval-k k s))
      (list 
        (make-erl-k 
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr 
            :expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))
        (make-erl-k :fuel (1- (erl-k->fuel k))
                    :kont (make-kont-binop-expr1 
                            :op (node-binop->op (kont-expr->expr (erl-k->kont k)))
                            :right (node-binop->right (kont-expr->expr (erl-k->kont k)))
                            :bind-0 (erl-state->bind s))))))
  :enable eval-k))

(local (defrule eval-k-of-expr-binop->s
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop))
    (equal (erl-s-klst->s (eval-k k s)) 
           (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k))

; Stepping the binop-expr1 continuation
(local (defrule eval-k-of-binop-expr1->klst
  (implies 
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr1))
    (equal 
      (erl-s-klst->klst (eval-k k s))
      (list (make-erl-k 
              :fuel (1- (erl-k->fuel k)) 
              :kont (make-kont-expr 
                      :expr (kont-binop-expr1->right (erl-k->kont k))))
            (make-erl-k 
              :fuel (1- (erl-k->fuel k)) 
              :kont (make-kont-binop-expr2 
                      :op (kont-binop-expr1->op (erl-k->kont k))
                      :val (erl-state->in s)
                      :left-bind (erl-state->bind s))))))
  :enable eval-k))

(local (defrule eval-k-of-binop-expr1->s
  (implies 
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr1))
    (equal 
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->bind s (kont-binop-expr1->bind-0 (erl-k->kont k)))))
  :enable eval-k))

; Stepping the binop-expr-2 continuation                                            
(local (defrule eval-k-of-binop-expr2->klst
  (implies 
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr2))
    (equal (erl-s-klst->klst (eval-k k s))
           nil))
  :enable eval-k))

(local (defrule eval-k-of-binop-expr2->s
  (implies 
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr2)
         (omap::compatiblep
            (erl-state->bind s) 
            (kont-binop-expr2->left-bind (erl-k->kont k))))
    (equal
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in-bind
        s
        (apply-erl-binop 
          (kont-binop-expr2->op (erl-k->kont k)) 
          (kont-binop-expr2->val (erl-k->kont k))
          (erl-state->in s))
        (omap::update*
          (erl-state->bind s) 
          (kont-binop-expr2->left-bind (erl-k->kont k))))))
  :enable eval-k))


; apply-k with a binop continuation is equivalent to evaluating the 
; operands in order and then applying the binop -- assuming there
; are no excpetion, rejection, or out-of-fuel errors.
;
; If evaluation succeeds for s and k, in the returned state
; - in will contain the result of the binop
; - bind will contain any previous bindings and any new ones created
;   in either operand.
; Rest: TODO

(defrule apply-k-of-binop->in
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 2)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop))
    (b* (((erl-state s) s)
         ((erl-k k))
         (op (node-binop->op (kont-expr->expr k.kont)))
         (a  (node-binop->left (kont-expr->expr k.kont)))
         (b  (node-binop->right (kont-expr->expr k.kont)))
         (a_res (apply-k (update-erl-state->in s (make-erl-val-none))
                         (list (make-erl-k :fuel (1- k.fuel) 
                                           :kont (make-kont-expr :expr a)))))
         ((unless (wf-state-p a_res)) t)
         (b_res (apply-k (update-erl-state->bind a_res s.bind)
                         (list (make-erl-k :fuel (- k.fuel 2) 
                                           :kont (make-kont-expr :expr b)))))
         ((unless (wf-state-p b_res)) t)
         ((unless (omap::compatiblep (erl-state->bind b_res) (erl-state->bind a_res))) t))

        (equal (erl-state->in (apply-k s (list k)))
               (apply-erl-binop op (erl-state->in a_res) (erl-state->in b_res))))))

(defrule apply-k-of-binop->bind
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 2)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop))
    (b* (((erl-state s) s)
         ((erl-k k))
         (a  (node-binop->left (kont-expr->expr k.kont)))
         (b  (node-binop->right (kont-expr->expr k.kont)))
         (a_res (apply-k (update-erl-state->in s (make-erl-val-none))
                         (list (make-erl-k :fuel (1- k.fuel) 
                                           :kont (make-kont-expr :expr a)))))
         ((unless (wf-state-p a_res)) t) 
         (b_res (apply-k (update-erl-state->bind a_res s.bind)
                         (list (make-erl-k :fuel (- k.fuel 2) 
                                           :kont (make-kont-expr :expr b)))))
         ((unless (wf-state-p b_res)) t)
         ((unless (omap::compatiblep (erl-state->bind b_res) (erl-state->bind a_res))) t))

        (equal (erl-state->bind (apply-k s (list k)))
               (omap::update* (erl-state->bind b_res) (erl-state->bind a_res))))))