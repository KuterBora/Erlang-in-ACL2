(in-package "ACL2")
(include-book "../core/eval-theorems")


; Unop Kont-Step ---------------------------------------------------------------

; The following theorems show that evaluating a continuation for a unop 
; expression is equivalent to evaluating the operand, and then applying 
; the unop, as would happen in Erlang's control flow.
; There are also some rules about excpetions, rejections, etc. 

; Stepping the initial continuation
(defrule eval-k-of-expr-unop->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :unop))
    (equal 
      (erl-s-klst->klst (eval-k k s))
      (list 
        (make-erl-k 
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr :expr 
            (node-unop->expr (kont-expr->expr (erl-k->kont k)))))
        (make-erl-k :fuel (1- (erl-k->fuel k))
                    :kont (make-kont-unop 
                        :op (node-unop->op (kont-expr->expr (erl-k->kont k))))))))
  :enable eval-k)

(defrule eval-k-of-expr-unop->s
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :unop))
    (equal (erl-s-klst->s (eval-k k s)) 
           (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)


; Stepping the unop continuation                                            
(defrule eval-k-of-unop->klst
  (implies 
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
          (equal (kont-kind (erl-k->kont k)) :unop))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-unop->s
  (implies 
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :unop))
    (equal
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in
        s
        (apply-erl-unop
            (kont-unop->op (erl-k->kont k)) 
            (erl-state->in s)))))
  :enable eval-k)

; apply-k with an unop continuation is equivalent to evaluating the 
; operand and then applying the unop -- assuming there are no excpetion,
; rejection, or out-of-fuel errors.
;
; If evaluation succeeds for s and k, in the returned state
; - in will contain the result of the unop operation
; - bind will contain any previous bindings and any new ones created
;   by the operand
; Rest: TODO

(defrule apply-k-of-unop->in
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 1)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :unop))
    (b* (((erl-state s) s)
         ((erl-k k))
         (op (node-unop->op (kont-expr->expr k.kont)))
         (x  (node-unop->expr (kont-expr->expr k.kont)))
         (x_res (apply-k (update-erl-state->in s (make-erl-val-none))
                         (list (make-erl-k :fuel (1- k.fuel) 
                                           :kont (make-kont-expr :expr x)))))
         ((unless (wf-state-p x_res)) t))
        (equal (erl-state->in (apply-k s (list k)))
               (apply-erl-unop op (erl-state->in x_res))))))

(defrule apply-k-of-unop->bind
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 1)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :unop))
    (b* (((erl-state s) s)
         ((erl-k k))
         (x  (node-unop->expr (kont-expr->expr k.kont)))
         (x_res (apply-k (update-erl-state->in s (make-erl-val-none))
                         (list (make-erl-k :fuel (1- k.fuel) 
                                           :kont (make-kont-expr :expr x)))))
         ((unless (wf-state-p x_res)) t))

        (equal (erl-state->bind (apply-k s (list k)))
               (erl-state->bind x_res)))))