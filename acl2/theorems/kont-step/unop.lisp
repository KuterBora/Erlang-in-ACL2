(in-package "ACL2")
(include-book "../core/eval-theorems")


; Unop Kont-Step ---------------------------------------------------------------

; The following theorems show that evaluating a continuation for a unop 
; expression is equivalent to evaluating the operand, and then applying 
; the unop, as would happen in Erlang's control flow.
; There are also some rules about excpetions, rejections, etc. 

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
          :kont (make-kont-expr
                  :expr (node-unop->expr
                           (kont-expr->expr (erl-k->kont k)))))
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-unop
                  :op (node-unop->op
                        (kont-expr->expr (erl-k->kont k))))))))
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