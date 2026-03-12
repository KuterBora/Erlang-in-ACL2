(defrule foo
  (implies 
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :expr)
       (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop))

    (equal (erl-s-klst->klst (eval-k k s))
           (list (make-erl-k :fuel (1- (erl-k->fuel k))
                             :kont (make-kont-expr :expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))
                 (make-erl-k :fuel (1- (erl-k->fuel k))
                             :kont (make-kont-binop-expr1 
                              :op (node-binop->op (kont-expr->expr (erl-k->kont k)))
                              :right (node-binop->right (kont-expr->expr (erl-k->kont k)))
                              :bind-0 (erl-state->bind s))))))
  :enable eval-k)

(defrule bar
  (implies 
    (and
      (wf-state-p s)
      (erl-k-p k)
      (> (erl-k->fuel k) 0)
      (equal (kont-kind (erl-k->kont k)) :expr)
      (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop))
    (equal (erl-s-klst->s (eval-k k s)) 
           (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)