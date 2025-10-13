(in-package "ACL2")
(include-book "erl-eval")

(set-induction-depth-limit 1)

; Erlang Addition --------------------------------------------------------------

(defrule apply-k-of-binop-crock
  (implies
    (and
      (erl-val-p val)
      (erl-klst-p rest)
      (erl-k-p k)
      (equal (kont-kind (erl-k->kont k)) :expr)
      (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop)
      (not (equal val (make-erl-val-fault)))
      (> (erl-k->fuel k) 3))
    (equal 
      (apply-k val (cons k rest))
      (apply-k
        (apply-erl-binop
          (node-binop->op (kont-expr->expr (erl-k->kont k)))
          (apply-k '(:nil) (list (erl-k (+ -1 (erl-k->fuel k)) (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))))
          (apply-k '(:nil) (list (erl-k (+ -2 (erl-k->fuel k)) (kont-expr (node-binop->right(kont-expr->expr (erl-k->kont k))))))))
        rest)))
  :in-theory (disable apply-k-of-append)
  :hints (("Goal" :use (:instance apply-k-of-append (klst1 (list k)) (klst2 rest) (klst (cons k rest)) (val val)))
          ("Goal'''" :expand (APPLY-K VAL (LIST K)))
          ("Subgoal 2" :in-theory (enable eval-k))
          ("Subgoal 1" :in-theory (enable eval-k))
          ("Subgoal 1''" :use (:instance apply-k-of-append
            (klst1 (list (ERL-K (+ -1 (ERL-K->FUEL K)) (KONT-EXPR (NODE-BINOP->LEFT (KONT-EXPR->EXPR (ERL-K->KONT K))))))) 
            (klst2 (list (ERL-K (+ -1 (ERL-K->FUEL K))
                                (KONT-BINOP-EXPR1 (NODE-BINOP->OP (KONT-EXPR->EXPR (ERL-K->KONT K)))
                                                  (NODE-BINOP->RIGHT (KONT-EXPR->EXPR (ERL-K->KONT K)))
                                NIL)))) 
            (klst (LIST (ERL-K (+ -1 (ERL-K->FUEL K))
                               (KONT-EXPR (NODE-BINOP->LEFT (KONT-EXPR->EXPR (ERL-K->KONT K)))))
                        (ERL-K (+ -1 (ERL-K->FUEL K))
                               (KONT-BINOP-EXPR1 (NODE-BINOP->OP (KONT-EXPR->EXPR (ERL-K->KONT K)))
                                                 (NODE-BINOP->RIGHT (KONT-EXPR->EXPR (ERL-K->KONT K)))
                              NIL)))) 
            (val '(:nil))))
          ("Subgoal 1'5'" :expand (:free (v) (apply-k v (LIST (ERL-K (+ -1 (ERL-K->FUEL K))
                                                                     (KONT-BINOP-EXPR1 (NODE-BINOP->OP (KONT-EXPR->EXPR (ERL-K->KONT K)))
                                                                                       (NODE-BINOP->RIGHT (KONT-EXPR->EXPR (ERL-K->KONT K)))
                                                                     NIL))))))
          ("Subgoal 1.3" :expand ((APPLY-K '(:FAULT) REST) (:free (o l r) (apply-erl-binop o l r))))
          ("Subgoal 1.1''" :use (:instance apply-k-of-append
            (klst1 (list (ERL-K (+ -2 (ERL-K->FUEL K)) (KONT-EXPR (NODE-BINOP->RIGHT (KONT-EXPR->EXPR (ERL-K->KONT K)))))))
            (klst2 (list (ERL-K (+ -2 (ERL-K->FUEL K))
                               (KONT-BINOP-EXPR2 (NODE-BINOP->OP (KONT-EXPR->EXPR (ERL-K->KONT K)))
                                                 (APPLY-K '(:NIL) (LIST (ERL-K (+ -1 (ERL-K->FUEL K))
                                                                               (KONT-EXPR (NODE-BINOP->LEFT (KONT-EXPR->EXPR (ERL-K->KONT K)))))))
                                                 NIL))))
            (klst (LIST (ERL-K (+ -2 (ERL-K->FUEL K))
                              (KONT-EXPR (NODE-BINOP->RIGHT (KONT-EXPR->EXPR (ERL-K->KONT K)))))
                        (ERL-K (+ -2 (ERL-K->FUEL K))
                              (KONT-BINOP-EXPR2 (NODE-BINOP->OP (KONT-EXPR->EXPR (ERL-K->KONT K)))
                                                (APPLY-K '(:NIL) (LIST (ERL-K (+ -1 (ERL-K->FUEL K)) 
                                                                              (KONT-EXPR (NODE-BINOP->LEFT (KONT-EXPR->EXPR (ERL-K->KONT K)))))))
                                                NIL))))
            (val '(:nil))))
          ("Subgoal 1.1'5'" :expand (:free (v) (apply-k v (LIST (ERL-K (+ -2 (ERL-K->FUEL K))
                                                                       (KONT-BINOP-EXPR2 (NODE-BINOP->OP (KONT-EXPR->EXPR (ERL-K->KONT K)))
                                                                                         (APPLY-K '(:NIL) (LIST (ERL-K (+ -1 (ERL-K->FUEL K))
                                                                                                                       (KONT-EXPR (NODE-BINOP->LEFT (KONT-EXPR->EXPR (ERL-K->KONT K)))))))
                                                                                         NIL))))))
          ("Subgoal 1.1.4" :expand ((APPLY-K '(:FAULT) REST) (:free (o l r) (apply-erl-binop o l r))))                                                                               
          ("Subgoal 1.1.2''" :expand (APPLY-K (APPLY-ERL-BINOP (NODE-BINOP->OP (KONT-EXPR->EXPR (ERL-K->KONT K))) 
                                                               (APPLY-K '(:NIL) (LIST (ERL-K (+ -1 (ERL-K->FUEL K)) (KONT-EXPR (NODE-BINOP->LEFT (KONT-EXPR->EXPR (ERL-K->KONT K)))))))
                                                               (APPLY-K '(:NIL) (LIST (ERL-K (+ -2 (ERL-K->FUEL K)) (KONT-EXPR (NODE-BINOP->RIGHT (KONT-EXPR->EXPR (ERL-K->KONT K)))))))) 
                                              NIL))))

(defrule stupid-acl2-2
  (equal (apply-k '(:fault) rest) '(:fault))
  :enable apply-k)


(defrule apply-k-of-binop-ensures
  (implies 
    (and
      (erl-val-p val)
      (erl-klst-p rest)
      (erl-k-p k)
      (equal (kont-kind (erl-k->kont k)) :expr)
      (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop)
      (not (equal (apply-k val (cons k rest)) (make-erl-val-fault)))
      (> (erl-k->fuel k) 3)
      (not (equal val (make-erl-val-fault))))
    (and (not (equal (apply-k '(:nil) (list (erl-k (+ -1 (erl-k->fuel k)) (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k))))))) (make-erl-val-fault)))    
         (not (equal (apply-k '(:nil) (list (erl-k (+ -2 (erl-k->fuel k)) (kont-expr (node-binop->right(kont-expr->expr (erl-k->kont k))))))) (make-erl-val-fault)))))  
    
    :disable apply-erl-binop-of-fault
    :use ((:instance apply-erl-binop-of-fault
      (op (NODE-BINOP->OP (KONT-EXPR->EXPR (ERL-K->KONT K))))
      (left (apply-k '(:nil) (list (erl-k (+ -1 (erl-k->fuel k)) (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k))))))))
      (right (apply-k '(:nil) (list (erl-k (+ -2 (erl-k->fuel k)) (kont-expr (node-binop->right(kont-expr->expr (erl-k->kont k))))))))))
    :hints (("Subgoal 2" :use 
      ((:instance apply-k-of-fault
          (val '(:FAULT))
          (klst REST))
      (:instance apply-k-of-fault
          (val '(:FAULT))
          (klst REST))))
          ))
