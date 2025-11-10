(in-package "ACL2")
(include-book "erl-eval")
(include-book "eval-theorems")

(set-induction-depth-limit 1)

; Erlang Unop ------------------------------------------------------------------

; apply-k of an unop expression is equivalent to evaluating the subexpression
; and then applying the unop.
(defrule apply-k-of-unop
  (implies
    (and
      ; The state and the continuations are well formed
      (erl-state-p s)
      (erl-k-p k)
      (erl-klst-p rest)

      ; The expression is of type binop
      (equal (kont-kind (erl-k->kont k)) :expr)
      (equal (node-kind (kont-expr->expr (erl-k->kont k))) :unop)

      ; There has been no rejection or exception, and fuel has not ran out
      (not (equal (erl-val-kind (erl-state->in s)) :flimit))
      (not (equal (erl-val-kind (erl-state->in s)) :reject))
      (not (equal (erl-val-kind (erl-state->in s)) :excpt))

      ; TODO: It is possible to remove these constraints, though not trivially
      ; Wheter it would provide any practical use is a different question.
      (not (equal (erl-val-kind (erl-state->in (apply-k s (cons k rest)))) :flimit))
      (not (equal (erl-val-kind (erl-state->in (apply-k s (cons k rest)))) :reject))
      (not (equal (erl-val-kind (erl-state->in (apply-k s (cons k rest)))) :excpt))

      ; 3 is the minimum fuel required to evalue a binop expression
      ; TODO: is this true?
      (> (erl-k->fuel k) 3))
    ; Bind variables to make the proof more readable
    (b* 
      ((s.bind (erl-state->bind s))
       (fuel (erl-k->fuel k))
       (expr (erl-k (+ -1 fuel) (kont-expr (node-unop->expr (kont-expr->expr (erl-k->kont k))))))
       (op (node-unop->op (kont-expr->expr (erl-k->kont k))))
       ((erl-state state) (apply-k (make-erl-state :bind s.bind) (list expr)))
       (bind (erl-state->bind state))
       (val (erl-state->in state)))

      ; The body of the theorem
      (equal
        (apply-k s (cons k rest))        
        (apply-k 
          (make-erl-state 
            :in (apply-erl-unop op val)
            :bind bind)
          rest))
        ))
  :in-theory (disable apply-k-of-append)
  :hints 
    (("Goal" :use (:instance apply-k-of-append (klst1 (list k)) (klst2 rest) (klst (cons k rest)) (s s)))
     ("Goal'''" :expand (apply-k s (list k)))
     ("Goal'4'" :in-theory (enable eval-k))
     ("Goal'6'" 
      :use 
        (:instance apply-k-of-append
          (klst1 (list (erl-k (+ -1 (erl-k->fuel k)) (kont-expr (node-unop->expr (kont-expr->expr (erl-k->kont k)))))))
          (klst2 (list (erl-k (+ -1 (erl-k->fuel k)) (kont-unop (node-unop->op (kont-expr->expr (erl-k->kont k)))))))
          (klst (list (erl-k (+ -1 (erl-k->fuel k)) (kont-expr (node-unop->expr (kont-expr->expr (erl-k->kont k)))))
                      (erl-k (+ -1 (erl-k->fuel k)) (kont-unop (node-unop->op (kont-expr->expr (erl-k->kont k)))))))
          (s (erl-state '(:none) (erl-state->bind s)))))
    ("Goal'9'"
      :expand 
        (:free (v) 
               (apply-k v (list (erl-k (+ -1 (erl-k->fuel k)) (kont-unop (node-unop->op (kont-expr->expr (erl-k->kont k)))))))))
    ("Subgoal 3''"
      :use (:instance erl-states-are-equal-if-fields-are-equal
            (x (APPLY-K
                (ERL-STATE '(:NONE) (ERL-STATE->BIND S))
                (LIST
                  (ERL-K
                  (+ -1 (ERL-K->FUEL K))
                  (KONT-EXPR (NODE-UNOP->EXPR (KONT-EXPR->EXPR (ERL-K->KONT K)))))
                  (ERL-K
                  (+ -1 (ERL-K->FUEL K))
                  (KONT-UNOP (NODE-UNOP->OP (KONT-EXPR->EXPR (ERL-K->KONT K))))))))
            (y (ERL-STATE
                  (APPLY-ERL-UNOP
                  (NODE-UNOP->OP (KONT-EXPR->EXPR (ERL-K->KONT K)))
                  (ERL-STATE->IN
                    (APPLY-K
                    (ERL-STATE '(:NONE) (ERL-STATE->BIND S))
                    (LIST
                      (ERL-K
                      (+ -1 (ERL-K->FUEL K))
                      (KONT-EXPR
                            (NODE-UNOP->EXPR (KONT-EXPR->EXPR (ERL-K->KONT K)))))))))
                  (ERL-STATE->BIND
                  (APPLY-K
                    (ERL-STATE '(:NONE) (ERL-STATE->BIND S))
                    (LIST
                    (ERL-K
                      (+ -1 (ERL-K->FUEL K))
                      (KONT-EXPR
                            (NODE-UNOP->EXPR (KONT-EXPR->EXPR (ERL-K->KONT K))))))))))
            (klst rest)))))
    

; Erlang Binop -----------------------------------------------------------------

; apply-k of a binop expression is equivalent to evaluating the left and right 
; subexpressions and then applying the binop.
(defrule apply-k-of-binop
  (implies
    (and
      ; The state and the continuations are well formed
      (erl-state-p s)
      (erl-k-p k)
      (erl-klst-p rest)

      ; The expression is of type binop
      (equal (kont-kind (erl-k->kont k)) :expr)
      (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop)

      ; There has been no rejection or exception, and fuel has not ran out
      (not (equal (erl-val-kind (erl-state->in s)) :flimit))
      (not (equal (erl-val-kind (erl-state->in s)) :reject))
      (not (equal (erl-val-kind (erl-state->in s)) :excpt))

      ; TODO: It is possible to remove these constraints, though not trivially
      ; Wheter it would provide any practical use is a different question.
      (not (equal (erl-val-kind (erl-state->in (apply-k s (cons k rest)))) :flimit))
      (not (equal (erl-val-kind (erl-state->in (apply-k s (cons k rest)))) :reject))
      (not (equal (erl-val-kind (erl-state->in (apply-k s (cons k rest)))) :excpt))

      ; 3 is the minimum fuel required to evalue a binop expression
      (> (erl-k->fuel k) 3))
    ; Bind variables to make the proof more readable
    (b* 
      ((s.bind (erl-state->bind s))
       (fuel (erl-k->fuel k))
       (left (erl-k (+ -1 fuel) (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k))))))
       (right (erl-k (+ -2 fuel) (kont-expr (node-binop->right (kont-expr->expr (erl-k->kont k))))))
       (op (node-binop->op (kont-expr->expr (erl-k->kont k))))
       ((erl-state ls) (apply-k (make-erl-state :bind s.bind) (list left)))
       ((erl-state rs) (apply-k (make-erl-state :bind s.bind) (list right)))
       (l.bind (erl-state->bind ls))
       (l.val (erl-state->in ls))
       (r.bind (erl-state->bind rs))
       (r.val (erl-state->in rs))

       ; TODO: relax these constarints
       ((unless (omap::compatiblep r.bind l.bind)) t))

      ; The body of the theorem
      (equal
        (apply-k s (cons k rest))        
        (apply-k 
          (make-erl-state 
            :in (apply-erl-binop op l.val r.val)
            :bind (omap::update* r.bind l.bind))
          rest))
        ))
  :in-theory (disable apply-k-of-append)
  :hints 
    (("Goal" :use (:instance apply-k-of-append (klst1 (list k)) (klst2 rest) (klst (cons k rest)) (s s)))
     ("Goal'''" :expand (apply-k s (list k)))
     ("Goal'4'" :in-theory (enable eval-k))
     ("Goal'6'" 
      :use 
        (:instance apply-k-of-append
          (klst1 (list (erl-k (+ -1 (erl-k->fuel k)) (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))))
          (klst2 (list (erl-k (+ -1 (erl-k->fuel k)) (kont-binop-expr1 (node-binop->op (kont-expr->expr (erl-k->kont k)))
                                                                       (node-binop->right (kont-expr->expr (erl-k->kont k)))
                                                                       (erl-state->bind s)))))
          (klst (list (erl-k (+ -1 (erl-k->fuel k)) (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))
                      (erl-k (+ -1 (erl-k->fuel k)) (kont-binop-expr1 (node-binop->op (kont-expr->expr (erl-k->kont k)))
                                                                      (node-binop->right (kont-expr->expr (erl-k->kont k)))
                                                                      (erl-state->bind s)))))
            (s (erl-state '(:none) (erl-state->bind s)))))
    ("Goal'9'"
      :expand 
        (:free (v) (apply-k v (list (erl-k (+ -1 (erl-k->fuel k)) 
                                           (kont-binop-expr1 (node-binop->op (kont-expr->expr (erl-k->kont k)))
                                                             (node-binop->right (kont-expr->expr (erl-k->kont k)))
                                                             (erl-state->bind s)))))))
    ("Subgoal 3''"
      :use (:instance apply-k-of-append
            (klst1 (list (erl-k (+ -2 (erl-k->fuel k)) (kont-expr (node-binop->right (kont-expr->expr (erl-k->kont k)))))))
            (klst2 (list (erl-k (+ -2 (erl-k->fuel k)) 
                                (kont-binop-expr2 
                                  (node-binop->op (kont-expr->expr (erl-k->kont k)))
                                  (erl-state->in (apply-k (erl-state '(:none) (erl-state->bind s))
                                                          (list (erl-k (+ -1 (erl-k->fuel k)) 
                                                                       (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k))))))))
                                  (erl-state->bind (apply-k (erl-state '(:none) (erl-state->bind s))
                                                            (list (erl-k (+ -1 (erl-k->fuel k))
                                                                         (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k))))))))))))
            (klst (list (erl-k (+ -2 (erl-k->fuel k)) (kont-expr (node-binop->right (kont-expr->expr (erl-k->kont k)))))
                        (erl-k (+ -2 (erl-k->fuel k)) 
                              (kont-binop-expr2 
                                (node-binop->op (kont-expr->expr (erl-k->kont k)))
                                (erl-state->in (apply-k (erl-state '(:none) (erl-state->bind s))
                                                        (list (erl-k (+ -1 (erl-k->fuel k)) 
                                                                    (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k))))))))
                                (erl-state->bind (apply-k (erl-state '(:none) (erl-state->bind s))
                                                          (list (erl-k (+ -1 (erl-k->fuel k))
                                                                      (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k))))))))))))
            (s (erl-state '(:none) (erl-state->bind s)))))
    ("Subgoal 3'5'"
      :expand 
        (:free (v) 
               (apply-k v 
                  (list (erl-k (+ -2 (erl-k->fuel k)) 
                               (kont-binop-expr2 
                                  (node-binop->op (kont-expr->expr (erl-k->kont k)))
                                  (erl-state->in (apply-k (erl-state '(:none) (erl-state->bind s))
                                                          (list (erl-k (+ -1 (erl-k->fuel k)) 
                                                                       (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k))))))))
                                  (erl-state->bind (apply-k (erl-state '(:none) (erl-state->bind s))
                                                            (list (erl-k (+ -1 (erl-k->fuel k))
                                                                         (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k))))))))))))))))