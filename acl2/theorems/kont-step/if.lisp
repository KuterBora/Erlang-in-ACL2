(in-package "ACL2")
(include-book "../core/eval-theorems")

; If Kont-Step -----------------------------------------------------------------

; The following theorems show that evaluating a continuation for an if
; expression is equivalent to calling the clause-evaluator with no argument for 
; pattern matching cases and then continuing with the body of the selected clause.

; Stepping the initial continuation
(local (defrule eval-k-of-expr-if->klst
  (implies
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :expr)
       (equal (node-kind (kont-expr->expr (erl-k->kont k))) :if)
       (not (equal (erl-val-kind (erl-state->in
                      (mv-nth 
                        0
                        (eval-clauses 
                          nil 
                          (node-if->clauses (kont-expr->expr (erl-k->kont k)))
                          s))))
                    :reject))
       (mv-nth 1 (eval-clauses 
                  nil 
                  (node-if->clauses (kont-expr->expr (erl-k->kont k))) s)))
    (equal 
      (erl-s-klst->klst (eval-k k s))
      (list 
        (make-erl-k 
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr 
            :expr (car (mv-nth 
                          1
                          (eval-clauses 
                            nil
                            (node-if->clauses (kont-expr->expr (erl-k->kont k))) s)))))
        (make-erl-k 
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-exprs
            :exprs (cdr (mv-nth 
                          1
                          (eval-clauses
                            nil
                            (node-if->clauses (kont-expr->expr (erl-k->kont k))) s))))))))
  :enable eval-k))

(local (defrule eval-k-of-expr-if->s
  (implies
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :expr)
       (equal (node-kind (kont-expr->expr (erl-k->kont k))) :if)
       (not (equal (erl-val-kind (erl-state->in
                      (mv-nth 
                        0
                        (eval-clauses 
                          nil 
                          (node-if->clauses (kont-expr->expr (erl-k->kont k)))
                          s))))
                    :reject))
       (mv-nth 1 (eval-clauses 
                  nil 
                  (node-if->clauses (kont-expr->expr (erl-k->kont k))) s)))
    (equal 
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k))


; apply-k with an if expression continuation is equivalent to finding the first
; clause with guards that hold, and evaluating the body of the clause -- assuming 
; there are no excpetion, rejection, or out-of-fuel errors.
;
; If evaluation succeeds for s and k, in the returned state
; is the result of evaluating the body of the selected clause.

(defrule apply-k-of-if
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 1)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :if))
    (b* (((erl-state s) s)
         ((erl-k k))
         ((mv (erl-state rs) body)
          (eval-clauses nil (node-if->clauses (kont-expr->expr k.kont)) s))
         ((if (equal (erl-val-kind rs.in) :reject)) t)
         ((unless body) t))
        (equal (apply-k s (list k)) 
               (apply-k (update-erl-state->in s (make-erl-val-none)) 
                        (list (make-erl-k :fuel (1- k.fuel)
                                          :kont (make-kont-expr :expr (car body)))
                              (make-erl-k :fuel (1- k.fuel)
                                          :kont (make-kont-exprs :exprs (cdr body)))))))))