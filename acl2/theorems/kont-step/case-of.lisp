(in-package "ACL2")
(include-book "../core/eval-theorems")


; Case-of Kont-Step ------------------------------------------------------------


; The following theorems show that evaluating a continuation for a case of
; expression is equivalent to evaluating the argument of the case and then
; calling the the clause-evaluator the result of evaluation and the clauses of 
; the case, and then continuing with the body of the selected clause.

; Stepping the initial continuation
(defrule eval-k-of-expr-case-of->klst
  (implies
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :expr)
       (equal (node-kind (kont-expr->expr (erl-k->kont k))) :case-of))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (list 
        (make-erl-k 
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr 
            :expr (node-case-of->expr (kont-expr->expr (erl-k->kont k)))))
        (make-erl-k 
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-case-of
            :clauses (node-case-of->clauses (kont-expr->expr (erl-k->kont k))))))))
  :enable eval-k)

(defrule eval-k-of-expr-case-of->s
  (implies
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :expr)
       (equal (node-kind (kont-expr->expr (erl-k->kont k))) :case-of))
    (equal
      (erl-s-klst->s (eval-k k s)) (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)


; Stepping the case-of continuation
(defrule eval-k-of-case-of->klst
  (implies
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :case-of)
       (not (equal (erl-val-kind (erl-state->in
                    (mv-nth 
                      0
                      (eval-clauses 
                          (list (erl-state->in s))
                          (kont-case-of->clauses (erl-k->kont k))
                          s))))
                :reject))
       (mv-nth 1 (eval-clauses 
                  (list (erl-state->in s))
                  (kont-case-of->clauses (erl-k->kont k))
                  s)))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (list 
        (make-erl-k 
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr 
            :expr (car (mv-nth 
                          1
                          (eval-clauses 
                            (list (erl-state->in s))
                            (kont-case-of->clauses (erl-k->kont k))
                            s)))))
        (make-erl-k 
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-exprs
            :exprs (cdr (mv-nth 
                          1
                          (eval-clauses 
                            (list (erl-state->in s))
                            (kont-case-of->clauses (erl-k->kont k))
                            s))))))))
  :enable eval-k)

(defrule eval-k-of-case-of->s
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :case-of)
         (not (equal (erl-val-kind (erl-state->in
                       (mv-nth 
                         0
                         (eval-clauses 
                           (list (erl-state->in s))
                           (kont-case-of->clauses (erl-k->kont k))
                           s))))
                     :reject))
         (mv-nth 1 (eval-clauses 
                     (list (erl-state->in s))
                     (kont-case-of->clauses (erl-k->kont k))
                     s)))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)


; apply-k with a case-of expression continuation is equivalent to evaluating the
; argument of the case, and the calling the clause evaluator with the result and
; the clauses of the case expression -- assuming there are no excpetion, rejection, or out-of-fuel errors.
;
; If evaluation succeeds for s and k, in the returned state is the result of 
; evaluating the body of the selected clause combined with effects of evaluating 
; the argument to case expression.

(defrule apply-k-of-case-of
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 2)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :case-of))
    (b* (((erl-state s) s)
         ((erl-k k))
         (x (node-case-of->expr (kont-expr->expr k.kont)))
         (x_res (apply-k (update-erl-state->in s (make-erl-val-none))
                         (list (make-erl-k :fuel (1- k.fuel) 
                                           :kont (make-kont-expr :expr x)))))
         ((unless (wf-state-p x_res)) t)
         ((mv (erl-state rs) body)
          (eval-clauses (list (erl-state->in x_res)) 
                        (node-case-of->clauses (kont-expr->expr k.kont)) 
                        x_res))
         ((if (equal (erl-val-kind rs.in) :reject)) t)
         ((unless body) t))
        (equal (apply-k s (list k)) 
               (apply-k (update-erl-state->in x_res (make-erl-val-none)) 
                        (list (make-erl-k :fuel (- k.fuel 2)
                                          :kont (make-kont-expr :expr (car body)))
                              (make-erl-k :fuel (- k.fuel 2)
                                          :kont (make-kont-exprs :exprs (cdr body)))))))))