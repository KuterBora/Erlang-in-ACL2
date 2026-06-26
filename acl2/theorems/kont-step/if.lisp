(in-package "ACL2")
(include-book "../core/eval-theorems")

; If Kont-Step -----------------------------------------------------------------

; The following theorems show that evaluating a continuation for an if
; expression is equivalent to calling the clause-evaluator with no argument for 
; pattern matching cases and then continuing with the body of the selected clause.

(defrule eval-k-of-expr-if->klst
  (implies
    (and
       (erl-state-p s)
       (erl-k-p k)
       (equal (kont-kind (erl-k->kont k)) :expr)
       (equal (node-kind (kont-expr->expr (erl-k->kont k))) :if))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (cond
        ((not (wf-state-p s)) nil)
        ((not (> (erl-k->fuel k) 0)) nil)
        ((equal
          (erl-val-kind
            (erl-state->in
              (mv-nth 
                0
                (eval-clauses 
                  nil 
                  (node-if->clauses (kont-expr->expr (erl-k->kont k)))
                  s))))
          :reject)
         nil)
       ((not (mv-nth
              1
              (eval-clauses
                nil
                (node-if->clauses (kont-expr->expr (erl-k->kont k))) s)))
        nil)
      (t
       (list
         (make-erl-k 
           :fuel (1- (erl-k->fuel k))
           :kont
             (make-kont-expr 
               :expr
                 (car
                   (mv-nth
                     1
                     (eval-clauses 
                       nil
                       (node-if->clauses
                         (kont-expr->expr (erl-k->kont k))) s)))))
         (make-erl-k 
           :fuel (1- (erl-k->fuel k))
           :kont
             (make-kont-exprs
              :exprs
                (cdr
                  (mv-nth 
                    1
                    (eval-clauses
                      nil
                      (node-if->clauses 
                        (kont-expr->expr (erl-k->kont k))) s))))))))))
    :enable eval-k)

(defrule eval-k-of-expr-if->s
  (implies
    (and
       (erl-state-p s) 
       (erl-k-p k)
       (equal (kont-kind (erl-k->kont k)) :expr)
       (equal (node-kind (kont-expr->expr (erl-k->kont k))) :if))
    (equal
      (erl-s-klst->s (eval-k k s))
      (cond
        ((not (wf-state-p s)) s)
        ((not (> (erl-k->fuel k) 0))
         (update-erl-state->in s (make-erl-val-flimit)))
        ((equal
          (erl-val-kind
            (erl-state->in
              (mv-nth 
                0
                (eval-clauses 
                  nil 
                  (node-if->clauses (kont-expr->expr (erl-k->kont k)))
                  s))))
          :reject)
         (mv-nth 
           0
           (eval-clauses 
             nil 
             (node-if->clauses (kont-expr->expr (erl-k->kont k)))
             s)))
        ((not (mv-nth 
                1 
                (eval-clauses 
                  nil 
                  (node-if->clauses (kont-expr->expr (erl-k->kont k))) s)))
         (update-erl-state->in
           s
           (make-erl-val-excpt 
             :err (make-erl-err :class (make-err-class-error)
                                :reason (make-exit-reason-if-clause)))))
        (t (update-erl-state->in s (make-erl-val-none))))))
  :enable eval-k)