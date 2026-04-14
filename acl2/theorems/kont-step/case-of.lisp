(in-package "ACL2")
(include-book "../core/eval-theorems")

; Case-of Kont-Step ------------------------------------------------------------

; The following theorems show that evaluating a continuation for a case of
; expression is equivalent to evaluating the argument of the case and then
; calling the the clause-evaluator the result of evaluation and the clauses of 
; the case, and then continuing with the body of the selected clause.

; expr-case-of
(defrule eval-k-of-expr-case-of->klst
  (implies
    (and
       (erl-state-p s)
       (erl-k-p k)
       (equal (kont-kind (erl-k->kont k)) :expr)
       (equal (node-kind (kont-expr->expr (erl-k->kont k))) :case-of))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (if (and (wf-state-p s) (> (erl-k->fuel k) 0))
          (list 
            (make-erl-k 
              :fuel (1- (erl-k->fuel k))
              :kont (make-kont-expr 
                :expr (node-case-of->expr (kont-expr->expr (erl-k->kont k)))))
            (make-erl-k 
              :fuel (1- (erl-k->fuel k))
              :kont (make-kont-case-of
                :clauses (node-case-of->clauses (kont-expr->expr (erl-k->kont k))))))
          nil)))
  :enable eval-k)

(defrule eval-k-of-expr-case-of->s
  (implies
    (and
       (erl-state-p s)
       (erl-k-p k)
       (equal (kont-kind (erl-k->kont k)) :expr)
       (equal (node-kind (kont-expr->expr (erl-k->kont k))) :case-of))
    (equal
      (erl-s-klst->s (eval-k k s)) 
      (cond
        ((not (wf-state-p s)) s)
        ((not (> (erl-k->fuel k) 0))
         (update-erl-state->in s (make-erl-val-flimit)))
        (t (update-erl-state->in s (make-erl-val-none))))))
  :enable eval-k)


; kont-case-of
(defrule eval-k-of-case-of->klst
  (implies
    (and
       (erl-state-p s)
       (erl-k-p k)
       (equal (kont-kind (erl-k->kont k)) :case-of))
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
                   (list (erl-state->in s))
                   (kont-case-of->clauses (erl-k->kont k))
                   s))))
           :reject)
         nil)
        ((not
           (mv-nth
             1
             (eval-clauses 
               (list (erl-state->in s))
               (kont-case-of->clauses (erl-k->kont k))
               s)))
         nil)
        (t (list 
             (make-erl-k 
               :fuel (1- (erl-k->fuel k))
               :kont
                 (make-kont-expr 
                  :expr
                    (car 
                      (mv-nth 
                        1
                        (eval-clauses 
                          (list (erl-state->in s))
                          (kont-case-of->clauses (erl-k->kont k))
                          s)))))
             (make-erl-k 
               :fuel (1- (erl-k->fuel k))
               :kont
                 (make-kont-exprs
                   :exprs
                     (cdr 
                       (mv-nth 
                         1
                         (eval-clauses 
                           (list (erl-state->in s))
                           (kont-case-of->clauses (erl-k->kont k))
                           s))))))))))
  :enable eval-k)

(defrule eval-k-of-case-of->s
  (implies
    (and
       (erl-state-p s) 
       (erl-k-p k)
       (equal (kont-kind (erl-k->kont k)) :case-of))
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
                   (list (erl-state->in s))
                   (kont-case-of->clauses (erl-k->kont k))
                   s))))
           :reject)
         (mv-nth 
           0
           (eval-clauses 
             (list (erl-state->in s))
             (kont-case-of->clauses (erl-k->kont k))
             s)))
        ((not 
          (mv-nth 
            1 
            (eval-clauses 
              (list (erl-state->in s))
              (kont-case-of->clauses (erl-k->kont k))
              s)))
         (update-erl-state->in 
           s
           (make-erl-val-excpt 
             :err (make-erl-err :class (make-err-class-error)
                                :reason (make-exit-reason-case-clause 
                                          :val (erl-state->in s))))))
        (t (update-erl-state->in
             (mv-nth
               0
               (eval-clauses
                 (list (erl-state->in s))
                 (kont-case-of->clauses (erl-k->kont k))
                 s))
             (make-erl-val-none))))))
  :enable eval-k)