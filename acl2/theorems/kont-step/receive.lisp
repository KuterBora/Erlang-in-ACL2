(in-package "ACL2")
(include-book "../core/top")
(include-book "../state/top")

; Receuve Kont-Step ------------------------------------------------------------

; The following theorems show that evaluating a continuation for a match
; expression is equivalent to evaluating the rhs, and then pattern matching it
; to the lhs.

; TODO: eval-k counterpart

(defrule apply-k-of-expr-receive
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :receive))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in (erl-state-fix s)
             (make-erl-val-receive
               :klst (list (make-erl-k
                             :fuel (erl-k->fuel k)
                             :kont (make-kont-receive
                                     :clauses (node-receive->cls
                                                (kont-expr->expr (erl-k->kont k))))))))))
  :enable (apply-k-of-step eval-k))

(defrule apply-k-of-in-receive
  (implies
    (and (equal (erl-val-kind (erl-state->in s)) :receive)
         (erl-klst-p klst)
         (consp klst))
    (equal (apply-k s klst)
           (update-erl-state->in (erl-state-fix s)
             (make-erl-val-receive
               :klst (append (erl-val-receive->klst (erl-state->in s)) klst)))))
  :expand ((apply-k s klst)))