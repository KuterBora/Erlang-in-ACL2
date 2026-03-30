(in-package "ACL2")
(include-book "../core/eval-theorems")

; Function Return Kont-Step ----------------------------------------------------

; Stepping the function-return continuation
(local (defrule eval-k-of-function-return->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :function-return))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k))

(local (defrule eval-k-of-function-return->s
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :function-return))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->bind-mod
            s 
            (kont-function-return->bind (erl-k->kont k))
            (kont-function-return->module (erl-k->kont k)))))
  :enable eval-k))