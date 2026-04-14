(in-package "ACL2")
(include-book "../core/eval-theorems")

; Function Return Kont-Step ----------------------------------------------------

(defrule eval-k-of-function-return->klst
  (implies
    (and (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :function-return))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-function-return->s
  (implies
    (and (erl-state-p s) 
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :function-return))
    (equal
      (erl-s-klst->s (eval-k k s))
      (cond 
        ((not (wf-state-p s)) s)
        ((not (> (erl-k->fuel k) 0)) 
          (update-erl-state->in s (make-erl-val-flimit)))
        (t (update-erl-state->bind-mod
          s 
          (kont-function-return->bind (erl-k->kont k))
          (kont-function-return->module (erl-k->kont k)))))))
  :enable eval-k)