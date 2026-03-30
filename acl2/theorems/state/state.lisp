(in-package "ACL2")
(include-book "../core/eval-theorems")
(include-book "../kont-step/top")


; State Rules ------------------------------------------------------------------

; The following rules reason about how the erl-state changes during evaluation.

; The world never changes
(defrule apply-k-of-world
  (implies 
    (and (erl-k-p k) (erl-state-p s))
    (equal (erl-state->world (apply-k s (cons k nil)))
           (erl-state->world s)))
  :expand (eval-k k s))