(in-package "ACL2")
(include-book "../core/eval-theorems")

(set-induction-depth-limit 1)

; Erl-State Module Theorems ----------------------------------------------------

; The theorems below reason about what happens the module field of an erl-state
; after various operations.

(defrule erl-state->module-of-eval-match
  (implies
    (erl-state-p s)
    (equal (erl-state->module (eval-match p s))
           (erl-state->module s)))
  :enable eval-match)

(defrule erl-state->module-of-match-args
  (implies
    (erl-state-p s)
    (equal (erl-state->module (match-args cs args s))
           (erl-state->module s)))
  :enable match-args)

(defrule erl-state->module-of-eval-clauses-when-consp
  (implies
    (erl-state-p s)
    (equal (erl-state->module (mv-nth 0 (eval-clauses-when-consp args cls s)))
           (erl-state->module s)))
  :enable eval-clauses-when-consp)

(defrule erl-state->module-of-eval-clauses
  (implies
    (erl-state-p s)
    (equal (erl-state->module (mv-nth 0 (eval-clauses args cls s)))
           (erl-state->module s)))
  :enable eval-clauses)