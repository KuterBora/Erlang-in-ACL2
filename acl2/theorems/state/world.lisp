(in-package "ACL2")
(include-book "../core/eval-theorems")

(set-induction-depth-limit 1)

; Erl-State World Theorems -----------------------------------------------------

; The theorems below reason about what happens the world field of an erl-state
; after various operations.

(defrule erl-state->world-of-eval-match
  (implies
    (erl-state-p s)
    (equal (erl-state->world (eval-match p s))
           (erl-state->world s)))
  :enable eval-match)

(defrule erl-state->world-of-match-args
  (implies
    (erl-state-p s)
    (equal (erl-state->world (match-args cs args s))
           (erl-state->world s)))
  :enable match-args)

(defrule erl-state->world-of-eval-clauses-when-consp
  (implies
    (erl-state-p s)
    (equal (erl-state->world (mv-nth 0 (eval-clauses-when-consp args cls s)))
           (erl-state->world s)))
  :enable eval-clauses-when-consp)

(defrule erl-state->world-of-eval-clauses
  (implies
    (erl-state-p s)
    (equal (erl-state->world (mv-nth 0 (eval-clauses args cls s)))
           (erl-state->world s)))
  :enable eval-clauses)

(defrule erl-state->world-of-eval-local-call
  (implies
    (erl-state-p s)
    (equal (erl-state->world (mv-nth 0 (eval-local-call s c args)))
           (erl-state->world s)))
  :enable eval-local-call)

(defrule erl-state->world-of-eval-remote-call
  (implies
    (erl-state-p s)
    (equal (erl-state->world (mv-nth 0 (eval-remote-call s m c args)))
           (erl-state->world s)))
  :enable eval-remote-call)

(defrule erl-state->world-of-eval-fun-call
  (implies
    (erl-state-p s)
    (equal (erl-state->world (mv-nth 0 (eval-fun-call s f args)))
           (erl-state->world s)))
  :enable eval-fun-call)

; The world field of an erl-state never changes during evaluation.
(defrule apply-k-of-world
  (implies 
    (and (erl-klst-p klst) (erl-state-p s))
    (equal (erl-state->world (apply-k s klst))
           (erl-state->world s)))
  :expand (eval-k (car klst) s)
  :enable (apply-k)
  :disable (apply-k-of-step apply-k-of-consp))

(defrule eval-k-of-world
  (implies 
    (and (erl-k-p k) (erl-state-p s))
    (equal (erl-state->world (erl-s-klst->s (eval-k k s)))
           (erl-state->world s)))
  :enable eval-k)