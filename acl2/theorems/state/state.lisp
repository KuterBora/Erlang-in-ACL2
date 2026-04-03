(in-package "ACL2")
(include-book "../core/eval-theorems")
(include-book "../kont-step/top")

(set-induction-depth-limit 1)

;; TODO
; rules about wf-state-p
; make rewrite rules fire

(defrule crock-1
  (implies 
    (and (erl-state-p s)
         (not (wf-state-p s)))
    (equal (erl-s-klst->s (eval-k k s)) s))
  :enable eval-k)

(defrule crock-2
  (implies 
    (and (erl-state-p s)
         (not (wf-state-p s)))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-match-crock
  (implies
    (erl-state-p s)
    (equal (erl-state->world (eval-match p s))
           (erl-state->world s)))
  :enable eval-match)

(defrule match-args-crock
  (implies
    (erl-state-p s)
    (equal (erl-state->world (match-args cs args s))
           (erl-state->world s)))
  :enable match-args)

(defrule eval-clauses-when-consp-crock
  (implies
    (erl-state-p s)
    (equal (erl-state->world (mv-nth 0 (eval-clauses-when-consp args cls s)))
           (erl-state->world s)))
  :enable eval-clauses-when-consp)

(defrule eval-clauses-crock
  (implies
    (erl-state-p s)
    (equal (erl-state->world (mv-nth 0 (eval-clauses args cls s)))
           (erl-state->world s)))
  :enable eval-clauses)

(defrule eval-local-call-crock
  (implies
    (erl-state-p s)
    (equal (erl-state->world (mv-nth 0 (eval-local-call s c args)))
           (erl-state->world s)))
  :enable eval-local-call)

(defrule eval-remote-call-crock
  (implies
    (erl-state-p s)
    (equal (erl-state->world (mv-nth 0 (eval-remote-call s m c args)))
           (erl-state->world s)))
  :enable eval-remote-call)

(defrule eval-fun-call-crock
  (implies
    (erl-state-p s)
    (equal (erl-state->world (mv-nth 0 (eval-fun-call s f args)))
           (erl-state->world s)))
  :enable eval-fun-call)

; State Rules ------------------------------------------------------------------

; The following rules reason about how the erl-state changes during evaluation.

; The world never changes
(defrule apply-k-of-world
  (implies 
    (and (erl-klst-p klst) (erl-state-p s))
    (equal (erl-state->world (apply-k s klst))
           (erl-state->world s)))
  :enable (apply-k)
  :expand (eval-k (car klst) s)
  :disable (apply-k-of-step apply-k-of-consp))

(defrule kont-kind-crock
  (implies (and (erl-k-p k))
           (equal (car (erl-k->kont k)) (kont-kind (erl-k->kont k))))
  :enable (kont-kind erl-k-p kont-p erl-k->kont))

(defrule update->in-crock
  (equal (erl-val-kind (erl-state->in (update-erl-state->in s val)))
         (erl-val-kind val)))

(defrule fuel-crock
  (not (wf-state-p (update-erl-state->in s '(:flimit))))
  :enable wf-state-p)

(defrule apply-k-of-module
  (implies 
    (and (erl-k-p k) 
         (wf-state-p s)
         (> (erl-k->fuel k) 0)
         (not (equal (kont-kind (erl-k->kont k)) :function-return))
         (wf-state-p (apply-k s (cons k nil))))
    (equal (erl-state->module (apply-k s (cons k nil)))
           (erl-state->module s)))
  :expand (kont-kind (erl-k->kont k))
  ; :hints 
  ;   (("Subgoal 14" :by nil)
  ;   )
    )