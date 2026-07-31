(in-package "ACL2")
(include-book "../core/top")

(set-induction-depth-limit 1)

; Properties of State Update ---------------------------------------------------

; There are also some rules on eval/erl-state.lisp

(defrule wf-state-of-update-erl-state->in
  (implies
    (not (or (equal (erl-val-kind v) :flimit)
             (equal (erl-val-kind v) :reject)
             (equal (erl-val-kind v) :excpt)))
    (wf-state-p (update-erl-state->in s v)))
  :enable wf-state-p)

(defrule wf-state-of-update-erl-state->bind
  (implies
    (wf-state-p s)
    (wf-state-p (update-erl-state->bind s b)))
  :enable wf-state-p)

(defrule wf-state-of-update-erl-state->in-bind
  (implies
    (not (or (equal (erl-val-kind v) :flimit)
             (equal (erl-val-kind v) :reject)
             (equal (erl-val-kind v) :excpt)))
    (wf-state-p (update-erl-state->in-bind s v b)))
  :enable wf-state-p)