(in-package "ACL2")
(include-book "../core/top")

(set-induction-depth-limit 1)

; State Equivalence ------------------------------------------------------------

(defruled update-erl-state->in-when-only-diff-val
  (implies
    (and (equal (erl-state->module s1) (erl-state->module s2))
         (equal (erl-state->bind s1) (erl-state->bind s2))
         (equal (erl-state->world s1) (erl-state->world s2)))
    (equal (update-erl-state->in s1 v) (update-erl-state->in s2 v)))
  :enable update-erl-state->in)

(defruled apply-k-of-expr-when-only-diff-val
  (implies
    (and (wf-state-p s1)
         (wf-state-p s2)
         (equal (erl-state->module s1) (erl-state->module s2))
         (equal (erl-state->bind s1) (erl-state->bind s2))
         (equal (erl-state->world s1) (erl-state->world s2))
         (equal (kont-kind (erl-k->kont k)) :expr))
    (equal (apply-k s1 (cons k nil))
           (apply-k s2 (cons k nil))))
  :expand
    ((apply-k s1 (cons k nil))
     (apply-k s2 (cons k nil))
     (eval-k k s1)
     (eval-k k s2))
  :enable update-erl-state->in
  :use
    ((:instance update-erl-state->in-when-only-diff-val
        (s1 s1) (s2 s2) (v '(:none)))
     (:instance update-erl-state->in-when-only-diff-val
        (s1 s1)
        (s2 s2)
        (v (make-erl-val-excpt
            :err (make-erl-err :class (make-err-class-error)
                               :reason (make-exit-reason-if-clause)))))))

(defrule update-bind-mod-to-update-in
  (implies
    (equal (erl-state->world s1) (erl-state->world s2))
    (equal (update-erl-state->bind-mod
             s2
             (erl-state->bind s1)
             (erl-state->module s1))
           (update-erl-state->in s1 (erl-state->in s2))))
  :enable (update-erl-state->in update-erl-state->bind
           update-erl-state->mod update-erl-state->bind-mod))

