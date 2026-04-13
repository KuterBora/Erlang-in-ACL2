(in-package "ACL2")
(include-book "../core/eval-theorems")

; Match Kont-Step --------------------------------------------------------------

; The following theorems show that evaluating a continuation for a match
; expression is equivalent to evaluating the rhs, and then pattern matching it
; to the lhs.

; expr-match
(defrule eval-k-of-expr-match->klst
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :match))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (list
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr
                  :expr (node-match->rhs
                           (kont-expr->expr (erl-k->kont k)))))
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-match
                  :lhs (node-match->lhs
                         (kont-expr->expr (erl-k->kont k))))))))
  :enable eval-k)

(defrule eval-k-of-expr-match->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :match))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)

; kont-match
(defrule eval-k-of-match->klst
  (implies 
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :match))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-match-ok->s
  (implies 
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :match)
       (not (and (equal (erl-val-kind (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s))) :excpt)
                 (equal (exit-reason-kind 
                          (erl-err->reason (erl-val-excpt->err (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s))))) 
                        :badmatch))))
    (equal (erl-s-klst->s (eval-k k s)) (eval-match (kont-match->lhs (erl-k->kont k)) s)))
  :enable eval-k)

(defrule eval-k-of-match-badmatch->s
  (implies 
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :match)
       (and (equal (erl-val-kind (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s))) :excpt)
            (equal (exit-reason-kind 
                    (erl-err->reason (erl-val-excpt->err (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s))))) 
                  :badmatch)))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->in
             s
             (make-erl-val-excpt 
               :err (make-erl-err :class (make-err-class-error) 
                                  :reason (make-exit-reason-badmatch :val (erl-state->in s)))))))
  :enable eval-k)

; Combined to general rewrite rule
(defrule eval-k-of-match->s
  (implies 
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :match))
    (equal 
      (erl-s-klst->s (eval-k k s)) 
      (if (not (and (equal (erl-val-kind (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s))) :excpt)
                    (equal (exit-reason-kind 
                              (erl-err->reason (erl-val-excpt->err (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s))))) 
                            :badmatch)))
          (eval-match (kont-match->lhs (erl-k->kont k)) s)
          (update-erl-state->in
             s
             (make-erl-val-excpt 
               :err (make-erl-err :class (make-err-class-error) 
                                  :reason (make-exit-reason-badmatch :val (erl-state->in s))))))))
  :enable eval-k)

(defrule eval-k-of-match->s-no-constraint
  (implies 
    (and
       (erl-state-p s) 
       (erl-k-p k)
       (equal (kont-kind (erl-k->kont k)) :match))
    (equal 
      (erl-s-klst->s (eval-k k s)) 
      (cond 
        ((not (wf-state-p s)) s)
        ((not (> (erl-k->fuel k) 0)) (update-erl-state->in s (make-erl-val-flimit)))
        ((not (and (equal (erl-val-kind (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s))) :excpt)
                    (equal (exit-reason-kind 
                              (erl-err->reason (erl-val-excpt->err (erl-state->in (eval-match (kont-match->lhs (erl-k->kont k)) s))))) 
                            :badmatch)))
          (eval-match (kont-match->lhs (erl-k->kont k)) s))
        (t (update-erl-state->in
             s
             (make-erl-val-excpt 
               :err (make-erl-err :class (make-err-class-error) 
                                  :reason (make-exit-reason-badmatch :val (erl-state->in s)))))))))
  :enable eval-k)