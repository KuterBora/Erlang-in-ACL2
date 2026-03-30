(in-package "ACL2")
(include-book "../core/eval-theorems")

; Match Kont-Step --------------------------------------------------------------

; The following theorems show that evaluating a continuation for a match
; expression is equivalent to evaluating the rhs, and then pattern matching it
; to the lhs.

; Stepping the initial continuation
(local (defrule eval-k-of-expr-match->klst
  (implies
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :expr)
       (equal (node-kind (kont-expr->expr (erl-k->kont k))) :match))
    (equal 
      (erl-s-klst->klst (eval-k k s))
      (list
        (make-erl-k 
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr :expr 
            (node-match->rhs (kont-expr->expr (erl-k->kont k)))))
        (make-erl-k :fuel (1- (erl-k->fuel k))
                    :kont
                      (make-kont-match 
                        :lhs (node-match->lhs (kont-expr->expr (erl-k->kont k))))))))
  :enable eval-k))

(local (defrule eval-k-of-expr-match->s
  (implies 
    (and
      (wf-state-p s)
      (erl-k-p k)
      (> (erl-k->fuel k) 0)
      (equal (kont-kind (erl-k->kont k)) :expr)
      (equal (node-kind (kont-expr->expr (erl-k->kont k))) :match))
    (equal (erl-s-klst->s (eval-k k s)) 
           (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k))


; Stepping the match continuation
(local (defrule eval-k-of-match->klst
  (implies 
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :match))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k))

(local (defrule eval-k-of-match->s
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
  :enable eval-k))


; apply-k with a match expression continuation is equivalent to evaluating the 
; rhs and then pattern matching to the lhs -- assuming there are no excpetion,
; rejection, or out-of-fuel errors.
;
; If evaluation succeeds for s and k, in the returned state
; - in will contain the value of evaluating rhs.
; - bind will contain any previous bindings and any new ones created by 
;   evaluating the rhs, and matching values in the rhs to free variables in thelhs.
;
; Rest: TODO

(defrule apply-k-of-match
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 2)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :match))
    (b* (((erl-state s) s)
         ((erl-k k))
         (rhs (node-match->rhs (kont-expr->expr k.kont)))
         (lhs (node-match->lhs (kont-expr->expr k.kont)))
         (rhs_res (apply-k (update-erl-state->in s (make-erl-val-none))
                           (list (make-erl-k :fuel (1- k.fuel) 
                                             :kont (make-kont-expr :expr rhs)))))
         ((unless (wf-state-p rhs_res)) t)
         (ms (eval-match lhs rhs_res))
         ((if (and (equal (erl-val-kind (erl-state->in ms)) :excpt)
                   (equal (exit-reason-kind 
                            (erl-err->reason (erl-val-excpt->err (erl-state->in ms)))) 
                        :badmatch)))
          t))
        (equal (apply-k s (list k)) (eval-match lhs rhs_res)))))