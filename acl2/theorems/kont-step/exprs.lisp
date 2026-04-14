(in-package "ACL2")
(include-book "../core/eval-theorems")

; Kont-Step for Consequitve Expressions ----------------------------------------

(defrule eval-k-exprs->s
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :exprs))
    (equal (erl-s-klst->s (eval-k k s)) s))
  :enable eval-k)

(defrule eval-k-exprs->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :exprs)
         (kont-exprs->exprs (erl-k->kont k)))
    (equal 
      (erl-s-klst->klst (eval-k k s))
        (list (make-erl-k 
                :fuel (1- (erl-k->fuel k))
                :kont
                  (make-kont-expr 
                    :expr (car (kont-exprs->exprs (erl-k->kont k)))))
              (make-erl-k
                :fuel (1- (erl-k->fuel k))
                :kont
                  (make-kont-exprs
                    :exprs (cdr (kont-exprs->exprs (erl-k->kont k))))))))
  :enable eval-k)

(defrule eval-k-exprs-nil->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :exprs)
         (null (kont-exprs->exprs (erl-k->kont k))))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)