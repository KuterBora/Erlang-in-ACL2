(in-package "ACL2")
(include-book "../core/top")
(include-book "../state/top")


; Kont-Step for Consequitve Expressions ----------------------------------------

; eval-k -----------------------------------------------------------------------

(defrule eval-k-exprs->s
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :exprs))
    (equal (erl-s-klst->s (eval-k k s)) (erl-state-fix s)))
  :enable eval-k)

(defrule eval-k-exprs->klst
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :exprs))
    (equal 
      (erl-s-klst->klst (eval-k k s))
      (if (kont-exprs->exprs (erl-k->kont k))
          (list (make-erl-k 
                  :fuel (1- (erl-k->fuel k))
                  :kont
                    (make-kont-expr 
                      :expr (car (kont-exprs->exprs (erl-k->kont k)))))
                (make-erl-k
                  :fuel (1- (erl-k->fuel k))
                  :kont
                    (make-kont-exprs
                      :exprs (cdr (kont-exprs->exprs (erl-k->kont k))))))
          nil)))
  :enable eval-k)


; apply-k ----------------------------------------------------------------------

(defrule apply-k-of-exprs
  (implies
    (and (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :exprs)
         (consp (kont-exprs->exprs (erl-k->kont k))))
    (equal (apply-k s (cons k nil))
           (apply-k
            (apply-k 
              s
              (list (make-erl-k 
                      :fuel (1- (erl-k->fuel k))
                      :kont
                        (make-kont-expr 
                          :expr (car (kont-exprs->exprs (erl-k->kont k)))))))
            (list (make-erl-k
                    :fuel (1- (erl-k->fuel k))
                    :kont
                      (make-kont-exprs
                        :exprs (cdr (kont-exprs->exprs (erl-k->kont k)))))))))
  :enable apply-k-of-step
  :cases ((wf-state-p s)))

; apply-k when wf --------------------------------------------------------------

; no need, it seems