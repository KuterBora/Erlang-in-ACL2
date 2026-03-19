(in-package "ACL2")
(include-book "../core/eval-theorems")


; Kont-Step for Atomic Expressions ---------------------------------------------


; The following theorems show the result of evaluating atomic expressions -- 
; integers, atoms, strings, empty lists, anononymous functions and variables.
;
; There are also some rules about excpetions, rejections, etc. 

(defrule apply-k-of-integer
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :integer))
    (b* (((erl-state s) s)
         ((erl-k k)))
        (equal 
          (apply-k s (list k))
          (update-erl-state->in 
            s 
            (make-erl-val-integer
              :val (node-integer->val (kont-expr->expr k.kont)))))))
  :enable eval-k)

(defrule apply-k-of-atom
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :atom))
    (b* (((erl-state s) s)
         ((erl-k k)))
        (equal 
          (apply-k s (list k))
          (update-erl-state->in 
            s
            (make-erl-val-atom
              :val (node-atom->val (kont-expr->expr k.kont)))))))
  :enable eval-k)

(defrule apply-k-of-string
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :string))
    (b* (((erl-state s) s)
         ((erl-k k)))
        (equal 
          (apply-k s (list k))
          (update-erl-state->in 
            s
            (string=>erl-cons 
              (node-string->val (kont-expr->expr k.kont)))))))
  :enable eval-k)

(defrule apply-k-of-empty-list
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :nil))
    (b* (((erl-state s) s)
         ((erl-k k)))
        (equal 
          (apply-k s (list k))
          (update-erl-state->in 
            s
            (make-erl-val-cons :lst nil)))))
  :enable eval-k)

(defrule apply-k-of-fun
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :fun)
         (erl-clause-list->arity (node-fun->cls (kont-expr->expr (erl-k->kont k)))))
    (b* (((erl-state s) s)
         ((erl-k k)))
        (update-erl-state->in 
          s
          (make-erl-val-fun
            :arity (erl-clause-list->arity (node-fun->cls (kont-expr->expr k.kont)))
            :cls (node-fun->cls (kont-expr->expr k.kont))
            :bind s.bind
            :module s.module))))
  :enable eval-k)

(defrule apply-k-of-var
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :var)
         (omap::assoc (node-var->id (kont-expr->expr (erl-k->kont k))) 
                      (erl-state->bind s)))
    (b* (((erl-state s) s)
         ((erl-k k)))
        (update-erl-state->in
          s 
          (omap::lookup 
            (node-var->id (kont-expr->expr k.kont)) 
            s.bind))))
  :enable eval-k)