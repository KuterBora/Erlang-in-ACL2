(in-package "ACL2")
(include-book "../core/eval-theorems")


; Binop Kont-Step --------------------------------------------------------------

; The following theorems show that evaluating a continuation for a binop 
; expression is equivalent to evaluating the left operand, the right operand
; and then applying the binop, as would happen in Erlang's control flow.
; There are also some rules about excpetions, rejections, etc. 

(defrule eval-k-of-expr-binop->klst
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (list
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr
                  :expr (node-binop->left
                           (kont-expr->expr (erl-k->kont k)))))
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-binop-expr1
                  :op (node-binop->op
                        (kont-expr->expr (erl-k->kont k)))
                  :right (node-binop->right
                           (kont-expr->expr (erl-k->kont k)))
                  :bind-0 (erl-state->bind s))))))
  :enable eval-k)

(defrule eval-k-of-expr-binop->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)

(defrule eval-k-of-binop-expr1->klst
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr1))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (list
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr
                  :expr (kont-binop-expr1->right (erl-k->kont k))))
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-binop-expr2
                  :op (kont-binop-expr1->op (erl-k->kont k))
                  :val (erl-state->in s)
                  :left-bind (erl-state->bind s))))))
  :enable eval-k)

(defrule eval-k-of-binop-expr1->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr1))
    (equal
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->bind
        s
        (kont-binop-expr1->bind-0 (erl-k->kont k)))))
  :enable eval-k)

(defrule eval-k-of-binop-expr2->klst
  (implies 
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr2))
    (equal (erl-s-klst->klst (eval-k k s))
           nil))
  :enable eval-k)

; binop-expr-2

(defrule eval-k-of-binop-expr2-compatible->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr2)
         (omap::compatiblep (erl-state->bind s)
                            (kont-binop-expr2->left-bind (erl-k->kont k))))
    (equal
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in-bind
        s
        (apply-erl-binop
          (kont-binop-expr2->op (erl-k->kont k))
          (kont-binop-expr2->val (erl-k->kont k))
          (erl-state->in s))
        (omap::update*
          (erl-state->bind s)
          (kont-binop-expr2->left-bind (erl-k->kont k))))))
  :enable eval-k)

(defrule eval-k-of-binop-expr2-incompatible->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr2)
         (not (omap::compatiblep (erl-state->bind s)
                                 (kont-binop-expr2->left-bind (erl-k->kont k)))))
    (equal
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in
        s
        (make-erl-val-excpt
          :err (make-erl-err
                 :class (make-err-class-error)
                 :reason (make-exit-reason-badmatch
                           :val (erl-state->in s)))))))
  :enable eval-k)

; TODO ask mark if I can do something like this.
(defrule eval-k-of-binop-expr2->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr2))
    (equal
      (erl-s-klst->s (eval-k k s))
      (if (omap::compatiblep (erl-state->bind s)
                             (kont-binop-expr2->left-bind (erl-k->kont k)))
          (update-erl-state->in-bind
            s
            (apply-erl-binop
              (kont-binop-expr2->op (erl-k->kont k))
              (kont-binop-expr2->val (erl-k->kont k))
              (erl-state->in s))
            (omap::update*
              (erl-state->bind s)
              (kont-binop-expr2->left-bind (erl-k->kont k))))
          (update-erl-state->in
            s
            (make-erl-val-excpt
              :err (make-erl-err
                    :class (make-err-class-error)
                    :reason (make-exit-reason-badmatch
                              :val (erl-state->in s)))))))))