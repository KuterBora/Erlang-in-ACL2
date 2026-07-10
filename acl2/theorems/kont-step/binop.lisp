(in-package "ACL2")
(include-book "../core/eval-theorems")

; Binop Kont-Step --------------------------------------------------------------

; The following theorems show that evaluating a continuation for a binop 
; expression is equivalent to evaluating the left operand, the right operand
; and then applying the binop, as would happen in Erlang's control flow.
; There are also some rules about excpetions, rejections, etc. 

; expr-binop
(defrule eval-k-of-expr-binop->klst
  (implies
    (and (> (erl-k->fuel k) 0)
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
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop))
    (equal (erl-s-klst->s (eval-k k s)) (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)

(defrule apply-k-of-expr-binop-1
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop))
    (equal (apply-k s (cons k nil))
           (apply-k
            (apply-k 
              (update-erl-state->in s (make-erl-val-none))
              (list (make-erl-k
                      :fuel (1- (erl-k->fuel k))
                      :kont (make-kont-expr
                              :expr (node-binop->left
                                      (kont-expr->expr (erl-k->kont k)))))))
            (list (make-erl-k
                    :fuel (1- (erl-k->fuel k))
                    :kont (make-kont-binop-expr1
                            :op (node-binop->op
                                  (kont-expr->expr (erl-k->kont k)))
                            :right (node-binop->right
                                      (kont-expr->expr (erl-k->kont k)))
                            :bind-0 (erl-state->bind s)))))))
  :enable apply-k-of-step
  :cases ((wf-state-p s)))


; kont-binop-expr1
(defrule eval-k-of-binop-expr1->klst
  (implies
    (and (> (erl-k->fuel k) 0)
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
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr1))
    (equal
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->bind
        s
        (kont-binop-expr1->bind-0 (erl-k->kont k)))))
  :enable eval-k)


(defrule apply-k-of-binop-expr1
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr1))
    (equal (apply-k s (cons k nil))
           (apply-k (update-erl-state->bind s (kont-binop-expr1->bind-0 (erl-k->kont k)))
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
                                :left-bind (erl-state->bind s)))))))
  :enable apply-k-of-step)

(defrule apply-k-of-binop-expr1-wf
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr1)
         (wf-state-p (apply-k s (cons k nil))))
    (equal (apply-k s (cons k nil))
           (apply-k (update-erl-state->bind s (kont-binop-expr1->bind-0 (erl-k->kont k)))
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
                                :left-bind (erl-state->bind s))))))))

(defrule apply-k-of-expr-binop-2
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 2)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop)
         (wf-state-p (apply-k (update-erl-state->in s (make-erl-val-none))
                              (list (make-erl-k
                                      :fuel (1- (erl-k->fuel k))
                                      :kont (make-kont-expr
                                              :expr (node-binop->left
                                                      (kont-expr->expr (erl-k->kont k)))))))))
    (equal (apply-k s (cons k nil))
           (apply-k
            (apply-k (update-erl-state->bind
                      (apply-k (update-erl-state->in s (make-erl-val-none))
                               (list (make-erl-k
                                        :fuel (1- (erl-k->fuel k))
                                        :kont (make-kont-expr
                                                :expr (node-binop->left
                                                        (kont-expr->expr (erl-k->kont k)))))))
                      (erl-state->bind s))
                    (list (make-erl-k
                            :fuel (+ -2 (erl-k->fuel k))
                            :kont (make-kont-expr
                                    :expr (node-binop->right (kont-expr->expr (erl-k->kont k)))))))
            (list (make-erl-k
                    :fuel (+ -2 (erl-k->fuel k))
                    :kont (make-kont-binop-expr2
                            :op (node-binop->op (kont-expr->expr (erl-k->kont k)))
                            :val (erl-state->in
                                   (apply-k (update-erl-state->in s (make-erl-val-none))
                                            (list (make-erl-k
                                                      :fuel (1- (erl-k->fuel k))
                                                      :kont (make-kont-expr
                                                              :expr (node-binop->left
                                                                      (kont-expr->expr (erl-k->kont k))))))))
                            :left-bind (erl-state->bind
                                         (apply-k (update-erl-state->in s (make-erl-val-none))
                                                  (list (make-erl-k
                                                      :fuel (1- (erl-k->fuel k))
                                                      :kont (make-kont-expr
                                                              :expr (node-binop->left
                                                                      (kont-expr->expr (erl-k->kont k))))))))))))))
  :cases ((wf-state-p s)))


; kont-binop-expr2
(defrule eval-k-of-binop-expr2->klst
  (implies 
    (equal (kont-kind (erl-k->kont k)) :binop-expr2)
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-binop-expr2->s
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr2))
    (equal
      (erl-s-klst->s (eval-k k s))
      (cond 
        ((not (omap::compatiblep 
                (erl-state->bind s)
                (kont-binop-expr2->left-bind (erl-k->kont k))))
          (update-erl-state->in
            s
            (make-erl-val-excpt
              :err (make-erl-err
                    :class (make-err-class-error)
                    :reason (make-exit-reason-badmatch
                              :val (erl-state->in s))))))
        
        (t
          (update-erl-state->in-bind
            s
            (apply-erl-binop
              (kont-binop-expr2->op (erl-k->kont k))
              (kont-binop-expr2->val (erl-k->kont k))
              (erl-state->in s))
            (omap::update*
              (erl-state->bind s)
              (kont-binop-expr2->left-bind (erl-k->kont k))))))))
  :enable eval-k)

(defrule apply-k-of-binop-expr2-compatible
  (implies
    (and (wf-state-p s)
         (omap::compatiblep 
           (erl-state->bind s)
           (kont-binop-expr2->left-bind (erl-k->kont k)))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr2))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in-bind
                s
                (apply-erl-binop
                  (kont-binop-expr2->op (erl-k->kont k))
                  (kont-binop-expr2->val (erl-k->kont k))
                  (erl-state->in s))
                (omap::update*
                  (erl-state->bind s)
                  (kont-binop-expr2->left-bind (erl-k->kont k))))))
  :enable apply-k-of-step)

(defrule apply-k-of-binop-expr2-incompatible
  (implies
    (and (wf-state-p s)
         (not (omap::compatiblep 
                (erl-state->bind s)
                (kont-binop-expr2->left-bind (erl-k->kont k))))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr2))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in
            s
            (make-erl-val-excpt
              :err (make-erl-err
                    :class (make-err-class-error)
                    :reason (make-exit-reason-badmatch
                              :val (erl-state->in s)))))))
  :enable apply-k-of-step)

(defrule compatibility-of-apply-k-of-binop-expr2-wf
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr2)
         (wf-state-p (apply-k s (cons k nil))))
    (omap::compatiblep 
      (erl-state->bind s)
      (kont-binop-expr2->left-bind (erl-k->kont k))))
  :disable apply-k-of-binop-expr2-incompatible
  :use (:instance apply-k-of-binop-expr2-incompatible))

(defrule apply-k-of-binop-expr2-wf
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :binop-expr2)
         (wf-state-p (apply-k s (cons k nil))))
    (equal (apply-k s (cons k nil))
        (update-erl-state->in-bind
          s
          (apply-erl-binop
            (kont-binop-expr2->op (erl-k->kont k))
            (kont-binop-expr2->val (erl-k->kont k))
            (erl-state->in s))
          (omap::update*
            (erl-state->bind s)
            (kont-binop-expr2->left-bind (erl-k->kont k)))))))

(defrule apply-k-of-expr-binop-long
  (implies
    (and (> (erl-k->fuel k) 3)
         (wf-state-p s)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop)
         (wf-state-p
           (apply-k
             (update-erl-state->in s (make-erl-val-none))
             (list (make-erl-k
                     :fuel (1- (erl-k->fuel k))
                     :kont (make-kont-expr
                             :expr (node-binop->left
                                     (kont-expr->expr (erl-k->kont k))))))))
        (wf-state-p
          (apply-k
            (update-erl-state->bind
              (apply-k (update-erl-state->in s (make-erl-val-none))
                       (list (make-erl-k
                                 :fuel (1- (erl-k->fuel k))
                                 :kont (make-kont-expr
                                         :expr (node-binop->left
                                                 (kont-expr->expr (erl-k->kont k)))))))
              (erl-state->bind s))
            (list (make-erl-k
                    :fuel (+ -2 (erl-k->fuel k))
                    :kont (make-kont-expr
                            :expr (node-binop->right (kont-expr->expr (erl-k->kont k))))))))
        (omap::compatiblep
          (erl-state->bind
            (apply-k
              (update-erl-state->bind
                (apply-k (update-erl-state->in s (make-erl-val-none))
                         (list (make-erl-k
                                 :fuel (1- (erl-k->fuel k))
                                 :kont (make-kont-expr
                                          :expr (node-binop->left
                                                  (kont-expr->expr (erl-k->kont k)))))))
                (erl-state->bind s))
              (list (make-erl-k
                      :fuel (+ -2 (erl-k->fuel k))
                      :kont (make-kont-expr
                              :expr (node-binop->right (kont-expr->expr (erl-k->kont k))))))))
          (erl-state->bind
              (apply-k (update-erl-state->in s (make-erl-val-none))
                       (list (make-erl-k
                               :fuel (1- (erl-k->fuel k))
                               :kont (make-kont-expr
                                       :expr (node-binop->left
                                               (kont-expr->expr (erl-k->kont k))))))))))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in-bind
            (apply-k
              (update-erl-state->bind
                (apply-k (update-erl-state->in s (make-erl-val-none))
                         (list (make-erl-k
                                 :fuel (1- (erl-k->fuel k))
                                 :kont (make-kont-expr
                                         :expr (node-binop->left
                                                 (kont-expr->expr (erl-k->kont k)))))))
                (erl-state->bind s))
              (list (make-erl-k
                      :fuel (+ -2 (erl-k->fuel k))
                      :kont (make-kont-expr
                              :expr (node-binop->right (kont-expr->expr (erl-k->kont k)))))))
            (apply-erl-binop
              (node-binop->op (kont-expr->expr (erl-k->kont k)))
              (erl-state->in
                (apply-k (update-erl-state->in s (make-erl-val-none))
                         (list (make-erl-k
                                 :fuel (1- (erl-k->fuel k))
                                 :kont (make-kont-expr
                                         :expr (node-binop->left
                                                 (kont-expr->expr (erl-k->kont k))))))))
              (erl-state->in
                (apply-k
                  (update-erl-state->bind
                    (apply-k (update-erl-state->in s (make-erl-val-none))
                             (list (make-erl-k
                                     :fuel (1- (erl-k->fuel k))
                                      :kont (make-kont-expr
                                              :expr (node-binop->left
                                                      (kont-expr->expr (erl-k->kont k)))))))
                    (erl-state->bind s))
              (list (make-erl-k
                      :fuel (+ -2 (erl-k->fuel k))
                      :kont (make-kont-expr
                              :expr (node-binop->right (kont-expr->expr (erl-k->kont k)))))))))
            (omap::update*
              (erl-state->bind
                (apply-k
                  (update-erl-state->bind
                    (apply-k (update-erl-state->in s (make-erl-val-none))
                             (list (make-erl-k
                                     :fuel (1- (erl-k->fuel k))
                                     :kont (make-kont-expr
                                              :expr (node-binop->left
                                                      (kont-expr->expr (erl-k->kont k)))))))
                    (erl-state->bind s))
                  (list (make-erl-k
                          :fuel (+ -2 (erl-k->fuel k))
                          :kont (make-kont-expr
                                  :expr (node-binop->right (kont-expr->expr (erl-k->kont k))))))))
              (erl-state->bind
                  (apply-k (update-erl-state->in s (make-erl-val-none))
                           (list (make-erl-k
                                   :fuel (1- (erl-k->fuel k))
                                   :kont (make-kont-expr
                                            :expr (node-binop->left
                                                    (kont-expr->expr (erl-k->kont k)))))))))))))