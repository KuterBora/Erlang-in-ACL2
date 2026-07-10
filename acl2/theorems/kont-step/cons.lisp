(in-package "ACL2")
(include-book "../core/top")
(include-book "../state/top")

; Cons Kont-Step ---------------------------------------------------------------

; The following theorems show that evaluating a continuation for a cons
; expression is equivalent to evaluating the car, evaluating the cdr,
; and then merging the result.

; expr-cons
(defrule eval-k-of-expr-cons->klst
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons))
    (equal 
      (erl-s-klst->klst (eval-k k s))
      (list 
        (make-erl-k 
          :fuel (1- (erl-k->fuel k))
          :kont 
            (make-kont-expr 
              :expr
                (node-cons->hd (kont-expr->expr (erl-k->kont k)))))
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont 
            (make-kont-cons 
              :cdr-expr
                (node-cons->tl
                  (kont-expr->expr (erl-k->kont k)))
              :bind-0 (erl-state->bind s))))))
  :enable eval-k)

(defrule eval-k-of-expr-cons->s
  (implies 
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons))
    (equal (erl-s-klst->s (eval-k k s)) 
           (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)

(local (defrule apply-k-of-expr-cons-1
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons))
    (equal (apply-k s (cons k nil))
           (apply-k
            (apply-k 
              s
              (list (make-erl-k 
                      :fuel (1- (erl-k->fuel k))
                      :kont 
                        (make-kont-expr 
                          :expr
                            (node-cons->hd (kont-expr->expr (erl-k->kont k)))))))
            (list (make-erl-k
                    :fuel (1- (erl-k->fuel k))
                    :kont 
                      (make-kont-cons 
                        :cdr-expr
                          (node-cons->tl
                            (kont-expr->expr (erl-k->kont k)))
                        :bind-0 (erl-state->bind s)))))))
  :enable apply-k-of-step
  :cases ((wf-state-p s))
  :use
    (:instance apply-k-of-expr-when-only-diff-val
      (s1 (update-erl-state->in s (make-erl-val-none)))
      (s2 s)
      (k (make-erl-k 
          :fuel (1- (erl-k->fuel k))
          :kont 
            (make-kont-expr 
              :expr
                (node-cons->hd (kont-expr->expr (erl-k->kont k)))))))))

; kont-cons
(defrule eval-k-of-cons->klst
  (implies 
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :cons))
    (equal (erl-s-klst->klst (eval-k k s))
           (list (make-erl-k 
                   :fuel (1- (erl-k->fuel k)) 
                   :kont
                     (make-kont-expr 
                       :expr (kont-cons->cdr-expr (erl-k->kont k))))
                 (make-erl-k 
                   :fuel (1- (erl-k->fuel k))
                   :kont (make-kont-cons-merge 
                           :car-val (erl-state->in s)
                           :car-bind (erl-state->bind s))))))
  :enable eval-k)

(defrule eval-k-of-cons->s
  (implies 
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :cons))
    (equal (erl-s-klst->s (eval-k k s)) 
           (update-erl-state->in-bind 
             s 
             (make-erl-val-none)
             (kont-cons->bind-0 (erl-k->kont k)))))
  :enable eval-k)

(local (defrule apply-k-of-cons
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :cons))
    (equal (apply-k s (cons k nil))
           (apply-k
            (update-erl-state->bind s (kont-cons->bind-0 (erl-k->kont k)))
            (list (make-erl-k 
                    :fuel (1- (erl-k->fuel k)) 
                    :kont
                      (make-kont-expr 
                        :expr (kont-cons->cdr-expr (erl-k->kont k))))
                  (make-erl-k 
                    :fuel (1- (erl-k->fuel k))
                    :kont (make-kont-cons-merge 
                            :car-val (erl-state->in s)
                            :car-bind (erl-state->bind s)))))))
  :enable apply-k-of-step
  :use
    (:instance apply-k-of-expr-when-only-diff-val
      (s1 (update-erl-state->in-bind s (make-erl-val-none) (kont-cons->bind-0 (erl-k->kont k))))
      (s2 (update-erl-state->bind s (kont-cons->bind-0 (erl-k->kont k))))
      (k (make-erl-k 
          :fuel (1- (erl-k->fuel k))
          :kont 
            (make-kont-expr 
              :expr
                (kont-cons->cdr-expr (erl-k->kont k))))))))

(local (defrule apply-k-of-cons-wf
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :cons)
         (wf-state-p (apply-k s (cons k nil))))
    (equal (apply-k s (cons k nil))
           (apply-k
              (update-erl-state->bind s (kont-cons->bind-0 (erl-k->kont k)))
              (list (make-erl-k 
                      :fuel (1- (erl-k->fuel k)) 
                      :kont
                        (make-kont-expr 
                          :expr (kont-cons->cdr-expr (erl-k->kont k))))
                    (make-erl-k 
                      :fuel (1- (erl-k->fuel k))
                      :kont (make-kont-cons-merge 
                              :car-val (erl-state->in s)
                              :car-bind (erl-state->bind s)))))))))

(local (defrule apply-k-of-expr-cons-2
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 2)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons)
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
  :cases ((wf-state-p s))))





; kont-cons-merge
(defrule eval-k-of-cons-merge->klst
  (implies
    (and (erl-state-p s)
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :cons-merge))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-cons-merge->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :cons-merge))
    (equal
      (erl-s-klst->s (eval-k k s))
      (cond
        ((not (equal (erl-val-kind (erl-state->in s)) :cons))
         (update-erl-state->in
           s
           (make-erl-val-reject
             :err "cons-merge expects list, pairs are not supported")))
        ((not 
          (omap::compatiblep
            (erl-state->bind s)
            (kont-cons-merge->car-bind (erl-k->kont k))))
         (update-erl-state->in
           s
           (make-erl-val-excpt
             :err (make-erl-err
                    :class (make-err-class-error)
                    :reason (make-exit-reason-badmatch
                              :val (erl-state->in s))))))
        (t (update-erl-state->in-bind
             s
             (make-erl-val-cons
               :lst (cons (kont-cons-merge->car-val (erl-k->kont k))
                          (erl-val-cons->lst (erl-state->in s))))
             (omap::update*
               (erl-state->bind s)
               (kont-cons-merge->car-bind (erl-k->kont k))))))))
  :enable eval-k)