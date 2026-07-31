(in-package "ACL2")
(include-book "../core/top")
(include-book "../state/top")

; Cons Kont-Step ---------------------------------------------------------------

; The following theorems show that evaluating a continuation for a cons
; expression is equivalent to evaluating the car, evaluating the cdr,
; and then merging the result.

; eval-k -----------------------------------------------------------------------

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


; kont-cons-merge
(defrule eval-k-of-cons-merge->klst
  (implies
    (equal (kont-kind (erl-k->kont k)) :cons-merge)
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-cons-merge->s
  (implies
    (and (> (erl-k->fuel k) 0)
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



; apply-k  ---------------------------------------------------------------------

(defrule apply-k-of-expr-cons-1
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
                (node-cons->hd (kont-expr->expr (erl-k->kont k))))))))

(defruled apply-k-of-cons
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
                (kont-cons->cdr-expr (erl-k->kont k)))))))

(defrule apply-k-of-expr-cons-2
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 2)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons)
         (wf-state-p (apply-k 
                       s
                       (list (make-erl-k 
                               :fuel (1- (erl-k->fuel k))
                               :kont 
                                 (make-kont-expr 
                                   :expr
                                     (node-cons->hd (kont-expr->expr (erl-k->kont k)))))))))
    (equal (apply-k s (cons k nil))
           (apply-k
             (apply-k s
                      (list (make-erl-k 
                        :fuel (+ -2 (erl-k->fuel k)) 
                        :kont
                          (make-kont-expr 
                            :expr (node-cons->tl (kont-expr->expr (erl-k->kont k)))))))
              (list (make-erl-k 
                      :fuel (+ -2 (erl-k->fuel k))
                      :kont (make-kont-cons-merge 
                              :car-val
                                (erl-state->in
                                  (apply-k 
                                    s
                                    (list (make-erl-k 
                                            :fuel (1- (erl-k->fuel k))
                                            :kont 
                                              (make-kont-expr 
                                                :expr
                                                  (node-cons->hd (kont-expr->expr (erl-k->kont k))))))))
                              :car-bind
                                (erl-state->bind
                                  (apply-k 
                                    s
                                    (list (make-erl-k 
                                            :fuel (1- (erl-k->fuel k))
                                            :kont 
                                              (make-kont-expr
                                                :expr
                                                  (node-cons->hd (kont-expr->expr (erl-k->kont k))))))))))))))
  :cases ((wf-state-p s))
  :enable apply-k-of-cons
  :use
    (:instance apply-k-of-expr-when-only-diff-val
      (s1 (update-erl-state->bind
            (apply-k s (list (make-erl-k
                              :fuel (1- (erl-k->fuel k))
                              :kont (make-kont-expr
                                      :expr (node-cons->hd (kont-expr->expr (erl-k->kont k)))))))
            (erl-state->bind s)))
      (s2 s)
      (k (make-erl-k
           :fuel (+ -2 (erl-k->fuel k))
           :kont (make-kont-expr
                    :expr (node-cons->tl (kont-expr->expr (erl-k->kont k))))))))

(defrule apply-k-of-cons-merge-when-not-cons
  (implies
    (and (wf-state-p s)
         (not (equal (erl-val-kind (erl-state->in s)) :cons))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :cons-merge))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in
             s
             (make-erl-val-reject
               :err "cons-merge expects list, pairs are not supported"))))
  :enable apply-k-of-step)

(defrule apply-k-of-cons-merge-incompatible
  (implies
    (and (wf-state-p s)
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (not 
           (omap::compatiblep
             (erl-state->bind s)
             (kont-cons-merge->car-bind (erl-k->kont k))))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :cons-merge))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in
             s
             (make-erl-val-excpt
               :err (make-erl-err
                       :class (make-err-class-error)
                       :reason (make-exit-reason-badmatch
                                 :val (erl-state->in s)))))))
  :enable apply-k-of-step)

(defrule apply-k-of-cons-merge-compatible
  (implies
    (and (wf-state-p s)
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (omap::compatiblep
           (erl-state->bind s)
           (kont-cons-merge->car-bind (erl-k->kont k)))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :cons-merge))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in-bind
             s
             (make-erl-val-cons
               :lst (cons (kont-cons-merge->car-val (erl-k->kont k))
                          (erl-val-cons->lst (erl-state->in s))))
             (omap::update*
               (erl-state->bind s)
               (kont-cons-merge->car-bind (erl-k->kont k))))))
  :enable apply-k-of-step)


(defrule apply-k-of-expr-cons
  (implies
    (and (> (erl-k->fuel k) 3)
         (wf-state-p s)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons)
         (wf-state-p (apply-k s (list (make-erl-k 
                                        :fuel (1- (erl-k->fuel k))
                                        :kont (make-kont-expr 
                                                :expr (node-cons->hd (kont-expr->expr (erl-k->kont k))))))))
         (wf-state-p (apply-k s (list (make-erl-k 
                                        :fuel (+ -2 (erl-k->fuel k)) 
                                        :kont (make-kont-expr 
                                                :expr (node-cons->tl (kont-expr->expr (erl-k->kont k))))))))
        (equal
          (erl-val-kind
            (erl-state->in
              (apply-k s (list (make-erl-k 
                                 :fuel (+ -2 (erl-k->fuel k)) 
                                 :kont (make-kont-expr 
                                         :expr (node-cons->tl (kont-expr->expr (erl-k->kont k)))))))))
          :cons)
        (omap::compatiblep
          (erl-state->bind (apply-k s (list (make-erl-k 
                                              :fuel (1- (erl-k->fuel k))
                                              :kont (make-kont-expr 
                                                      :expr (node-cons->hd (kont-expr->expr (erl-k->kont k))))))))
          (erl-state->bind (apply-k s (list (make-erl-k 
                                              :fuel (+ -2 (erl-k->fuel k)) 
                                              :kont (make-kont-expr 
                                                      :expr (node-cons->tl (kont-expr->expr (erl-k->kont k))))))))))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in-bind
             (apply-k s (list (make-erl-k 
                                :fuel (+ -2 (erl-k->fuel k)) 
                                :kont (make-kont-expr 
                                        :expr (node-cons->tl (kont-expr->expr (erl-k->kont k)))))))
             
             (make-erl-val-cons
               :lst
                (cons (erl-state->in (apply-k s (list (make-erl-k
                                                        :fuel (1- (erl-k->fuel k))
                                                        :kont (make-kont-expr 
                                                                :expr (node-cons->hd (kont-expr->expr (erl-k->kont k))))))))
                      (erl-val-cons->lst
                        (erl-state->in (apply-k s (list (make-erl-k
                                                          :fuel (+ -2 (erl-k->fuel k)) 
                                                          :kont (make-kont-expr 
                                                                  :expr (node-cons->tl (kont-expr->expr (erl-k->kont k)))))))))))
             (omap::update*
               (erl-state->bind (apply-k s (list (make-erl-k 
                                                   :fuel (+ -2 (erl-k->fuel k)) 
                                                   :kont (make-kont-expr 
                                                           :expr (node-cons->tl (kont-expr->expr (erl-k->kont k))))))))
               (erl-state->bind (apply-k s (list (make-erl-k 
                                                   :fuel (1- (erl-k->fuel k))
                                                   :kont (make-kont-expr 
                                                           :expr (node-cons->hd (kont-expr->expr (erl-k->kont k)))))))))))))


; apply-k when wf --------------------------------------------------------------

(defrule cons-hd-well-formed
  (implies
    (and (> (erl-k->fuel k) 3)
         (wf-state-p (apply-k s (cons k nil)))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons))
    (wf-state-p
      (apply-k s (list (make-erl-k 
                         :fuel (1- (erl-k->fuel k)) 
                         :kont (make-kont-expr 
                                 :expr (node-cons->hd (kont-expr->expr (erl-k->kont k)))))))))
  :disable apply-k-of-expr-cons-1
  :use (:instance apply-k-of-expr-cons-1))



(defrule apply-k-of-expr-cons-not-cons
  (implies
    (and
      (wf-state-p s)
      (> (erl-k->fuel k) 2)
      (equal (kont-kind (erl-k->kont k)) :expr)
      (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons)
      (wf-state-p (apply-k s (list (make-erl-k 
                                        :fuel (1- (erl-k->fuel k))
                                        :kont (make-kont-expr 
                                                :expr (node-cons->hd (kont-expr->expr (erl-k->kont k))))))))
      (wf-state-p (apply-k s (list (make-erl-k 
                                     :fuel (+ -2 (erl-k->fuel k)) 
                                     :kont (make-kont-expr 
                                             :expr (node-cons->tl (kont-expr->expr (erl-k->kont k))))))))
      (not
        (equal
          (erl-val-kind
            (erl-state->in
              (apply-k s (list (make-erl-k 
                                :fuel (+ -2 (erl-k->fuel k)) 
                                :kont (make-kont-expr 
                                        :expr (node-cons->tl (kont-expr->expr (erl-k->kont k)))))))))
          :cons)))
    (not (wf-state-p (apply-k s (cons k nil)))))
    :disable (apply-k-of-expr-cons-1 apply-k-of-expr-cons-2)
    :use (:instance apply-k-of-expr-cons-2))

(defrule apply-k-of-expr-cons-is-cons-when-wf
  (implies
    (and (> (erl-k->fuel k) 3)
         (wf-state-p (apply-k s (cons k nil)))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons))
    (equal
      (erl-val-kind
        (erl-state->in
          (apply-k
            s
            (list (make-erl-k 
                    :fuel (+ -2 (erl-k->fuel k)) 
                    :kont (make-kont-expr 
                            :expr (node-cons->tl (kont-expr->expr (erl-k->kont k)))))))))
      :cons))
  :disable (apply-k-of-expr-cons-1 apply-k-of-expr-cons-2 apply-k-of-expr-cons-not-cons)
  :use (:instance apply-k-of-expr-cons-not-cons))

(defrule apply-k-of-expr-cons-incompatible
  (implies
    (and
      (wf-state-p s)
      (> (erl-k->fuel k) 2)
      (equal (kont-kind (erl-k->kont k)) :expr)
      (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons)
      (wf-state-p (apply-k s (list (make-erl-k 
                                        :fuel (1- (erl-k->fuel k))
                                        :kont (make-kont-expr 
                                                :expr (node-cons->hd (kont-expr->expr (erl-k->kont k))))))))
      (wf-state-p (apply-k s (list (make-erl-k 
                                     :fuel (+ -2 (erl-k->fuel k)) 
                                     :kont (make-kont-expr 
                                             :expr (node-cons->tl (kont-expr->expr (erl-k->kont k))))))))
      (equal
        (erl-val-kind
          (erl-state->in
            (apply-k s (list (make-erl-k 
                              :fuel (+ -2 (erl-k->fuel k)) 
                              :kont (make-kont-expr 
                                      :expr (node-cons->tl (kont-expr->expr (erl-k->kont k)))))))))
        :cons)
      (not (omap::compatiblep
             (erl-state->bind (apply-k s (list (make-erl-k 
                                                 :fuel (1- (erl-k->fuel k))
                                                 :kont (make-kont-expr 
                                                         :expr (node-cons->hd (kont-expr->expr (erl-k->kont k))))))))
             (erl-state->bind (apply-k s (list (make-erl-k 
                                                 :fuel (+ -2 (erl-k->fuel k)) 
                                                 :kont (make-kont-expr 
                                                         :expr (node-cons->tl (kont-expr->expr (erl-k->kont k)))))))))))
    (not (wf-state-p (apply-k s (cons k nil))))))

(defrule cons-compatible
  (implies
    (and (> (erl-k->fuel k) 3)
         (wf-state-p (apply-k s (cons k nil)))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons))
    (omap::compatiblep
      (erl-state->bind (apply-k s (list (make-erl-k 
                                          :fuel (1- (erl-k->fuel k))
                                          :kont (make-kont-expr 
                                                  :expr (node-cons->hd (kont-expr->expr (erl-k->kont k))))))))
      (erl-state->bind (apply-k s (list (make-erl-k 
                                          :fuel (+ -2 (erl-k->fuel k)) 
                                          :kont (make-kont-expr 
                                                  :expr (node-cons->tl (kont-expr->expr (erl-k->kont k))))))))))
  :disable (apply-k-of-expr-cons-1 apply-k-of-expr-cons-2 apply-k-of-expr-cons-incompatible)
  :use (:instance apply-k-of-expr-cons-incompatible))


(defrule apply-k-of-expr-cons-wf
  (implies
    (and (> (erl-k->fuel k) 3)
         (wf-state-p (apply-k s (cons k nil)))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in-bind
             (apply-k s (list (make-erl-k 
                                :fuel (+ -2 (erl-k->fuel k)) 
                                :kont (make-kont-expr 
                                        :expr (node-cons->tl (kont-expr->expr (erl-k->kont k)))))))
             
             (make-erl-val-cons
               :lst
                (cons (erl-state->in (apply-k s (list (make-erl-k
                                                        :fuel (1- (erl-k->fuel k))
                                                        :kont (make-kont-expr 
                                                                :expr (node-cons->hd (kont-expr->expr (erl-k->kont k))))))))
                      (erl-val-cons->lst
                        (erl-state->in (apply-k s (list (make-erl-k
                                                          :fuel (+ -2 (erl-k->fuel k)) 
                                                          :kont (make-kont-expr 
                                                                  :expr (node-cons->tl (kont-expr->expr (erl-k->kont k)))))))))))
             (omap::update*
               (erl-state->bind (apply-k s (list (make-erl-k 
                                                   :fuel (+ -2 (erl-k->fuel k)) 
                                                   :kont (make-kont-expr 
                                                           :expr (node-cons->tl (kont-expr->expr (erl-k->kont k))))))))
               (erl-state->bind (apply-k s (list (make-erl-k 
                                                   :fuel (1- (erl-k->fuel k))
                                                   :kont (make-kont-expr 
                                                           :expr (node-cons->hd (kont-expr->expr (erl-k->kont k)))))))))))))