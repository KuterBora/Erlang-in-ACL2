(in-package "ACL2")
(include-book "../core/eval-theorems")

; Cons Kont-Step ---------------------------------------------------------------

; The following theorems show that evaluating a continuation for a cons
; expression is equivalent to evaluating the car, evaluating the cdr,
; and then merging the result.

; expr-cons
(defrule eval-k-of-expr-cons->klst
  (implies
    (and (erl-state-p s) 
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons))
    (equal 
      (erl-s-klst->klst (eval-k k s))
      (cond 
        ((not (wf-state-p s)) nil)
        ((not (> (erl-k->fuel k) 0)) nil)
          
        (t (list 
             (make-erl-k 
              :fuel (1- (erl-k->fuel k))
              :kont (make-kont-expr :expr 
                (node-cons->hd (kont-expr->expr (erl-k->kont k)))))
             (make-erl-k :fuel (1- (erl-k->fuel k))
                         :kont 
                          (make-kont-cons 
                            :cdr-expr (node-cons->tl (kont-expr->expr (erl-k->kont k)))
                            :bind-0 (erl-state->bind s))))))))
  :enable eval-k)

(defrule eval-k-of-expr-cons->s
  (implies 
    (and (erl-state-p s)
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons))
    (equal (erl-s-klst->s (eval-k k s)) 
           (cond
             ((not (wf-state-p s)) s)
             ((not (> (erl-k->fuel k) 0))
              (update-erl-state->in s (make-erl-val-flimit)))
             (t (update-erl-state->in s (make-erl-val-none))))))
  :enable eval-k)

; kont-cons
(defrule eval-k-of-cons->klst
  (implies 
    (and (erl-state-p s) 
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :cons))
    (equal (erl-s-klst->klst (eval-k k s))
           (if (and (wf-state-p s) (> (erl-k->fuel k) 0))
               (list (make-erl-k 
                      :fuel (1- (erl-k->fuel k)) 
                      :kont (make-kont-expr 
                              :expr (kont-cons->cdr-expr (erl-k->kont k))))
                     (make-erl-k 
                      :fuel (1- (erl-k->fuel k))
                      :kont (make-kont-cons-merge 
                              :car-val (erl-state->in s)
                              :car-bind (erl-state->bind s))))
              nil)))
  :enable eval-k)

(defrule eval-k-of-cons->s
  (implies 
    (and (erl-state-p s) 
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :cons))
    (equal (erl-s-klst->s (eval-k k s)) 
           (cond
             ((not (wf-state-p s)) s)
             ((not (> (erl-k->fuel k) 0))
              (update-erl-state->in s (make-erl-val-flimit)))
             (t (update-erl-state->in-bind 
                  s 
                  (make-erl-val-none)
                  (kont-cons->bind-0 (erl-k->kont k)))))))
  :enable eval-k)

; kont-cons-merge
(defrule eval-k-of-cons-merge->klst
  (implies
    (and (erl-state-p s)
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :cons-merge))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-cons-merge-cons-compatible->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :cons-merge)
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (omap::compatiblep (erl-state->bind s)
                            (kont-cons-merge->car-bind (erl-k->kont k))))
    (equal
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in-bind
        s
        (make-erl-val-cons
          :lst (cons (kont-cons-merge->car-val (erl-k->kont k))
                     (erl-val-cons->lst (erl-state->in s))))
        (omap::update*
          (erl-state->bind s)
          (kont-cons-merge->car-bind (erl-k->kont k))))))
  :enable eval-k)

(defrule eval-k-of-cons-merge-cons-incompatible->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :cons-merge)
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (not (omap::compatiblep (erl-state->bind s)
                                 (kont-cons-merge->car-bind (erl-k->kont k)))))
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

(defrule eval-k-of-cons-merge-noncons->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :cons-merge)
         (not (equal (erl-val-kind (erl-state->in s)) :cons)))
    (equal
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in
        s
        (make-erl-val-reject
          :err "cons-merge expects list, pairs are not supported"))))
  :enable eval-k)


; Combine to general rule
(defrule eval-k-of-cons-merge->s
  (implies
    (and (erl-state-p s)
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :cons-merge))
    (equal
      (erl-s-klst->s (eval-k k s))
      (cond
        ((not (wf-state-p s)) s)
        ((not (> (erl-k->fuel k) 0))
         (update-erl-state->in s (make-erl-val-flimit)))
        ((not (equal (erl-val-kind (erl-state->in s)) :cons))
         (update-erl-state->in
           s
           (make-erl-val-reject
             :err "cons-merge expects list, pairs are not supported")))
        ((not (omap::compatiblep 
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