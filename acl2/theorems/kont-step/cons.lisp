(in-package "ACL2")
(include-book "../core/eval-theorems")

; Cons Kont-Step ---------------------------------------------------------------

; The following theorems show that evaluating a continuation for a cons
; expression is equivalent to evaluating the car, evaluating the cdr,
; and then merging the result.

; Stepping the initial continuation
(defrule eval-k-of-expr-cons->klst
  (implies
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :expr)
       (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons))
    (equal 
      (erl-s-klst->klst (eval-k k s))
      (list 
        (make-erl-k 
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr :expr 
            (node-cons->hd (kont-expr->expr (erl-k->kont k)))))
        (make-erl-k :fuel (1- (erl-k->fuel k))
                    :kont 
                      (make-kont-cons 
                        :cdr-expr (node-cons->tl (kont-expr->expr (erl-k->kont k)))
                        :bind-0 (erl-state->bind s))))))
  :enable eval-k)

(defrule eval-k-of-expr-cons->s
  (implies 
    (and
      (wf-state-p s)
      (erl-k-p k)
      (> (erl-k->fuel k) 0)
      (equal (kont-kind (erl-k->kont k)) :expr)
      (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons))
    (equal (erl-s-klst->s (eval-k k s)) 
           (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)


; Stepping the cons continuation                                        
(defrule eval-k-of-cons->klst
  (implies 
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :cons))
    (equal (erl-s-klst->klst (eval-k k s))
           (list (make-erl-k 
                    :fuel (1- (erl-k->fuel k)) 
                    :kont (make-kont-expr :expr (kont-cons->cdr-expr (erl-k->kont k))))
                 (make-erl-k :fuel (1- (erl-k->fuel k))
                             :kont (make-kont-cons-merge 
                                    :car-val (erl-state->in s)
                                    :car-bind (erl-state->bind s))))))
  :enable eval-k)

(defrule eval-k-of-cons->s
  (implies 
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :cons))
    (equal (erl-s-klst->s (eval-k k s)) 
           (update-erl-state->in-bind 
             s 
             (make-erl-val-none)
             (kont-cons->bind-0 (erl-k->kont k)))))
  :enable eval-k)

; Stepping the cons-merge continuation                                        
(defrule eval-k-of-cons-merge->klst
  (implies 
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :cons-merge))
    (equal (erl-s-klst->klst (eval-k k s))
           nil))
  :enable eval-k)

(defrule eval-k-of-cons-merge->s
  (implies 
    (and
       (wf-state-p s)
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :cons-merge)
       (equal (erl-val-kind (erl-state->in s)) :cons)
       (omap::compatiblep
        (erl-state->bind s) 
        (kont-cons-merge->car-bind (erl-k->kont k))))
    (equal (erl-s-klst->s (eval-k k s)) 
           (update-erl-state->in-bind 
            s
            (make-erl-val-cons 
              :lst (cons (kont-cons-merge->car-val (erl-k->kont k)) 
                         (erl-val-cons->lst (erl-state->in s))))
            (omap::update* 
              (erl-state->bind s) 
              (kont-cons-merge->car-bind (erl-k->kont k))))))
  :enable eval-k)


; apply-k with a cons expression continuation is equivalent to evaluating the 
; car and cdr then merging the results -- assuming there are no excpetion,
; rejection, or out-of-fuel errors.
;
; If evaluation succeeds for s and k, in the returned state
; - in will contain the result of consing the car and cdr of the list
; - bind will contain any previous bindings and any new ones created by 
;   evaluating the car and cdr expressions.
;
; Rest: TODO

(defrule apply-k-of-cons->in
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 2)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons))
    (b* (((erl-state s) s)
         ((erl-k k))
         (hd (node-cons->hd (kont-expr->expr k.kont)))
         (tl (node-cons->tl (kont-expr->expr k.kont)))
         (hd_res (apply-k (update-erl-state->in s (make-erl-val-none))
                         (list (make-erl-k :fuel (1- k.fuel) 
                                           :kont (make-kont-expr :expr hd)))))
         (tl_res (apply-k (update-erl-state->in-bind hd_res (make-erl-val-none) s.bind)
                          (list (make-erl-k :fuel (- k.fuel 2)
                                            :kont (make-kont-expr :expr tl)))))
         ((unless (wf-state-p hd_res)) t)
         ((unless (and (wf-state-p tl_res)
                       (equal (erl-val-kind (erl-state->in tl_res)) :cons)
                       (omap::compatiblep (erl-state->bind tl_res)
                                          (erl-state->bind hd_res))))
                  t))
        (equal (erl-state->in (apply-k s (list k)))
               (make-erl-val-cons 
                 :lst (cons (erl-state->in hd_res)
                            (erl-val-cons->lst (erl-state->in tl_res))))))))

(defrule apply-k-of-cons->bind
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 2)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :cons))
    (b* (((erl-state s) s)
         ((erl-k k))
         (hd (node-cons->hd (kont-expr->expr k.kont)))
         (tl (node-cons->tl (kont-expr->expr k.kont)))
         (hd_res (apply-k (update-erl-state->in s (make-erl-val-none))
                          (list (make-erl-k :fuel (1- k.fuel) 
                                            :kont (make-kont-expr :expr hd)))))
         (tl_res (apply-k (update-erl-state->in-bind hd_res (make-erl-val-none) s.bind)
                          (list (make-erl-k :fuel (- k.fuel 2)
                                            :kont (make-kont-expr :expr tl)))))
         ((unless (wf-state-p hd_res)) t)
         ((unless (and (wf-state-p tl_res)
                       (equal (erl-val-kind (erl-state->in tl_res)) :cons)
                       (omap::compatiblep (erl-state->bind tl_res)
                                          (erl-state->bind hd_res))))
                  t))
        (equal (erl-state->bind (apply-k s (list k)))
               (omap::update* (erl-state->bind tl_res) (erl-state->bind hd_res))))))