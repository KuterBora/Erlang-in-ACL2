(in-package "ACL2")
(include-book "../core/eval-theorems")

; Tuple Kont-Step --------------------------------------------------------------


; The following theorems show that evaluating a continuation for a tuple
; expression is equivalent to evaluating every element of the tuple from
; left to right, and then merging the results.


; Stepping the initial continuation
(local (defrule eval-k-of-expr-empty-tuple->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :tuple)
         (null (node-tuple->lst (kont-expr->expr (erl-k->kont k)))))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k))

(local (defrule eval-k-of-expr-empty-tuple->s
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :tuple)
         (null (node-tuple->lst (kont-expr->expr (erl-k->kont k)))))
    (equal (erl-s-klst->s (eval-k k s)) 
           (update-erl-state->in s (make-erl-val-tuple :lst nil))))
  :enable eval-k))

(local (defrule eval-k-of-expr-tuple->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :tuple)
         (node-tuple->lst (kont-expr->expr (erl-k->kont k))))
    (equal 
      (erl-s-klst->klst (eval-k k s))
      (list (make-erl-k 
              :fuel (1- (erl-k->fuel k))
              :kont (make-kont-expr 
                :expr (car (node-tuple->lst (kont-expr->expr (erl-k->kont k))))))
            (make-erl-k 
              :fuel (1- (erl-k->fuel k))
              :kont 
                (make-kont-tuple 
                  :t-rem 
                    (make-node-tuple 
                      :lst (cdr (node-tuple->lst (kont-expr->expr (erl-k->kont k)))))
                  :bind-0 (erl-state->bind s))))))
  :enable eval-k))

(local (defrule eval-k-of-expr-tuple->s
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :tuple)
         (node-tuple->lst (kont-expr->expr (erl-k->kont k))))
    (equal 
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k))


; Stepping the tuple continuation                                        
(local (defrule eval-k-of-tuple->klst
  (implies 
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :tuple))
    (equal (erl-s-klst->klst (eval-k k s))
           (list (make-erl-k 
                    :fuel (1- (erl-k->fuel k)) 
                    :kont (make-kont-expr :expr (kont-tuple->t-rem (erl-k->kont k))))
                 (make-erl-k 
                    :fuel (1- (erl-k->fuel k))
                    :kont (make-kont-tuple-merge 
                            :t-hd (erl-state->in s)
                            :t-bind (erl-state->bind s))))))
  :enable eval-k))

(local (defrule eval-k-of-tuple->s
  (implies 
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :tuple))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->bind 
             s
             (kont-tuple->bind-0 (erl-k->kont k)))))
  :enable eval-k))


; Stepping the tuple-merge continuation                                        
(local (defrule eval-k-of-tuple-merge->klst
  (implies 
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :tuple-merge))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k))

(local (defrule eval-k-of-tuple-merge->s
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :tuple-merge)
         (equal (erl-val-kind (erl-state->in s)) :tuple)
         (omap::compatiblep
          (erl-state->bind s) 
          (kont-tuple-merge->t-bind (erl-k->kont k))))
    (equal (erl-s-klst->s (eval-k k s)) 
           (update-erl-state->in-bind 
            s
            (make-erl-val-tuple
              :lst (cons (kont-tuple-merge->t-hd (erl-k->kont k)) 
                         (erl-val-tuple->lst (erl-state->in s))))
            (omap::update*
              (erl-state->bind s) 
              (kont-tuple-merge->t-bind (erl-k->kont k))))))
  :enable eval-k))


; apply-k with a tuple expression continuation is equivalent to evaluating the 
; elements of the tuple in order and then merging the results -- assuming there 
; are no excpetion, rejection, or out-of-fuel errors.
;
; If evaluation succeeds for s and k, in the returned state
; - in will contain a tuple, where each element corresponds the evaluation of the
;   element from the original tuple.
; - bind will contain any previous bindings and any new ones created when 
;   evaluating the elements.
;
; Rest: TODO

(defrule apply-k-of-tuple->in
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 2)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :tuple)
         (node-tuple->lst (kont-expr->expr (erl-k->kont k))))
    (b* (((erl-state s) s)
         ((erl-k k))
         (hd (car (node-tuple->lst (kont-expr->expr k.kont))))
         (tl (make-node-tuple :lst (cdr (node-tuple->lst (kont-expr->expr k.kont)))))
         (hd_res (apply-k (update-erl-state->in s (make-erl-val-none))
                          (list (make-erl-k :fuel (1- k.fuel) 
                                            :kont (make-kont-expr :expr hd)))))
         (tl_res (apply-k (update-erl-state->bind hd_res s.bind)
                          (list (make-erl-k :fuel (- k.fuel 2)
                                            :kont (make-kont-expr :expr tl)))))
         ((unless (wf-state-p hd_res)) t)
         ((unless (and (wf-state-p tl_res)
                       (equal (erl-val-kind (erl-state->in tl_res)) :tuple)
                       (omap::compatiblep (erl-state->bind tl_res)
                                          (erl-state->bind hd_res))))
          t))
        (equal (erl-state->in (apply-k s (list k)))
               (make-erl-val-tuple 
                 :lst (cons (erl-state->in hd_res)
                            (erl-val-tuple->lst (erl-state->in tl_res))))))))