(in-package "ACL2")
; (include-book "../core/eval-theorems")

; ; Tuple Kont-Step --------------------------------------------------------------

; ; The following theorems show that evaluating a continuation for a tuple
; ; expression is equivalent to evaluating every element of the tuple from
; ; left to right, and then merging the results.

; (defrule eval-k-of-expr-tuple->s
;   (implies
;     (and (erl-state-p s)
;          (erl-k-p k)
;          (equal (kont-kind (erl-k->kont k)) :expr)
;          (equal (node-kind (kont-expr->expr (erl-k->kont k))) :tuple))
;     (equal
;       (erl-s-klst->s (eval-k k s))
      
;       (cond
;         ((not (wf-state-p s)) s)
;         ((not (> (erl-k->fuel k) 0))
;          (update-erl-state->in s (make-erl-val-flimit)))
;         ((not (consp (node-tuple->lst (kont-expr->expr (erl-k->kont k)))))
;          (update-erl-state->in s (make-erl-val-tuple :lst nil)))
;         (t (update-erl-state->in s (make-erl-val-none))))))
;   :enable eval-k)

; (defrule eval-k-of-expr-tuple->klst
;   (implies
;     (and (erl-state-p s)
;          (erl-k-p k)
;          (equal (kont-kind (erl-k->kont k)) :expr)
;          (equal (node-kind (kont-expr->expr (erl-k->kont k))) :tuple))
;     (equal
;       (erl-s-klst->klst (eval-k k s))
;       (if (and (wf-state-p s)
;                (> (erl-k->fuel k) 0)
;                (node-tuple->lst (kont-expr->expr (erl-k->kont k))))
;           (list
;             (make-erl-k
;               :fuel (1- (erl-k->fuel k))
;               :kont (make-kont-expr
;                       :expr (car (node-tuple->lst
;                                    (kont-expr->expr (erl-k->kont k))))))
;             (make-erl-k
;               :fuel (1- (erl-k->fuel k))
;               :kont (make-kont-tuple
;                       :t-rem (make-node-tuple
;                               :lst (cdr (node-tuple->lst
;                                           (kont-expr->expr (erl-k->kont k)))))
;                       :bind-0 (erl-state->bind s))))
;           nil)))
;   :enable eval-k)


; ; kont-tuple
; (defrule eval-k-of-tuple->klst
;   (implies 
;     (and (erl-state-p s) 
;          (erl-k-p k)
;          (equal (kont-kind (erl-k->kont k)) :tuple))
;     (equal
;       (erl-s-klst->klst (eval-k k s))
;       (if (and (wf-state-p s) (> (erl-k->fuel k) 0)) 
;           (list (make-erl-k 
;                   :fuel (1- (erl-k->fuel k)) 
;                   :kont (make-kont-expr 
;                         :expr (kont-tuple->t-rem (erl-k->kont k))))
;                 (make-erl-k 
;                   :fuel (1- (erl-k->fuel k))
;                   :kont (make-kont-tuple-merge 
;                           :t-hd (erl-state->in s)
;                           :t-bind (erl-state->bind s))))
;           nil)))
;   :enable eval-k)

; (defrule eval-k-of-tuple->s
;   (implies 
;     (and (erl-state-p s) 
;          (erl-k-p k)
;          (equal (kont-kind (erl-k->kont k)) :tuple))
;     (equal (erl-s-klst->s (eval-k k s))
;            (cond
;              ((not (wf-state-p s) ) s)
;              ((not (> (erl-k->fuel k) 0))
;               (update-erl-state->in s (make-erl-val-flimit)))
;              (t (update-erl-state->bind 
;                   s
;                   (kont-tuple->bind-0 (erl-k->kont k)))))))
;   :enable eval-k)


; ; kont-tuple-merge
; (defrule eval-k-of-tuple-merge->klst
;   (implies
;     (and (erl-k-p k)
;          (equal (kont-kind (erl-k->kont k)) :tuple-merge))
;     (equal (erl-s-klst->klst (eval-k k s)) nil))
;   :enable eval-k)

; (defrule eval-k-of-tuple-merge->s
;   (implies
;     (and (erl-k-p k)
;          (erl-state-p s)
;          (equal (kont-kind (erl-k->kont k)) :tuple-merge))
;     (equal
;       (erl-s-klst->s (eval-k k s))
;       (cond
;         ((not (wf-state-p s)) s)
;         ((not (> (erl-k->fuel k) 0))
;          (update-erl-state->in s (make-erl-val-flimit)))
;         ((not (equal (erl-val-kind (erl-state->in s)) :tuple))
;          (update-erl-state->in 
;             s 
;             (make-erl-val-reject :err "tuple-merge expects tuple")))
;         ((not (omap::compatiblep 
;                 (erl-state->bind s)
;                 (kont-tuple-merge->t-bind (erl-k->kont k))))
;          (update-erl-state->in 
;            s 
;            (make-erl-val-excpt 
;              :err (make-erl-err :class (make-err-class-error) 
;                                 :reason (make-exit-reason-badmatch 
;                                           :val (erl-state->in s))))))
;         (t (update-erl-state->in-bind
;              s
;              (make-erl-val-tuple
;                :lst (cons (kont-tuple-merge->t-hd (erl-k->kont k))
;                           (erl-val-tuple->lst (erl-state->in s))))
;              (omap::update*
;                (erl-state->bind s)
;                (kont-tuple-merge->t-bind (erl-k->kont k))))))))
;   :enable eval-k)