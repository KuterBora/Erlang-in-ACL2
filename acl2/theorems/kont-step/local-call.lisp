(in-package "ACL2")
(include-book "../core/top")
(include-book "../state/top")

; Local Call Kont-Step ---------------------------------------------------------

; The following theorems show that evaluating a continuation for a local call
; expression is equivalent to evaluating the arguments in order, and then invoking
; the call evaluator which will then provide the body of the function to execute.


; eval-k -----------------------------------------------------------------------

; expr-local-call
(defrule eval-k-of-expr-local-call->klst
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :call))
    (equal 
      (erl-s-klst->klst (eval-k k s))
      (list
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr
                  :expr (node-call->args
                          (kont-expr->expr (erl-k->kont k)))))
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-local-call 
                  :call (node-call->fn
                          (kont-expr->expr (erl-k->kont k))))))))
  :enable eval-k)

(defrule eval-k-of-expr-local-call->s
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :call))
    (equal 
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)


; kont-local-call
; (defrule eval-k-of-local-call->klst
;   (implies
;     (and (erl-state-p s) 
;          (erl-k-p k)
;          (equal (kont-kind (erl-k->kont k)) :local-call))
;     (equal
;       (erl-s-klst->klst (eval-k k s))
;       (cond
;         ((not (wf-state-p s)) nil)
;         ((not (> (erl-k->fuel k) 0)) nil)
;         ((not (equal (erl-val-kind (erl-state->in s)) :cons)) nil)
;         ((not (mv-nth 
;                 1 
;                 (eval-local-call
;                   (update-erl-state->in s (make-erl-val-none))
;                   (kont-local-call->call (erl-k->kont k))
;                   (erl-val-cons->lst (erl-state->in s)))))
;           nil)
;         (t (list (make-erl-k 
;                   :fuel (1- (erl-k->fuel k))
;                   :kont (make-kont-exprs :exprs
;                     (mv-nth
;                       1 
;                       (eval-local-call
;                         (update-erl-state->in s (make-erl-val-none))
;                         (kont-local-call->call (erl-k->kont k))
;                         (erl-val-cons->lst (erl-state->in s))))))
;                 (make-erl-k
;                   :fuel (1- (erl-k->fuel k)) 
;                   :kont (make-kont-function-return 
;                           :bind (erl-state->bind s) 
;                           :module (erl-state->module s))))))))
;   :enable eval-k)

; (defrule eval-k-of-local-call->s
;   (implies
;     (and (erl-state-p s) 
;          (erl-k-p k)
;          (equal (kont-kind (erl-k->kont k)) :local-call))
;     (equal
;       (erl-s-klst->s (eval-k k s))
;       (cond
;         ((not (wf-state-p s)) s)
;         ((not (> (erl-k->fuel k) 0))
;          (update-erl-state->in s (make-erl-val-flimit))) 
;         ((not (equal (erl-val-kind (erl-state->in s)) :cons))
;          (update-erl-state->in 
;            s
;            (make-erl-val-reject :err "Local call: invalid arg list.")))
;         ((not (mv-nth 
;                 1 
;                 (eval-local-call
;                   (update-erl-state->in s (make-erl-val-none))
;                   (kont-local-call->call (erl-k->kont k))
;                   (erl-val-cons->lst (erl-state->in s)))))
;          (mv-nth 
;            0 
;            (eval-local-call
;              (update-erl-state->in s (make-erl-val-none))
;              (kont-local-call->call (erl-k->kont k))
;              (erl-val-cons->lst (erl-state->in s)))))
;         (t (update-erl-state->in 
;              (mv-nth
;               0 
;               (eval-local-call
;                 (update-erl-state->in s (make-erl-val-none))
;                 (kont-local-call->call (erl-k->kont k))
;                 (erl-val-cons->lst (erl-state->in s))))
;             (make-erl-val-none))))))
;   :enable eval-k)

; apply-k ----------------------------------------------------------------------
