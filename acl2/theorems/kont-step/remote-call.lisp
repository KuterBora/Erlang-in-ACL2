(in-package "ACL2")
(include-book "../core/eval-theorems")

; Remote Call Kont-Step --------------------------------------------------------

; The following theorems show that evaluating a continuation for a remote call
; expression is equivalent to evaluating the arguments in order, and then invoking
; the call evaluator which will then provide the body of the function to execute.

(defrule eval-k-of-expr-remote-call->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :remote-call))
    (equal 
      (erl-s-klst->klst (eval-k k s))
      (list
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr 
            :expr (node-remote-call->args (kont-expr->expr (erl-k->kont k)))))
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-remote-call
                  :module (node-remote-call->module (kont-expr->expr (erl-k->kont k)))
                  :call (node-remote-call->fn (kont-expr->expr (erl-k->kont k))))))))
  :enable eval-k)

(defrule eval-k-of-expr-remote-call->s
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :remote-call))
    (equal 
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)

(defrule eval-k-of-remote-call-ok->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :remote-call)
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (mv-nth 1 (eval-remote-call
                     (update-erl-state->in s (make-erl-val-none))
                     (kont-remote-call->module (erl-k->kont k))
                     (kont-remote-call->call (erl-k->kont k))
                     (erl-val-cons->lst (erl-state->in s)))))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (list (make-erl-k 
              :fuel (1- (erl-k->fuel k))
              :kont (make-kont-exprs :exprs
                (mv-nth 1 (eval-remote-call
                    (update-erl-state->in s (make-erl-val-none))
                    (kont-remote-call->module (erl-k->kont k))
                    (kont-remote-call->call (erl-k->kont k))
                    (erl-val-cons->lst (erl-state->in s))))))
            (make-erl-k
              :fuel (1- (erl-k->fuel k)) 
              :kont (make-kont-function-return 
                      :bind (erl-state->bind s) 
                      :module (erl-state->module s))))))
  :enable eval-k)

(defrule eval-k-of-remote-call-ok->s
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :remote-call)
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (mv-nth 1 (eval-remote-call
                     (update-erl-state->in s (make-erl-val-none))
                     (kont-remote-call->module (erl-k->kont k))
                     (kont-remote-call->call (erl-k->kont k))
                     (erl-val-cons->lst (erl-state->in s)))))
    (equal
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in 
        (mv-nth 0 (eval-remote-call
                    (update-erl-state->in s (make-erl-val-none))
                    (kont-remote-call->module (erl-k->kont k))
                    (kont-remote-call->call (erl-k->kont k))
                    (erl-val-cons->lst (erl-state->in s))))
        (make-erl-val-none))))
  :enable eval-k)

(defrule eval-k-of-remote-call-invalid-args->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :remote-call)
         (not (equal (erl-val-kind (erl-state->in s)) :cons)))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-remote-call-invalid-args->s
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :remote-call)
         (not (equal (erl-val-kind (erl-state->in s)) :cons)))
    (equal 
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in 
        s
        (make-erl-val-reject :err "Remote call: invalid arg list."))))
  :enable eval-k)

(defrule eval-k-of-remote-call-no-clauses->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :remote-call)
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (not (mv-nth 1 (eval-remote-call
                     (update-erl-state->in s (make-erl-val-none))
                     (kont-remote-call->module (erl-k->kont k))
                     (kont-remote-call->call (erl-k->kont k))
                     (erl-val-cons->lst (erl-state->in s))))))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-remote-call-no-clauses->s
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :remote-call)
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (not (mv-nth 1 (eval-remote-call
                     (update-erl-state->in s (make-erl-val-none))
                     (kont-remote-call->module (erl-k->kont k))
                     (kont-remote-call->call (erl-k->kont k))
                     (erl-val-cons->lst (erl-state->in s))))))
    (equal 
      (erl-s-klst->s (eval-k k s))
      (mv-nth 0 (eval-remote-call
                     (update-erl-state->in s (make-erl-val-none))
                     (kont-remote-call->module (erl-k->kont k))
                     (kont-remote-call->call (erl-k->kont k))
                     (erl-val-cons->lst (erl-state->in s))))))
  :enable eval-k)


; Combine the rules from above to a general rewrite rule
(defrule eval-k-of-remote->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :remote-call))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (cond ((not (equal (erl-val-kind (erl-state->in s)) :cons)) nil)
            ((not (mv-nth 1 (eval-remote-call
                              (update-erl-state->in s (make-erl-val-none))
                              (kont-remote-call->module (erl-k->kont k))
                              (kont-remote-call->call (erl-k->kont k))
                              (erl-val-cons->lst (erl-state->in s)))))
              nil)
            (t (list (make-erl-k 
                      :fuel (1- (erl-k->fuel k))
                      :kont (make-kont-exprs :exprs
                        (mv-nth 1 (eval-remote-call
                            (update-erl-state->in s (make-erl-val-none))
                            (kont-remote-call->module (erl-k->kont k))
                            (kont-remote-call->call (erl-k->kont k))
                            (erl-val-cons->lst (erl-state->in s))))))
                    (make-erl-k
                      :fuel (1- (erl-k->fuel k)) 
                      :kont (make-kont-function-return 
                              :bind (erl-state->bind s) 
                              :module (erl-state->module s))))))))
  :enable eval-k)

(defrule eval-k-of-remote->s
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :remote-call))
    (equal
      (erl-s-klst->s (eval-k k s))
      (cond ((not (equal (erl-val-kind (erl-state->in s)) :cons))
             (update-erl-state->in 
              s
              (make-erl-val-reject :err "Remote call: invalid arg list.")))
            ((not (mv-nth 1 (eval-remote-call
                              (update-erl-state->in s (make-erl-val-none))
                              (kont-remote-call->module (erl-k->kont k))
                              (kont-remote-call->call (erl-k->kont k))
                              (erl-val-cons->lst (erl-state->in s)))))
             (mv-nth 
              0 
              (eval-remote-call
                (update-erl-state->in s (make-erl-val-none))
                (kont-remote-call->module (erl-k->kont k))
                (kont-remote-call->call (erl-k->kont k))
                (erl-val-cons->lst (erl-state->in s)))))
            (t (update-erl-state->in 
                 (mv-nth 0 (eval-remote-call
                             (update-erl-state->in s (make-erl-val-none))
                             (kont-remote-call->module (erl-k->kont k))
                             (kont-remote-call->call (erl-k->kont k))
                             (erl-val-cons->lst (erl-state->in s))))
                 (make-erl-val-none)))))))