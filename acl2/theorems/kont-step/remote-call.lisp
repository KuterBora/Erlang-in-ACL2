(in-package "ACL2")
(include-book "../core/eval-theorems")

; Remote Call Kont-Step --------------------------------------------------------

; The following theorems show that evaluating a continuation for a remote call
; expression is equivalent to evaluating the arguments in order, and then invoking
; the call evaluator which will then provide the body of the function to execute.

; Stepping the initial continuation
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
          :kont (make-kont-function-args-start 
                  :args (node-remote-call->args (kont-expr->expr (erl-k->kont k)))))
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


; Stepping the remote-call continuation
(defrule eval-k-of-remote-call->klst
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
                     (rev (erl-val-cons->lst (erl-state->in s))))))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (list (make-erl-k 
              :fuel (1- (erl-k->fuel k))
              :kont (make-kont-exprs :exprs
                (mv-nth 1 (eval-remote-call
                    (update-erl-state->in s (make-erl-val-none))
                    (kont-remote-call->module (erl-k->kont k))
                    (kont-remote-call->call (erl-k->kont k))
                    (rev (erl-val-cons->lst (erl-state->in s)))))))
            (make-erl-k
              :fuel (1- (erl-k->fuel k)) 
              :kont (make-kont-function-return 
                      :bind (erl-state->bind s) 
                      :module (erl-state->module s))))))
  :enable eval-k)

(defrule eval-k-of-remote-call->s
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
                     (rev (erl-val-cons->lst (erl-state->in s))))))
    (equal
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in 
        (mv-nth 0 (eval-remote-call
                    (update-erl-state->in s (make-erl-val-none))
                    (kont-remote-call->module (erl-k->kont k))
                    (kont-remote-call->call (erl-k->kont k))
                    (rev (erl-val-cons->lst (erl-state->in s)))))
        (make-erl-val-none))))
  :enable eval-k)


; apply-k with a remote-call expression continuation is equivalent to evaluating
; the arguments in order, invoking the call evaluator to find the first matching
; clause, executing the clause body, and then returning to the module and bindings
; before the call. -- assuming there are no excpetion rejection, or out-of-fuel errors.
;
; If evaluation succeeds for s and k, in the returned state
; - in will contain the value obtained by evaluating the function.
; - bind will contain any previous bindings and any new ones created by 
;   evaluating the arguments.
; - module will remain unchanged.
; Rest: TODO

(defrule apply-k-of-remote-call
  (implies 
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 2)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :remote-call))
    (b* (((erl-state s) s)
         ((erl-k k))
         (args (node-remote-call->args (kont-expr->expr k.kont)))
         (args_res (apply-k (update-erl-state->in s (make-erl-val-none))
                            (list (make-erl-k :fuel (1- k.fuel) 
                                              :kont (make-kont-function-args-start 
                                                      :args args)))))
         ((unless (wf-state-p args_res)) t)
         ((unless (equal (erl-val-kind (erl-state->in args_res)) :cons)) t)
         ((mv (erl-state rs) body)
          (eval-remote-call 
            (update-erl-state->in args_res (make-erl-val-none))
            (node-remote-call->module (kont-expr->expr k.kont))
            (node-remote-call->fn (kont-expr->expr k.kont))
            (rev (erl-val-cons->lst (erl-state->in args_res)))))
         ((unless (wf-state-p rs)) t)
         ((unless body) t))
        (equal (apply-k s (list k))
               (apply-k (update-erl-state->in rs (make-erl-val-none))
                        (list (make-erl-k 
                            :fuel (- k.fuel 2)
                            :kont (make-kont-exprs :exprs body))
                          (make-erl-k
                            :fuel (- k.fuel 2)
                            :kont (make-kont-function-return 
                                    :bind (erl-state->bind args_res)
                                    :module (erl-state->module args_res)))))))))