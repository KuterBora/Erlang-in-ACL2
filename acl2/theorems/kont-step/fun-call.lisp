(in-package "ACL2")
(include-book "../core/eval-theorems")

; Fun Call Kont-Step -----------------------------------------------------------

; The following theorems show that evaluating a continuation for an anonymous call
; expression is equivalent to evaluating the arguments in order, and then invoking
; the call evaluator which will then provide the body of the function to execute.

; expr-fun-call
(defrule eval-k-of-expr-fun-call->klst
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :fun-call))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (list
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr
                  :expr (node-fun-call->fun
                           (kont-expr->expr (erl-k->kont k)))))
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-fun-call-args
                  :args (node-fun-call->args
                          (kont-expr->expr (erl-k->kont k))))))))
  :enable eval-k)

(defrule eval-k-of-expr-fun-call->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :fun-call))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)

; kont-fun-args
(defrule eval-k-of-fun-call-args-ok->klst
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :fun-call-args)
         (erl-fun-p (erl-state->in s)))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (list
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-expr
                  :expr (kont-fun-call-args->args (erl-k->kont k))))
        (make-erl-k
          :fuel (1- (erl-k->fuel k))
          :kont (make-kont-fun-call
                  :fun (erl-state->in s))))))
  :enable eval-k)

(defrule eval-k-of-fun-call-args-ok->s
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :fun-call-args)
         (erl-fun-p (erl-state->in s)))
    (equal
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)

(defrule eval-k-of-fun-call-args-not-fun->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :fun-call-args)
         (not (erl-fun-p (erl-state->in s))))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-fun-call-args-not-fun->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :fun-call-args)
         (not (erl-fun-p (erl-state->in s))))
    (equal
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in
        s
        (make-erl-val-excpt
          :err (make-erl-err
                 :class (make-err-class-error)
                 :reason (make-exit-reason-badfun
                           :fun (erl-state->in s)))))))
  :enable eval-k)

; Combine the results from above to a general rewrite rule.
(defrule eval-k-of-fun-call-args->klst
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :fun-call-args))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (if (erl-fun-p (erl-state->in s))
          (list
            (make-erl-k
              :fuel (1- (erl-k->fuel k))
              :kont (make-kont-expr
                      :expr (kont-fun-call-args->args (erl-k->kont k))))
            (make-erl-k
              :fuel (1- (erl-k->fuel k))
              :kont (make-kont-fun-call
                      :fun (erl-state->in s))))
          nil))))

; Combine the results from above to a general rewrite rule.
(defrule eval-k-of-fun-call-args->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :fun-call-args))
    (equal
      (erl-s-klst->s (eval-k k s))
      (if (erl-fun-p (erl-state->in s))
          (update-erl-state->in s (make-erl-val-none))
          (update-erl-state->in
            s
            (make-erl-val-excpt
              :err (make-erl-err
                    :class (make-err-class-error)
                    :reason (make-exit-reason-badfun
                              :fun (erl-state->in s)))))))))

; kont 
(defrule eval-k-of-fun-call-ok->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :fun-call)
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (mv-nth 1 (eval-fun-call
                     (update-erl-state->in s (make-erl-val-none))
                     (kont-fun-call->fun (erl-k->kont k))
                     (erl-val-cons->lst (erl-state->in s)))))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (list (make-erl-k 
              :fuel (1- (erl-k->fuel k))
              :kont (make-kont-exprs :exprs
                (mv-nth 1 (eval-fun-call
                    (update-erl-state->in s (make-erl-val-none))
                    (kont-fun-call->fun (erl-k->kont k))
                    (erl-val-cons->lst (erl-state->in s))))))
            (make-erl-k
              :fuel (1- (erl-k->fuel k)) 
              :kont (make-kont-function-return 
                      :bind (erl-state->bind s) 
                      :module (erl-state->module s))))))
  :enable eval-k)

(defrule eval-k-of-fun-call-ok->s
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :fun-call)
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (mv-nth 1 (eval-fun-call
                     (update-erl-state->in s (make-erl-val-none))
                     (kont-fun-call->fun (erl-k->kont k))
                     (erl-val-cons->lst (erl-state->in s)))))
    (equal
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in
        (mv-nth 0 (eval-fun-call
                    (update-erl-state->in s (make-erl-val-none))
                    (kont-fun-call->fun (erl-k->kont k))
                    (erl-val-cons->lst (erl-state->in s))))
        (make-erl-val-none))))
  :enable eval-k)

(defrule eval-k-of-fun-call-invalid-args->klst
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :fun-call)
         (not (equal (erl-val-kind (erl-state->in s)) :cons)))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-fun-call-invalid-args->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :fun-call)
         (not (equal (erl-val-kind (erl-state->in s)) :cons)))
    (equal
      (erl-s-klst->s (eval-k k s))
      (update-erl-state->in
        s
        (make-erl-val-reject :err "Fun call: invalid arg list."))))
  :enable eval-k)

(defrule eval-k-of-fun-call-no-clauses->klst
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :fun-call)
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (not (mv-nth 1 (eval-fun-call
                     (update-erl-state->in s (make-erl-val-none))
                     (kont-fun-call->fun (erl-k->kont k))
                     (erl-val-cons->lst (erl-state->in s))))))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-fun-call-no-clauses->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :fun-call)
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (not (mv-nth 1 (eval-fun-call
                     (update-erl-state->in s (make-erl-val-none))
                     (kont-fun-call->fun (erl-k->kont k))
                     (erl-val-cons->lst (erl-state->in s))))))
    (equal
      (erl-s-klst->s (eval-k k s))
      (mv-nth 0 (eval-fun-call
                  (update-erl-state->in s (make-erl-val-none))
                  (kont-fun-call->fun (erl-k->kont k))
                  (erl-val-cons->lst (erl-state->in s))))))
  :enable eval-k)

; Combine the rules from above to a general rewrite rule
(defrule eval-k-of-fun-call->klst
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :fun-call))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (cond
        ((not (equal (erl-val-kind (erl-state->in s)) :cons)) nil)
        ((not (mv-nth
                1 
                (eval-fun-call
                  (update-erl-state->in s (make-erl-val-none))
                  (kont-fun-call->fun (erl-k->kont k))
                  (erl-val-cons->lst (erl-state->in s)))))
          nil)
        (t (list (make-erl-k 
              :fuel (1- (erl-k->fuel k))
              :kont (make-kont-exprs :exprs
                (mv-nth 1 (eval-fun-call
                    (update-erl-state->in s (make-erl-val-none))
                    (kont-fun-call->fun (erl-k->kont k))
                    (erl-val-cons->lst (erl-state->in s))))))
            (make-erl-k
              :fuel (1- (erl-k->fuel k)) 
              :kont (make-kont-function-return 
                      :bind (erl-state->bind s) 
                      :module (erl-state->module s))))))))
  :enable eval-k)

(defrule eval-k-of-fun-call->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :fun-call))
    (equal
      (erl-s-klst->s (eval-k k s))
      (cond
        ((not (equal (erl-val-kind (erl-state->in s)) :cons)) 
         (update-erl-state->in
           s
           (make-erl-val-reject :err "Fun call: invalid arg list.")))
        ((not (mv-nth
                1 
                (eval-fun-call
                  (update-erl-state->in s (make-erl-val-none))
                  (kont-fun-call->fun (erl-k->kont k))
                  (erl-val-cons->lst (erl-state->in s)))))
          (mv-nth 
            0 
            (eval-fun-call
              (update-erl-state->in s (make-erl-val-none))
              (kont-fun-call->fun (erl-k->kont k))
              (erl-val-cons->lst (erl-state->in s)))))
        (t (update-erl-state->in
            (mv-nth 0 (eval-fun-call
                        (update-erl-state->in s (make-erl-val-none))
                        (kont-fun-call->fun (erl-k->kont k))
                        (erl-val-cons->lst (erl-state->in s))))
            (make-erl-val-none)))))))