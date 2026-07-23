(in-package "ACL2")
(include-book "../core/top")
(include-book "../state/top")
(include-book "functions")
(include-book "exprs")

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
(defrule eval-k-of-local-call->klst
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :local-call))
    (equal
      (erl-s-klst->klst (eval-k k s))
      (cond
        ((not (equal (erl-val-kind (erl-state->in s)) :cons)) nil)
        ((not (mv-nth
                1
                (eval-local-call
                  s
                  (kont-local-call->call (erl-k->kont k))
                  (erl-val-cons->lst (erl-state->in s)))))
          nil)
        (t (list (make-erl-k
                  :fuel (1- (erl-k->fuel k))
                  :kont (make-kont-exprs :exprs
                    (mv-nth
                      1
                      (eval-local-call
                        s
                        (kont-local-call->call (erl-k->kont k))
                        (erl-val-cons->lst (erl-state->in s))))))
                (make-erl-k
                  :fuel (1- (erl-k->fuel k))
                  :kont (make-kont-function-return
                          :bind (erl-state->bind s)
                          :module (erl-state->module s))))))))
  :enable eval-k)

(defrule eval-k-of-local-call->s
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :local-call))
    (equal
      (erl-s-klst->s (eval-k k s))
      (cond
        ((not (equal (erl-val-kind (erl-state->in s)) :cons))
         (update-erl-state->in 
           s
           (make-erl-val-reject :err "Local call: invalid arg list.")))
        (t (mv-nth 
             0
             (eval-local-call
               s
               (kont-local-call->call (erl-k->kont k))
               (erl-val-cons->lst (erl-state->in s))))))))
  :enable eval-k)


; apply-k ----------------------------------------------------------------------

(local (defrule apply-k-of-expr-local-call-1
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :call))
    (equal (apply-k s (cons k nil))
           (apply-k
             (apply-k 
               s
               (list (make-erl-k
                       :fuel (1- (erl-k->fuel k))
                       :kont (make-kont-expr
                               :expr (node-call->args
                                       (kont-expr->expr (erl-k->kont k)))))))
             (list (make-erl-k
                    :fuel (1- (erl-k->fuel k))
                    :kont (make-kont-local-call 
                            :call (node-call->fn
                                    (kont-expr->expr (erl-k->kont k)))))))))
  :enable apply-k-of-step
  :cases ((wf-state-p s))
  :use
    (:instance apply-k-of-expr-when-only-diff-val
      (s1 (update-erl-state->in s (make-erl-val-none)))
      (s2 s)
      (k (make-erl-k
            :fuel (1- (erl-k->fuel k))
            :kont (make-kont-expr
                    :expr (node-call->args
                            (kont-expr->expr (erl-k->kont k)))))))))

(local (defrule apply-k-of-local-call-bad-args
  (implies
    (and (wf-state-p s)
         (not (equal (erl-val-kind (erl-state->in s)) :cons))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :local-call))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in 
             s
             (make-erl-val-reject :err "Local call: invalid arg list."))))
  :enable apply-k-of-step))

(local (defrule apply-k-of-local-call-no-match
  (implies
    (and (wf-state-p s)
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (not (mv-nth 
                1 
                (eval-local-call
                  s
                  (kont-local-call->call (erl-k->kont k))
                  (erl-val-cons->lst (erl-state->in s)))))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :local-call))
    (equal (apply-k s (cons k nil))
           (mv-nth 
              0 
              (eval-local-call
                s
                (kont-local-call->call (erl-k->kont k))
                (erl-val-cons->lst (erl-state->in s))))))
  :enable apply-k-of-step))

(local (defrule apply-k-of-local-call-when-match
  (implies
    (and (wf-state-p s)
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (mv-nth 
           1 
           (eval-local-call
             s
             (kont-local-call->call (erl-k->kont k))
             (erl-val-cons->lst (erl-state->in s))))
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :local-call))
    (equal (apply-k s (cons k nil))
           (apply-k
             (mv-nth
               0 
               (eval-local-call
                 s
                 (kont-local-call->call (erl-k->kont k))
                 (erl-val-cons->lst (erl-state->in s))))
             (list (make-erl-k 
                     :fuel (1- (erl-k->fuel k))
                     :kont (make-kont-exprs :exprs
                              (mv-nth
                                1 
                                (eval-local-call
                                  s
                                  (kont-local-call->call (erl-k->kont k))
                                  (erl-val-cons->lst (erl-state->in s))))))
                    (make-erl-k
                      :fuel (1- (erl-k->fuel k)) 
                      :kont (make-kont-function-return 
                              :bind (erl-state->bind s) 
                              :module (erl-state->module s)))))))
  :enable apply-k-of-step))

(local (defrule apply-k-of-local-call-when-wf-body
  (implies
    (and (wf-state-p s)
         (equal (erl-val-kind (erl-state->in s)) :cons)
         (mv-nth 
           1 
           (eval-local-call
             s
             (kont-local-call->call (erl-k->kont k))
             (erl-val-cons->lst (erl-state->in s))))
         (> (erl-k->fuel k) 2)
         (equal (kont-kind (erl-k->kont k)) :local-call)
         (wf-state-p
           (apply-k
             (mv-nth
               0 
               (eval-local-call
                 s
                 (kont-local-call->call (erl-k->kont k))
                 (erl-val-cons->lst (erl-state->in s))))
             (list (make-erl-k 
                     :fuel (1- (erl-k->fuel k))
                     :kont (make-kont-exprs
                            :exprs
                               (mv-nth
                                1 
                                (eval-local-call
                                  s
                                  (kont-local-call->call (erl-k->kont k))
                                  (erl-val-cons->lst (erl-state->in s))))))))))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in
             s
             (erl-state->in
               (apply-k
                 (mv-nth
                   0 
                   (eval-local-call
                     s
                     (kont-local-call->call (erl-k->kont k))
                     (erl-val-cons->lst (erl-state->in s))))
                 (list (make-erl-k 
                         :fuel (1- (erl-k->fuel k))
                         :kont (make-kont-exprs
                                 :exprs
                                   (mv-nth
                                     1 
                                     (eval-local-call
                                       s
                                       (kont-local-call->call (erl-k->kont k))
                                       (erl-val-cons->lst (erl-state->in s))))))))))))
  :disable update-bind-mod-to-update-in
  :use
    (:instance update-bind-mod-to-update-in
      (s1 s)
      (s2 (apply-k
            (mv-nth
              0 
              (eval-local-call
                s
                (kont-local-call->call (erl-k->kont k))
                (erl-val-cons->lst (erl-state->in s))))
            (list (make-erl-k 
                    :fuel (1- (erl-k->fuel k))
                    :kont (make-kont-exprs
                            :exprs
                              (mv-nth
                                1 
                                (eval-local-call
                                  s
                                  (kont-local-call->call (erl-k->kont k))
                                  (erl-val-cons->lst (erl-state->in s))))))))))))

(defrule apply-k-of-expr-local-call-when-function-has-body
  (implies
    (and (> (erl-k->fuel k) 2)
         (wf-state-p s)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :call)
         (equal (erl-val-kind
                  (erl-state->in (apply-k s (list (make-erl-k
                                     :fuel (1- (erl-k->fuel k))
                                     :kont (make-kont-expr
                                              :expr (node-call->args
                                                      (kont-expr->expr (erl-k->kont k)))))))))
                :cons)
        (mv-nth 
          1 
          (eval-local-call
            (apply-k
              s
              (list (make-erl-k
                      :fuel (1- (erl-k->fuel k))
                      :kont (make-kont-expr
                              :expr (node-call->args
                                      (kont-expr->expr (erl-k->kont k)))))))
            (node-call->fn (kont-expr->expr (erl-k->kont k)))
            (erl-val-cons->lst
              (erl-state->in (apply-k s (list (make-erl-k
                                 :fuel (1- (erl-k->fuel k))
                                 :kont (make-kont-expr
                                         :expr (node-call->args
                                                 (kont-expr->expr (erl-k->kont k))))))))))))
    (equal
      (apply-k s (cons k nil))
      (apply-k
        (mv-nth
          0 
          (eval-local-call
            (apply-k
              s
              (list (make-erl-k
                      :fuel (1- (erl-k->fuel k))
                      :kont (make-kont-expr
                              :expr (node-call->args
                                      (kont-expr->expr (erl-k->kont k)))))))
            (node-call->fn (kont-expr->expr (erl-k->kont k)))
            (erl-val-cons->lst
              (erl-state->in (apply-k s (list (make-erl-k
                                :fuel (1- (erl-k->fuel k))
                                :kont (make-kont-expr
                                        :expr (node-call->args
                                                (kont-expr->expr (erl-k->kont k)))))))))))
        (list
          (make-erl-k 
            :fuel (+ -2 (erl-k->fuel k))
            :kont
              (make-kont-exprs
                :exprs
                  (mv-nth
                    1 
                    (eval-local-call
                      (apply-k
                        s
                        (list (make-erl-k
                                :fuel (1- (erl-k->fuel k))
                                :kont (make-kont-expr
                                        :expr (node-call->args
                                                (kont-expr->expr (erl-k->kont k)))))))
                      (node-call->fn (kont-expr->expr (erl-k->kont k)))
                      (erl-val-cons->lst
                        (erl-state->in (apply-k s (list (make-erl-k
                                          :fuel (1- (erl-k->fuel k))
                                          :kont (make-kont-expr
                                                  :expr (node-call->args
                                                          (kont-expr->expr (erl-k->kont k)))))))))))))
          (make-erl-k
            :fuel (+ -2 (erl-k->fuel k)) 
            :kont
              (make-kont-function-return 
                :bind
                  (erl-state->bind
                    (apply-k s (list (make-erl-k
                                     :fuel (1- (erl-k->fuel k))
                                     :kont (make-kont-expr
                                              :expr (node-call->args
                                                      (kont-expr->expr (erl-k->kont k)))))))) 
                :module
                  (erl-state->module
                    (apply-k s (list (make-erl-k
                                     :fuel (1- (erl-k->fuel k))
                                     :kont (make-kont-expr
                                              :expr (node-call->args
                                                      (kont-expr->expr (erl-k->kont k)))))))))))))))

(defrule apply-k-of-expr-local-call-when-function-has-no-body
  (implies
    (and (> (erl-k->fuel k) 2)
         (wf-state-p s)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :call)
         (equal (erl-val-kind
                  (erl-state->in (apply-k s (list (make-erl-k
                                     :fuel (1- (erl-k->fuel k))
                                     :kont (make-kont-expr
                                              :expr (node-call->args
                                                      (kont-expr->expr (erl-k->kont k)))))))))
                :cons)
        (not
          (mv-nth 
            1 
            (eval-local-call
              (apply-k
                s
                (list (make-erl-k
                        :fuel (1- (erl-k->fuel k))
                        :kont (make-kont-expr
                                :expr (node-call->args
                                        (kont-expr->expr (erl-k->kont k)))))))
              (node-call->fn (kont-expr->expr (erl-k->kont k)))
              (erl-val-cons->lst
                (erl-state->in (apply-k s (list (make-erl-k
                                  :fuel (1- (erl-k->fuel k))
                                  :kont (make-kont-expr
                                          :expr (node-call->args
                                                  (kont-expr->expr (erl-k->kont k)))))))))))))
    (equal
      (apply-k s (cons k nil))
      (mv-nth
          0 
          (eval-local-call
            (apply-k
              s
              (list (make-erl-k
                      :fuel (1- (erl-k->fuel k))
                      :kont (make-kont-expr
                              :expr (node-call->args
                                      (kont-expr->expr (erl-k->kont k)))))))
            (node-call->fn (kont-expr->expr (erl-k->kont k)))
            (erl-val-cons->lst
              (erl-state->in (apply-k s (list (make-erl-k
                                :fuel (1- (erl-k->fuel k))
                                :kont (make-kont-expr
                                        :expr (node-call->args
                                                (kont-expr->expr (erl-k->kont k))))))))))))))

; apply-k when wf --------------------------------------------------------------

(defrule local-call-args-wf
  (implies
    (and (> (erl-k->fuel k) 2)
         (wf-state-p (apply-k s (cons k nil)))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :call))
    (wf-state-p
      (apply-k s (list (make-erl-k
                         :fuel (1- (erl-k->fuel k))
                         :kont (make-kont-expr
                                 :expr (node-call->args
                                         (kont-expr->expr (erl-k->kont k)))))))))
  :disable (apply-k-of-expr-local-call-1)
  :use (:instance apply-k-of-expr-local-call-1))

(defrule local-call-args-are-cons-when-wf
  (implies
    (and (> (erl-k->fuel k) 2)
         (wf-state-p (apply-k s (cons k nil)))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :call))
    (equal
      (erl-val-kind
        (erl-state->in (apply-k s (list (make-erl-k
                         :fuel (1- (erl-k->fuel k))
                         :kont (make-kont-expr
                                 :expr (node-call->args
                                         (kont-expr->expr (erl-k->kont k)))))))))
        :cons))
  :disable (apply-k-of-expr-local-call-1)
  :use (:instance apply-k-of-expr-local-call-1))

(defrule eval-local-call-wf-when-apply-local-call-wf
  (implies
    (and (> (erl-k->fuel k) 2)
         (wf-state-p (apply-k s (cons k nil)))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :call))
    (wf-state-p
      (mv-nth 
        0
        (eval-local-call
          (apply-k
            s
            (list (make-erl-k
                    :fuel (1- (erl-k->fuel k))
                    :kont (make-kont-expr
                            :expr (node-call->args
                                    (kont-expr->expr (erl-k->kont k)))))))
          (node-call->fn (kont-expr->expr (erl-k->kont k)))
          (erl-val-cons->lst
            (erl-state->in (apply-k s (list (make-erl-k
                                :fuel (1- (erl-k->fuel k))
                                :kont (make-kont-expr
                                        :expr (node-call->args
                                                (kont-expr->expr (erl-k->kont k)))))))))))))
  :disable
    (apply-k-of-expr-local-call-1
     apply-k-of-expr-local-call-when-function-has-body
     apply-k-of-expr-local-call-when-function-has-no-body)
  :use ((:instance apply-k-of-expr-local-call-when-function-has-body)
        (:instance apply-k-of-expr-local-call-when-function-has-no-body)))

(defrule local-call-is-wf-before-return-when-apply-k-is-wf
  (implies
    (and (> (erl-k->fuel k) 3)
         (wf-state-p (apply-k s (cons k nil)))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :call))
    (wf-state-p
      (apply-k
        (mv-nth
          0 
          (eval-local-call
            (apply-k
              s
              (list (make-erl-k
                      :fuel (1- (erl-k->fuel k))
                      :kont (make-kont-expr
                              :expr (node-call->args
                                      (kont-expr->expr (erl-k->kont k)))))))
            (node-call->fn (kont-expr->expr (erl-k->kont k)))
            (erl-val-cons->lst
              (erl-state->in (apply-k s (list (make-erl-k
                                :fuel (1- (erl-k->fuel k))
                                :kont (make-kont-expr
                                        :expr (node-call->args
                                                (kont-expr->expr (erl-k->kont k)))))))))))
        (list
          (make-erl-k 
            :fuel (+ -2 (erl-k->fuel k))
            :kont
              (make-kont-exprs
                :exprs
                  (mv-nth
                    1 
                    (eval-local-call
                      (apply-k
                        s
                        (list (make-erl-k
                                :fuel (1- (erl-k->fuel k))
                                :kont (make-kont-expr
                                        :expr (node-call->args
                                                (kont-expr->expr (erl-k->kont k)))))))
                      (node-call->fn (kont-expr->expr (erl-k->kont k)))
                      (erl-val-cons->lst
                        (erl-state->in (apply-k s (list (make-erl-k
                                          :fuel (1- (erl-k->fuel k))
                                          :kont (make-kont-expr
                                                  :expr (node-call->args
                                                          (kont-expr->expr (erl-k->kont k)))))))))))))))))
  :disable
    (apply-k-of-expr-local-call-1
     apply-k-of-expr-local-call-when-function-has-body
     apply-k-of-expr-local-call-when-function-has-no-body)
  :use ((:instance apply-k-of-expr-local-call-when-function-has-body)
        (:instance apply-k-of-expr-local-call-when-function-has-no-body)))


(local (defrule bind-mod-of-eval-local-call-when-no-match
  (implies
    (and (not (mv-nth 1 (eval-local-call s f args)))
         (wf-state-p (mv-nth 0 (eval-local-call s  f args))))
    (equal (update-erl-state->bind-mod
             (mv-nth 0 (eval-local-call s  f args))
             (erl-state->bind s)
             (erl-state->module s))
           (mv-nth 0 (eval-local-call s  f args))))
  :enable
    (update-erl-state->bind-mod update-erl-state->bind
     update-erl-state->mod update-erl-state->in eval-local-call)))


(defrule apply-k-of-expr-local-call-wf
  (implies
    (and (> (erl-k->fuel k) 4)
         (wf-state-p (apply-k s (cons k nil)))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :call))
    (equal
      (apply-k s (cons k nil))
      (update-erl-state->bind-mod
        (apply-k
          (mv-nth
            0 
            (eval-local-call
              (apply-k
                s
                (list (make-erl-k
                        :fuel (1- (erl-k->fuel k))
                        :kont (make-kont-expr
                                :expr (node-call->args
                                        (kont-expr->expr (erl-k->kont k)))))))
              (node-call->fn (kont-expr->expr (erl-k->kont k)))
              (erl-val-cons->lst
                (erl-state->in (apply-k s (list (make-erl-k
                                  :fuel (1- (erl-k->fuel k))
                                  :kont (make-kont-expr
                                          :expr (node-call->args
                                                  (kont-expr->expr (erl-k->kont k)))))))))))
          (list
            (make-erl-k 
              :fuel (+ -2 (erl-k->fuel k))
              :kont
                (make-kont-exprs
                  :exprs
                    (mv-nth
                      1 
                      (eval-local-call
                        (apply-k
                          s
                          (list (make-erl-k
                                  :fuel (1- (erl-k->fuel k))
                                  :kont (make-kont-expr
                                          :expr (node-call->args
                                                  (kont-expr->expr (erl-k->kont k)))))))
                        (node-call->fn (kont-expr->expr (erl-k->kont k)))
                        (erl-val-cons->lst
                          (erl-state->in (apply-k s (list (make-erl-k
                                            :fuel (1- (erl-k->fuel k))
                                            :kont (make-kont-expr
                                                    :expr (node-call->args
                                                            (kont-expr->expr (erl-k->kont k)))))))))))))))
          (erl-state->bind
            (apply-k
              s
              (list (make-erl-k
                      :fuel (1- (erl-k->fuel k))
                      :kont (make-kont-expr
                              :expr (node-call->args
                                      (kont-expr->expr (erl-k->kont k))))))))
          (erl-state->module
            (apply-k
              s
              (list (make-erl-k
                      :fuel (1- (erl-k->fuel k))
                      :kont (make-kont-expr
                              :expr (node-call->args
                                      (kont-expr->expr (erl-k->kont k)))))))))))
  :disable
    (apply-k-of-expr-local-call-1
     apply-k-of-expr-local-call-when-function-has-body
     apply-k-of-expr-local-call-when-function-has-no-body
     apply-k-of-exprs
     bind-mod-of-eval-local-call-when-no-match)
  :use ((:instance apply-k-of-expr-local-call-when-function-has-body)
        (:instance apply-k-of-expr-local-call-when-function-has-no-body)
        (:instance bind-mod-of-eval-local-call-when-no-match
          (s (apply-k s (list (erl-k (+ -1 (erl-k->fuel k))
                                     (kont-expr
                                      (node-call->args (kont-expr->expr (erl-k->kont k))))))))
          (args
            (erl-val-cons->lst
              (erl-state->in
                (apply-k s (list (erl-k (+ -1 (erl-k->fuel k))
                                        (kont-expr
                                          (node-call->args
                                            (kont-expr->expr (erl-k->kont k))))))))))
          (f (node-call->fn (kont-expr->expr (erl-k->kont k)))))))