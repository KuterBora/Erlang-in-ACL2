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

(defrule apply-k-of-expr-local-call
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
    (:instance apply-k-of-expr-when-diff-val
      (s1 (update-erl-state->in s (make-erl-val-none)))
      (s2 s)
      (k (make-erl-k
            :fuel (1- (erl-k->fuel k))
            :kont (make-kont-expr
                    :expr (node-call->args
                            (kont-expr->expr (erl-k->kont k))))))))

(defruled apply-k-of-local-call-no-match
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
  :enable apply-k-of-step)

(defruled apply-k-of-local-call-when-match
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
  :enable apply-k-of-step)

; apply-k when wf --------------------------------------------------------------

(local (defrule fuel-crock
  (implies
    (wf-state-p (apply-k s (cons k nil)))
    (> (erl-k->fuel k) 0))
  :enable apply-k))

; expr-local-call
(defrule expr-local-call-has-enough-fuel-when-wf
  (implies
    (and (wf-state-p (apply-k s (cons k nil)))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :call))
    (> (erl-k->fuel k) 1))
  :disable (apply-k-of-expr-local-call fuel-crock)
  :use ((:instance fuel-crock
          (s s)
          (k (erl-k
              (+ -1 (erl-k->fuel k))
              (kont-expr (node-call->args (kont-expr->expr (erl-k->kont k)))))))
        (:instance apply-k-of-expr-local-call)))

(defrule expr-local-call-args-wf
  (implies
    (and (wf-state-p (apply-k s (cons k nil)))
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :call))
    (wf-state-p
      (apply-k s (list (make-erl-k
                         :fuel (1- (erl-k->fuel k))
                         :kont (make-kont-expr
                                 :expr (node-call->args
                                         (kont-expr->expr (erl-k->kont k)))))))))
  :disable (apply-k-of-expr-local-call)
  :use (:instance apply-k-of-expr-local-call))

; kont local call

(defrule local-call-has-enough-fuel-when-wf
  (implies
    (and (wf-state-p (apply-k s (cons k nil)))
         (equal (kont-kind (erl-k->kont k)) :local-call))
     (> (erl-k->fuel k) 0))
:disable (apply-k-of-local-call-no-match
          apply-k-of-local-call-when-match
          erl-state-of-wf-apply-k)
:use ((:instance apply-k-of-local-call-no-match)
      (:instance apply-k-of-local-call-when-match)
      (:instance fuel-crock)))

(defrule local-call-args-are-cons-when-wf
  (implies
    (and (wf-state-p (apply-k s (cons k nil)))
         (equal (kont-kind (erl-k->kont k)) :local-call))
    (equal (erl-val-kind (erl-state->in s)) :cons))
  :expand (apply-k s (cons k nil))
  :disable (local-call-has-enough-fuel-when-wf
            eval-k-of-local-call->klst
            eval-k-of-local-call->s)
  :use ((:instance local-call-has-enough-fuel-when-wf)
        (:instance eval-k-of-local-call->klst)
        (:instance eval-k-of-local-call->s)))

(defrule eval-local-call-wf-when-apply-local-call-wf
  (implies
    (and (wf-state-p (apply-k s (cons k nil)))
         (equal (kont-kind (erl-k->kont k)) :local-call))
    (wf-state-p
      (mv-nth 
        0
        (eval-local-call
          s
          (kont-local-call->call (erl-k->kont k))
          (erl-val-cons->lst
            (erl-state->in s))))))
  :disable (apply-k-of-local-call-no-match
            apply-k-of-local-call-when-match)
  :use ((:instance apply-k-of-local-call-no-match)
        (:instance apply-k-of-local-call-when-match)))

; !!!!
(defruled apply-k-of-local-call-no-match-wf
  (implies
    (and (wf-state-p (apply-k s (cons k nil)))
         (not (mv-nth 
                1 
                (eval-local-call
                  s
                  (kont-local-call->call (erl-k->kont k))
                  (erl-val-cons->lst (erl-state->in s)))))
         (equal (kont-kind (erl-k->kont k)) :local-call))
    (equal (apply-k s (cons k nil))
           (mv-nth 
              0 
              (eval-local-call
                s
                (kont-local-call->call (erl-k->kont k))
                (erl-val-cons->lst (erl-state->in s))))))
  :use (:instance apply-k-of-local-call-no-match))

; (defrule local-call-match-has-enough-fuel-when-wf
;   (implies
;     (and (wf-state-p (apply-k s (cons k nil)))
;          (mv-nth 
;             1 
;             (eval-local-call
;               s
;               (kont-local-call->call (erl-k->kont k))
;               (erl-val-cons->lst (erl-state->in s))))
;          (equal (kont-kind (erl-k->kont k)) :local-call))
;      (> (erl-k->fuel k) 2))
;   :disable (erl-state-of-wf-apply-k
;             fuel-crock)
;   :use ((:instance apply-k-of-local-call-no-match)
;         (:instance apply-k-of-local-call-when-match)
;         (:instance fuel-crock)
;         (:instance fuel-crock
;           (s (mv-nth 0
;               (eval-local-call s
;                                 (kont-local-call->call (erl-k->kont k))
;                                 (erl-val-cons->lst (erl-state->in s)))))
;           (k (erl-k
;               (+ -1 (erl-k->fuel k))
;               (kont-exprs
;                 (mv-nth 1
;                         (eval-local-call s
;                                           (kont-local-call->call (erl-k->kont k))
;                                           (erl-val-cons->lst (erl-state->in s))))))))))

; !!!
(defruled apply-k-of-local-call-when-match-wf
  (implies
    (and (wf-state-p (apply-k s (cons k nil)))
         (mv-nth 
           1 
           (eval-local-call
             s
             (kont-local-call->call (erl-k->kont k))
             (erl-val-cons->lst (erl-state->in s))))
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
  :use (:instance apply-k-of-local-call-when-match))