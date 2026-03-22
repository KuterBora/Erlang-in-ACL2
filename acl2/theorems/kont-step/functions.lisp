(in-package "ACL2")
(include-book "../core/eval-theorems")

; Function Args Kont-Step ------------------------------------------------------

; The following theorems show that evaluating a function args continuation is 
; equivalent to evaluating the arguments in order, and then returning a list
; containing their values.

; Stepping the initial continuation
(defrule eval-k-of-function-args-start->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :function-args-start)
         (kont-function-args-start->args (erl-k->kont k)))
    (equal 
      (erl-s-klst->klst (eval-k k s))
      (list 
        (make-erl-k 
          :fuel (1- (erl-k->fuel k)) 
          :kont 
            (make-kont-expr 
              :expr (car (kont-function-args-start->args (erl-k->kont k)))))
        (make-erl-k
          :fuel (1- (erl-k->fuel k)) 
          :kont 
            (make-kont-function-args 
              :done nil 
              :rest (cdr (kont-function-args-start->args (erl-k->kont k))))))))
  :enable eval-k)

(defrule eval-k-of-function-args-start->s
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :function-args-start)
         (kont-function-args-start->args (erl-k->kont k)))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)

(defrule eval-k-of-function-args-start-nil->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :function-args-start)
         (null (kont-function-args-start->args (erl-k->kont k))))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-function-args-start-nil->s
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :function-args-start)
         (null (kont-function-args-start->args (erl-k->kont k))))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->in s (make-erl-val-cons :lst nil))))
  :enable eval-k)


; Stepping the function-args continuation
(defrule eval-k-of-function-args->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :function-args)
         (kont-function-args->rest (erl-k->kont k)))
    (equal 
      (erl-s-klst->klst (eval-k k s))
      (list 
        (make-erl-k 
          :fuel (1- (erl-k->fuel k)) 
          :kont 
            (make-kont-expr 
              :expr (car (kont-function-args->rest (erl-k->kont k)))))
        (make-erl-k
          :fuel (1- (erl-k->fuel k)) 
          :kont 
            (make-kont-function-args
              :done (cons (erl-state->in s) (kont-function-args->done (erl-k->kont k)))
              :rest (cdr (kont-function-args->rest (erl-k->kont k))))))))
  :enable eval-k)

(defrule eval-k-of-function-args->s
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :function-args)
         (kont-function-args->rest (erl-k->kont k)))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->in s (make-erl-val-none))))
  :enable eval-k)

(defrule eval-k-of-function-args-nil->klst
  (implies
    (and
       (wf-state-p s) 
       (erl-k-p k)
       (> (erl-k->fuel k) 0)
       (equal (kont-kind (erl-k->kont k)) :function-args)
       (null (kont-function-args->rest (erl-k->kont k))))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-function-args-nil->s
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :function-args)
         (null (kont-function-args->rest (erl-k->kont k))))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->in
            s 
            (make-erl-val-cons 
              :lst (cons (erl-state->in s)
                         (kont-function-args->done (erl-k->kont k)))))))
  :enable eval-k)


; Stepping the function-return continuation
(defrule eval-k-of-function-return->klst
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :function-return))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-function-return->s
  (implies
    (and (wf-state-p s) 
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :function-return))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->bind-mod
            s 
            (kont-function-return->bind (erl-k->kont k))
            (kont-function-return->module (erl-k->kont k)))))
  :enable eval-k)