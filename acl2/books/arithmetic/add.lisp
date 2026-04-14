(in-package "ACL2")
(include-book "../../erl-eval")
(include-book "../../theorems/top")

(set-induction-depth-limit 1)

;; ACL2 add
(define add ((a integerp) (b integerp))
  (b* ((a (ifix a))
       (b (ifix b)))
      (+ a b)))

;; Erlang World with the following functions defined locally.
;; - When you run Erlang on the command line, the module is set to 'local.
;;   Normally, functions like add and would be defined in a different module
;;   which we would then have to import (or do a remote call m:f()) but I will
;;   ignore that here for simplicity.
;;
;; add(X, Y) when is_integer(X), is_integer(Y) -> X + Y.
;;
(define add-test-w ()
  :returns (w world-p)
  :enabled t
  '((local
      (attrs (module . local)
            (export)
            (import))
      (fn-defns
        (((name . add) (arity . 2))
         ((cases (:var X) (:var Y))
          (guards ((:call is_integer (:cons (:var X) (:nil))) 
                   (:call is_integer (:cons (:var Y) (:nil)))))
          (body (:binop
                  + 
                  (:var X) 
                  (:var Y)))))))))

; While it is not necessary to admit the theorem below, this lemma speeds up 
; the proof quite a bit. ACL2 has an easier time dealing with the cases of 
; eval-local-call and apply-k separately.
(local (defrule lemma-eval-local-call-of-add
  (implies
    (and (wf-state-p s)
         (equal (erl-state->world s) (add-test-w))
         (equal (erl-state->module s) 'local)
         (erl-vlst-p args)
         (car args)
         (cadr args)
         (not (cddr args))
         (equal (erl-val-kind (car args)) :integer)
         (equal (erl-val-kind (cadr args)) :integer))
    (equal
      (eval-local-call s 'add args)
      (mv (update-erl-state->bind
            (update-erl-state->in s (cadr args))
            (omap::update 'X (car args) (omap::update 'Y (cadr args) nil)))
          '((:binop
              + 
              (:var X) 
              (:var Y))))))
  :enable 
    (eval-local-call eval-local-call eval-clauses eval-clauses-when-consp
      match-args eval-match eval-guard-seq eval-guard-seq-when-consp
      eval-guard eval-guard-expr eval-bif)
  :do-not-induct t))


(defrule apply-k-of-add
  (b* (; The starting state is well-formed
       ((unless (wf-state-p s)) t) 
       ((erl-state s) s)
       ((unless (equal s.world (add-test-w))) t)
       ((unless (equal s.module 'local)) t)
       
       ; The next continuation calls add(X, Y)
       ((unless (erl-k-p k)) t)
       ((erl-k k) k)
       ((unless (equal (kont-kind k.kont) :expr)) t)
       ((unless (equal (node-kind (kont-expr->expr k.kont)) :call)) t)
       ((unless (equal (node-call->fn (kont-expr->expr k.kont)) 'add)) t)

       ; Result of the function call does not cause an error
       ((unless (wf-state-p (apply-k s (list k)))) t)

       ; Properties of the function arguments
       ; Remark: a lot of these can be removed with some work.
       (args
        (apply-k
          (update-erl-state->in s '(:none))
          (list
            (make-erl-k
              :fuel (1- k.fuel)
              :kont
                (make-kont-expr
                  :expr
                    (node-call->args
                      (kont-expr->expr k.kont)))))))

       ; TODO: remove this when the apply-k-of-module theorem is complete.
       ; - in ../../theorems/state/module 
       ((unless (equal (erl-state->module args) 'local)) t)

       ; The argument must evaluate to a list of two integers.
       ((unless (wf-state-p args)) t)
       ((unless (equal (erl-val-kind (erl-state->in args)) :cons)) t)
       (vals (erl-val-cons->lst (erl-state->in args)))
       ((unless 
          (and (car vals)
               (cadr vals)
               (not (cddr vals))
               (equal (erl-val-kind (car vals)) :integer)
               (equal (erl-val-kind (cadr vals)) :integer))) t))

    (equal (erl-state->in (apply-k s (cons k nil)))
           (erl-val-integer (add (erl-val-integer->val (car vals))
                                 (erl-val-integer->val (cadr vals))))))
  :enable (apply-erl-binop apply-erl-arithm-binop erl-add add)
  :case-split-limitations (5 4)
  :disable 
    (erl-k-p-when-member-equal-of-erl-klst-p default-<-2 default-<-1
     kont-expr->expr-of-kont-expr expr-fix-is-the-identity-on-expr
     expr-fix-is-the-identity-on-expr expr-call-ensures
     return-type-of-kont-expr))