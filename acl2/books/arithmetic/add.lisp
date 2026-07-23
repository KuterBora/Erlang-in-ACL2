(in-package "ACL2")
(include-book "../../theorems/top")

(set-induction-depth-limit 1)

;; An Erlang World with the following functions defined locally:
;; - Remark: When Erlang is run on the command line, the module is set to 'local.
;;   Normally, functions like [add] would be defined in a different module
;;   which we would then have to import (or do a remote call [m:f()]) but I will
;;   ignore that here for simplicity by defining [add] in the local module.
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


; Steps: 71056 with the expand hints
; Steps: 96651 without the expand hints
; Why does this happen?
;
(defrule apply-k-of-add
  (b* (; The starting state is well-formed
       ((unless (wf-state-p s)) t)
       ((erl-state s) s)

       ; The state has the world defined above.
       ((unless (equal s.world (add-test-w))) t)
       ((unless (equal s.module 'local)) t)
       
       ; The next continuation calls add(X, Y).
       ((erl-k k) k)
       ((unless (> (erl-k->fuel k) 5)) t)
       ((unless (equal (kont-kind k.kont) :local-call)) t)
       ((unless (equal (kont-local-call->call (erl-k->kont k)) 'add)) t)

       ; The arguments have evaluated to a list of two integers.
       ((unless (equal (erl-val-kind (erl-state->in s)) :cons)) t)
       (vals (erl-val-cons->lst (erl-state->in s)))
       ((unless
          (and (car vals)
               (cadr vals)
               (not (cddr vals))
               (equal (erl-val-kind (car vals)) :integer)
               (equal (erl-val-kind (cadr vals)) :integer))) t))

    (equal (erl-state->in (apply-k s (cons k nil)))
           (erl-val-integer (+ (erl-val-integer->val (car vals))
                               (erl-val-integer->val (cadr vals))))))
;  :expand ((apply-k s (cons k nil)) (eval-k k s)) :disable apply-k-of-local-call-when-match
 :disable apply-k-of-expr-local-call apply-k-of-local-call-when-match
 :enable (eval-local-call eval-clauses eval-clauses-when-consp
          match-args eval-match eval-guard-seq eval-guard-seq-when-consp
          eval-guard eval-guard-expr eval-bif))



; TODO,

; - finish local call
; - sum when well formed
; - try showing wf-result bound by fuel
; - general sum
; - reduce step count in sum

; - simpl/remove make-none in eval-calls
; - hide eval-local-call etc.

; - finish kont-step, naively for now. After adding messages, get back to it.
; - more Erlang examples, list operations, for example

; - add messages and ensure nothing breaks
; - scheduler

; MORE TODO:
;   Erlang -> ACL2
; - reduce with + running
; - reduce with + proof