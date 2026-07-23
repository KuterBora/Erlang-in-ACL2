(in-package "ACL2")
(include-book "../../theorems/top")

(set-induction-depth-limit 1)

; ACL2 sum
(define sum ((n natp))
  (b* ((n (nfix n))
       ((if (= n 0)) 0))
      (+ n (sum (1- n)))))

;; An Erlang World with the following functions defined locally:
;; - Remark: When Erlang is run on the command line, the module is set to 'local.
;;   Normally, functions like [add] would be defined in a different module
;;   which we would then have to import (or do a remote call [m:f()]) but I will
;;   ignore that here for simplicity by defining [add] in the local module.
;;
;; sum(0) -> 0;
;; sum(X) when is_integer(X), X > 0 -> X + sum(X - 1).
;;
(define sum-test-w ()
  :returns (w world-p)
  :enabled t
  '((local
      (attrs (module . local)
             (export)
             (import))
      (fn-defns
        (((name . sum) (arity . 1))
         ((cases (:integer 0))
          (guards)
          (body (:integer 0)))
         ((cases (:var X))
          (guards ((:call is_integer (:cons (:var X) (:nil))) 
                   (:binop > (:var X) (:integer 0))))
          (body (:binop 
                  + 
                  (:var X) 
                  (:call 
                    sum 
                    (:cons (:binop - (:var X) (:integer 1)) 
                           (:nil)))))))))))


; While it is not necessary to admit the theorem below, this lemma speeds up 
; the proof quite a bit. ACL2 has an easier time dealing with the cases of 
; eval-local-call and apply-k separately.
(defrule local-call-of-sum
  (implies
    (and 
      (wf-state-p s)
      (equal (erl-state->world s) (sum-test-w))
      (equal (erl-state->module s) 'local)
      (erl-vlst-p args)
      (car args)
      (not (cdr args))
      (equal (erl-val-kind (car args)) :integer))
    (equal 
      (eval-local-call s 'sum args)
      (if (> (erl-val-integer->val (car args)) 0)
          (mv (update-erl-state->bind
                (update-erl-state->in s (car args))
                (omap::update 'X (car args) nil))
              '((:binop 
                  + 
                  (:var X) 
                  (:call 
                    sum 
                    (:cons (:binop - (:var X) (:integer 1)) 
                            (:nil))))))
          (if (equal (erl-val-integer->val (car args)) 0)
              (mv (update-erl-state->bind
                    (update-erl-state->in s (car args))
                    nil)
                  '((:integer 0)))
              (mv (update-erl-state->in 
                    s 
                    (make-erl-val-excpt 
                      :err
                        (make-erl-err
                          :class (make-err-class-error)
                          :reason (make-exit-reason-function-clause)))) 
                  nil)))))
  :enable
    (eval-local-call eval-clauses eval-clauses-when-consp
     match-args eval-match eval-guard-seq eval-guard-seq-when-consp
     eval-guard eval-guard-expr eval-bif apply-erl-binop
     apply-erl-comp-binop erl-compare))


; Base case of calling apply-k with sum
(defrule apply-k-of-sum-base-case
  (implies 
    (and
      ; there is enough fuel
      (> (erl-k->fuel k) 5)

      ; the module and the world are correct
      (equal (erl-state->world s) (sum-test-w))
      (equal (erl-state->module s) 'local)
      
      ; the next continuation is a call to [sum]
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum)
      
      ; the arguments are well-formed
      (wf-state-p s)
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)

      ; the first (and only) argument is 0
      (equal (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0))

    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (make-erl-val-integer :val 0)))
    :disable apply-k-of-expr-local-call-when-function-has-no-body
    :use (:instance apply-k-of-expr-local-call-when-function-has-no-body))



; Induction schema for apply-k-of-sum
(local (define apply-k-of-sum-induct (args k)
  (declare (irrelevant k))
  :measure 
    (nfix 
      (erl-val-integer->val 
        (car (erl-val-cons->lst (erl-state->in args)))))
  :verify-guards nil
  :enabled t
  (if (< (erl-val-integer->val 
            (car (erl-val-cons->lst (erl-state->in args)))) 0)
      nil
      (if (= (erl-val-integer->val 
                (car (erl-val-cons->lst (erl-state->in args)))) 0)
          t
          (apply-k-of-sum-induct
            (update-erl-state->in-bind
              args
              (erl-val-cons
                (list 
                  (erl-val-integer
                    (+ -1 
                       (erl-val-integer->val 
                         (car (erl-val-cons->lst (erl-state->in args))))))))
              (omap::update 
                'X
                (car (erl-val-cons->lst (erl-state->in args)))
                nil))
            (erl-k (+ -5 (erl-k->fuel k))
                   '(:local-call sum)))))))


(defrule apply-k-of-sum
  (implies 
    (and
      ; there is enough fuel
      (> (erl-k->fuel k) 100)

      ; the module and the world are correct
      (equal (erl-state->world s) (sum-test-w))
      (equal (erl-state->module s) 'local)
      
      ; the next continuation is a call to [sum]
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum)
      
      ; the arguments are well-formed
      (wf-state-p s)
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)

      ; the first (and only) argument is 0
      (>= (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0)
      
      ; Let's assume the result is well-formed
      (wf-state-p (apply-k s (cons k nil)))
      )
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (make-erl-val-integer 
        :val
          (sum (erl-val-integer->val 
                 (car (erl-val-cons->lst (erl-state->in s))))))))
  :induct (sum (erl-val-integer->val 
                 (car (erl-val-cons->lst (erl-state->in s))))))