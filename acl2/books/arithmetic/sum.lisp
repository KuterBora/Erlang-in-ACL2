(in-package "ACL2")
(include-book "../../erl-eval")
(include-book "../../theorems/top")
(include-book "std/omaps/top" :dir :system)

(set-induction-depth-limit 1)

; ACL2 sum
(define sum ((n natp))
  (b* ((n (nfix n))
       ((if (= n 0)) 0))
      (+ n (sum (1- n)))))

;; Erlang World with the following functions defined locally.
;; - When you run Erlang on the command line, the module is set to 'local.
;;   Normally, functions like add and would be defined in a different module
;;   which we would then have to import (or do a remote call m:f()) but I will
;;   ignore that here for simplicity.
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


; Disable useless runes for efficiency.
(local 
  (in-theory (disable 
    erl-k-p-when-member-equal-of-erl-klst-p erl-val-fix-when-none
    erl-val-fix-when-flimit default-<-2 default-<-1 default-+-2
    default-+-1 erl-val-p-when-member-equal-of-erl-vlst-p
    erl-klst-p-when-subsetp-equal erl-val-p-when-erl-fun-p-rewrite
    erl-val-p-when-erl-fun-p-rewrite apply-k-of-reject apply-k-of-flimit
    apply-k-of-excpt)))

; Base case of calling apply-k with sum
(defrule apply-k-of-sum-base-case
  (implies 
    (and
      (wf-state-p s)
      (erl-k-p k)
      (wf-state-p (apply-k s (cons k nil)))
      (equal (erl-state->world s) (sum-test-w))
      (equal (erl-state->module s) 'local)
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum)
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)
      (equal (erl-val-kind (erl-state->in (apply-k s (cons k nil)))) :integer)
      (equal (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0))
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (make-erl-val-integer :val 0)))
:expand (eval-k k s)
:enable (apply-erl-binop apply-erl-arithm-binop erl-sub erl-add))

; Inductive step of calling apply-k with sum
(defrule apply-k-of-sum-inductive-step
  (implies 
    (and
      (wf-state-p s)
      (erl-k-p k)
      (wf-state-p (apply-k s (cons k nil)))
      (equal (erl-state->world s) (sum-test-w))
      (equal (erl-state->module s) 'local)
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum)
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)
      (equal (erl-val-kind (erl-state->in (apply-k s (cons k nil)))) :integer)
      (> (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0))
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (erl-add
        (car (erl-val-cons->lst (erl-state->in s)))
        (erl-state->in
          (apply-k 
            (update-erl-state->bind
              (update-erl-state->in
                s
                (erl-val-cons
                  (list 
                    (erl-val-integer
                      (+ -1 
                        (erl-val-integer->val 
                            (car (erl-val-cons->lst (erl-state->in s)))))))))
              (omap::update 
                'X
                (car (erl-val-cons->lst (erl-state->in s)))
                nil))
            (list (erl-k (+ -5 (erl-k->fuel k))
                         '(:local-call sum)))
            )))))
:expand (eval-k k s)
:enable (apply-erl-binop apply-erl-arithm-binop erl-sub erl-add)
:disable (eval-k-of-local-call->s eval-k-of-local-call->klst)
:case-split-limitations (5 1))

; Remark: This is a rule I added after realizing ACL2 forgets that the returned
; erl-state should be well-formed after applying the rewrite rule above. This 
; lemma should trivially follow from apply-k-of-sum-inductive-step, but I will
; keep it in for now, until I figure out why it is not obvious to ACL2.
(defrule apply-k-of-sum-inductive-step-wf
  (implies 
    (and
      (wf-state-p s)
      (erl-k-p k)
      (wf-state-p (apply-k s (cons k nil)))
      (equal (erl-state->world s) (sum-test-w))
      (equal (erl-state->module s) 'local)
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum)
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)
      (equal (erl-val-kind (erl-state->in (apply-k s (cons k nil)))) :integer)
      (> (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0))
    (equal
      (erl-val-kind 
        (erl-state->in
          (apply-k 
            (update-erl-state->bind
              (update-erl-state->in s
                (erl-val-cons
                  (list
                    (erl-val-integer
                      (+ -1 
                         (erl-val-integer->val 
                           (car (erl-val-cons->lst (erl-state->in s)))))))))
              (omap::update 
                'x
                (car (erl-val-cons->lst (erl-state->in s)))
                nil))
            (list (erl-k (+ -5 (erl-k->fuel k))
                         '(:local-call sum))))))
    :integer))
  :use (:instance apply-k-of-sum-inductive-step)
  :enable erl-add
  :disable (eval-k-of-local-call->s eval-k-of-local-call->klst))

; This theorem later allows erl-val-integer->val to be called on the result
; of (apply-k s (cons k nil)) without needing to expand more terms.
(defrule val-kind-of-apply-k-of-sum
  (implies 
    (and 
      (wf-state-p s)
      (erl-k-p k)
      (equal (erl-state->world s) (sum-test-w))
      (equal (erl-state->module s) 'local)
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum)
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)
      (>= (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0)
      (wf-state-p (apply-k s (cons k nil))))
    (equal (erl-val-kind (erl-state->in (apply-k s (cons k nil)))) :integer))
  :expand (eval-k k s)
  :enable (apply-erl-binop apply-erl-arithm-binop erl-add)
  :disable (eval-k-of-local-call->s eval-k-of-local-call->klst)
  :case-split-limitations (5 1))

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

; apply-k-of-sum is equivalent to the lisp sum.
(defrule apply-k-of-sum-kont
  (implies 
    (and
      (wf-state-p s)
      (erl-k-p k)
      (equal (erl-state->world s) (sum-test-w))
      (equal (erl-state->module s) 'local)
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum)
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)
      (wf-state-p (apply-k s (cons k nil)))
      (>= (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0))
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (make-erl-val-integer 
        :val
          (sum (erl-val-integer->val 
                 (car (erl-val-cons->lst (erl-state->in s))))))))
:induct (apply-k-of-sum-induct s k)
:enable (sum erl-add)
:disable (apply-k-of-step apply-k-of-consp))


; Remark: I should be able to remove the use hint with some work.
(defrule apply-k-of-sum
  (b* (; The starting state is well-formed
       ((unless (wf-state-p s)) t) 
       ((erl-state s) s)
       ((unless (equal s.world (sum-test-w))) t)
       ((unless (equal s.module 'local)) t)
       
       ; The next continuation calls sum(N)
       ((unless (erl-k-p k)) t)
       ((erl-k k) k)
       ((unless (equal (kont-kind k.kont) :expr)) t)
       ((unless (equal (node-kind (kont-expr->expr k.kont)) :call)) t)
       ((unless (equal (node-call->fn (kont-expr->expr k.kont)) 'sum)) t)

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

       ; TODO: remove this when the apply-k-of-module theorem is complete
       ; - in ../../theorems/state/module 
       ((unless (equal (erl-state->module args) 'local)) t)

       ; The argument must evaluate to a list of two integers.
       ((unless (wf-state-p args)) t)
       ((unless (equal (erl-val-kind (erl-state->in args)) :cons)) t)
       (vals (erl-val-cons->lst (erl-state->in args)))
       ((unless 
          (and (car vals)
               (equal (erl-val-kind (car vals)) :integer)
               (>= (erl-val-integer->val (car vals)) 0)
               (not (cdr vals)))) t))

    (equal (erl-state->in (apply-k s (cons k nil)))
           (erl-val-integer (sum (erl-val-integer->val (car vals))))))
  :disable 
    (erl-k-p-when-member-equal-of-erl-klst-p default-<-2 default-<-1
     kont-expr->expr-of-kont-expr expr-fix-is-the-identity-on-expr
     expr-fix-is-the-identity-on-expr expr-call-ensures
     return-type-of-kont-expr eval-k-of-local-call->s 
     eval-k-of-local-call->klst)
  :case-split-limitations (5 1)
  :use 
    (:instance apply-k-of-sum-kont
      (s (apply-k
          (update-erl-state->in s '(:none))
          (list
            (make-erl-k
              :fuel (1- (erl-k->fuel k))
              :kont
                (make-kont-expr
                  :expr
                    (node-call->args
                      (kont-expr->expr (erl-k->kont k))))))))
      (k (erl-k (+ -1 (erl-k->fuel k))
                '(:local-call sum)))))