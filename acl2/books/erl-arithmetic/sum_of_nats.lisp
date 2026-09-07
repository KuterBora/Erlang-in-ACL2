(in-package "ACL2")
(include-book "../../theorems/top")

(set-induction-depth-limit 1)

; ACL2 sum_of_nats
(define sum-of-nats ((n natp))
  (b* ((n (nfix n))
       ((if (= n 0)) 0))
      (+ n (sum-of-nats (1- n)))))

;; An Erlang World with the following functions defined locally:
;; - Remark: When Erlang is run on the command line, the module is set to 'local.
;;   Normally, functions like [add] would be defined in a different module
;;   which we would then have to import (or do a remote call [m:f()]) but I will
;;   ignore that here for simplicity by defining [add] in the local module.
;;
;; sum_of_nats(0) -> 0;
;; sum_of_nats(X) when is_integer(X), X > 0 -> X + sum_of_nats(X - 1).
;;
(define sum-test-w ()
  :returns (w world-p)
  :enabled t
  '((local
      (attrs (module . local)
             (export)
             (import))
      (fn-defns
        (((name . sum_of_nats) (arity . 1)) ;; sum_of_nats(0) -> 0;
         ((cases (:integer 0))
          (guards)
          (body (:integer 0)))
         ((cases (:var X)) ;; sum_of_nats(X) when is_integer(X), X > 0 -> X + sum_of_nats(X - 1).
          (guards ((:call is_integer (:cons (:var X) (:nil))) 
                   (:binop > (:var X) (:integer 0))))
          (body (:binop
                  +
                  (:var X) 
                  (:call 
                    sum_of_nats
                    (:cons (:binop - (:var X) (:integer 1)) 
                           (:nil)))))))))))

; While it is not necessary to admit the theorem below, this lemma speeds up 
; the proof quite a bit. ACL2 has an easier time dealing with the cases of 
; eval-local-call and apply-k separately.
(defrule local-call-of-sum-of-nats
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
      (eval-local-call s 'sum_of_nats args)
      (if (> (erl-val-integer->val (car args)) 0)
          (mv (update-erl-state->bind
                (update-erl-state->in s (car args))
                (omap::update 'X (car args) nil))
              '((:binop 
                  + 
                  (:var X) 
                  (:call 
                    sum_of_nats 
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

; Induction schema for apply-k-of-sum-of-nats
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
            (update-erl-state->bind
              (update-erl-state->in
                args
                (erl-val-cons
                  (list (erl-val-integer
                              (+ -1
                                (erl-val-integer->val
                                      (car (erl-val-cons->lst (erl-state->in args)))))))))
              (omap::update 'x
                            (car (erl-val-cons->lst (erl-state->in args)))
                            nil))
            (erl-k (+ -5 (erl-k->fuel k))
                        '(:local-call sum_of_nats)))))))

; Base case of calling apply-k with sum_of_nats
(defrule apply-k-of-sum-of-nats-base-case
  (implies 
    (and
      (wf-state-p s)
      (> (erl-k->fuel k) 5)

      ; the module and the world are correct
      (equal (erl-state->world s) (sum-test-w))
      (equal (erl-state->module s) 'local)
      
      ; the next continuation is a call to [sum_of_nats]
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum_of_nats)
      
      ; the arguments are well-formed
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)

      ; the first (and only) argument is 0
      (equal (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0))

    (equal (erl-state->in (apply-k s (list k)))
           (erl-val-integer 0)))
  :use ((:instance apply-k-of-local-call-when-match)))

; If evaluation does not fail, nor will evaluating the next the recursive call.
; Remark: the reason this theorem takes so many steps seems to be case splits caused by nfix.
; one way to solve this might be to disable nfix initially, and only expand it when needed.
(defrule inductive-step-is-wf
  (implies 
    (and
      ; there is enough fuel to step to the next recuirsive call
      (< 8 (erl-k->fuel k))

      ; the module and the world are correct
      (equal (erl-state->world s) (sum-test-w))
      (equal (erl-state->module s) 'local)
      
      ; the next continuation is a call to [sum_of_nats]
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum_of_nats)
      
      ; the arguments are well-formed
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)

      ; the first (and only) argument is greater than or equal to 0.
      (> (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0)
      
      ; Let's assume the result is well-formed
      (wf-state-p (apply-k s (cons k nil))))
    (wf-state-p
       (apply-k
          (update-erl-state->bind
           (update-erl-state->in
             s
             (erl-val-cons
               (list (erl-val-integer
                       (+ -1
                          (erl-val-integer->val
                            (car (erl-val-cons->lst (erl-state->in s)))))))))
           (omap::update 'x
                         (car (erl-val-cons->lst (erl-state->in s)))
                         nil))
         (list (erl-k (+ -5 (erl-k->fuel k))
                     '(:local-call sum_of_nats))))))
  :use ((:instance apply-k-of-local-call-when-match))
  :enable (apply-k-of-binop-expr1 apply-k-of-cons))

; steps: 252227
; Evaluating the call until the next recursive call will produce the following term.
; Remark: the reason this theorem takes so many steps seems to be case splits caused by nfix.
; one way to solve this might be to disable nfix initially, and only expand it when needed.
(defrule inductive-step-up-to-next-recursive-call
  (implies 
    (and
      (< 8 (erl-k->fuel k))

      ; the module and the world are correct
      (equal (erl-state->world s) (sum-test-w))
      (equal (erl-state->module s) 'local)
      
      ; the next continuation is a call to [sum_of_nats]
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum_of_nats)
      
      ; the arguments are well-formed
      (wf-state-p s)
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)

      ; the first (and only) argument is greater than or equal to 0.
      (> (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0)
    
      ; Let's assumse the result is well-formed
      (wf-state-p (apply-k s (cons k nil))))
    (equal (erl-state->in (apply-k s (cons k nil)))
           (apply-erl-binop
              '+
              (car (erl-val-cons->lst (erl-state->in s)))
              (erl-state->in
                (apply-k
                  (update-erl-state->bind
                    (update-erl-state->in
                      s
                      (erl-val-cons
                        (list (erl-val-integer
                                (+ -1
                                  (erl-val-integer->val
                                        (car (erl-val-cons->lst (erl-state->in s)))))))))
                    (omap::update 'x
                                  (car (erl-val-cons->lst (erl-state->in s)))
                                  nil))
                  (list (erl-k (+ -5 (erl-k->fuel k))
                               '(:local-call sum_of_nats))))))))
  
  :disable (inductive-step-is-wf apply-k-of-sum-of-nats-base-case)
  :enable (apply-k-of-binop-expr1 apply-k-of-cons)

  ; this case split can be removed by proving a lemma regarding
  ; how a function call does not introduce any new bindings once it returns.
  ; -- If the bindings are equal, they are obviously compatible.
  :cases ((omap::compatiblep
            (erl-state->bind
              (apply-k
                (update-erl-state->bind
                  (update-erl-state->in
                    s
                    (erl-val-cons
                      (list (erl-val-integer
                              (+ -1
                                (erl-val-integer->val
                                      (car (erl-val-cons->lst (erl-state->in s)))))))))
                  (omap::update 'x
                                (car (erl-val-cons->lst (erl-state->in s)))
                                nil))
                (list (erl-k (+ -5 (erl-k->fuel k))
                            '(:local-call sum_of_nats)))))
            (omap::update 'x
                (car (erl-val-cons->lst (erl-state->in s)))
                nil)))

  :hints (("Goal" :use ((:instance apply-k-of-local-call-when-match)
                        (:instance inductive-step-is-wf)))
          ("Subgoal 1.1.1.1.1.1'"
            :cases ((equal
                      (erl-val-kind
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
                            (omap::update 'X
                                          (car (erl-val-cons->lst (erl-state->in s)))
                                          nil))
                            (list (erl-k (+ -5 (erl-k->fuel k))
                                        '(:local-call sum_of_nats))))))
                      :integer)))))

; Erlang sum_of_nats is equivalent to the ACL2 sum-of-nats, if evaluation succeeds.
(defrule apply-k-of-sum-of-nats
  (implies 
    (and
      ; there is enough fuel for each recursive call
      (< (* 8 (+ 1 (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s))))))
         (erl-k->fuel k))
      ; the module and the world are correct
      (equal (erl-state->world s) (sum-test-w))
      (equal (erl-state->module s) 'local)
      
      ; the next continuation is a call to [sum_of_nats]
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum_of_nats)
      
      ; the arguments are well-formed
      (wf-state-p s)
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)

      ; the first (and only) argument is greater than or equal to 0.
      (>= (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0)
      
      ; Let's assum_of_natse the result is well-formed
      (wf-state-p (apply-k s (cons k nil))))
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (make-erl-val-integer 
        :val
          (sum-of-nats
            (erl-val-integer->val 
              (car (erl-val-cons->lst (erl-state->in s))))))))
  :induct (apply-k-of-sum-induct s k)
  :in-theory (enable sum-of-nats))

; helper to simplify the above theorem (just replaces the argument with x).
(defrule apply-k-of-sum-of-nats-of-x
  (implies 
    (and
      (equal (* 8 (+ x 2)) (erl-k->fuel k))
      ; the module and the world are correct
      (equal (erl-state->world s) (sum-test-w))
      (equal (erl-state->module s) 'local)
      
      ; the next continuation is a call to [sum_of_nats]
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum_of_nats)
      
      ; the arguments are well-formed
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)

      ; the first (and only) argument is greater than or equal to 0.
      (natp x)
      (equal (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) x)
      
      ; Let's assume the result is well-formed
      (wf-state-p (apply-k s (cons k nil))))
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (make-erl-val-integer 
        :val (sum-of-nats x))))
  :do-not-induct t
  :disable apply-k-of-sum-of-nats
  :use (:instance apply-k-of-sum-of-nats (s s) (k k)))


; We can now use the existing ACL2 arithemtic books to reason about the sum_of_nats function!
(include-book "arithmetic/top" :dir :system)

; closed form of sum of nats
(defrule cfs 
    (implies (natp n) (equal (sum-of-nats n) (/ (* n (+ n 1)) 2)))
    :enable sum-of-nats)

(defrule apply-k-of-sum-of-nats-closed-form
  (implies 
    (and
      (equal (* 8 (+ x 2)) (erl-k->fuel k))
      ; the module and the world are correct
      (equal (erl-state->world s) (sum-test-w))
      (equal (erl-state->module s) 'local)
      
      ; the next continuation is a call to [sum_of_nats]
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum_of_nats)
      
      ; the arguments are well-formed
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s)))) :integer)

      ; the first (and only) argument is a natp
      (natp x)
      (equal (erl-val-integer->val
              (car (erl-val-cons->lst (erl-state->in s)))) x)
      
      ; Let's assume the result is well-formed
      (wf-state-p (apply-k s (cons k nil))))
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (make-erl-val-integer 
        :val  (/ (* x (+ x 1)) 2))))
  :disable (apply-k-of-sum-of-nats-of-x apply-k-of-sum-of-nats)
  :use (:instance apply-k-of-sum-of-nats-of-x))