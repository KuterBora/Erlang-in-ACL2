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
        (((name . sum) (arity . 1)) ;; sum(0) -> 0;
         ((cases (:integer 0))
          (guards)
          (body (:integer 0)))
         ((cases (:var X)) ;; sum(X) when is_integer(X), X > 0 -> X + sum(X - 1).
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
      (wf-state-p s)
      (> (erl-k->fuel k) 5)

      ; the module and the world are correct
      (equal (erl-state->world s) (sum-test-w))
      (equal (erl-state->module s) 'local)
      
      ; the next continuation is a call to [sum]
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum)
      
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
          (APPLY-K-of-sum-induct
            (UPDATE-ERL-STATE->BIND
              (UPDATE-ERL-STATE->IN
                args
                (ERL-VAL-CONS
                  (LIST (ERL-VAL-INTEGER
                              (+ -1
                                (ERL-VAL-INTEGER->VAL
                                      (CAR (ERL-VAL-CONS->LST (ERL-STATE->IN args)))))))))
              (OMAP::UPDATE 'X
                            (CAR (ERL-VAL-CONS->LST (ERL-STATE->IN args)))
                            NIL))
            (ERL-K (+ -5 (ERL-K->FUEL K))
                        '(:LOCAL-CALL SUM)))))))

(local (defrule fuel-crock
  (implies
    (wf-state-p (apply-k s (cons k nil)))
    (> (erl-k->fuel k) 0))
  :enable apply-k))

(local (defrule fuel-crock-rev
  (implies
    (<= (erl-k->fuel k) 0)
    (not (wf-state-p (apply-k s (cons k nil)))))
  :enable apply-k))



(defrule crock-1
  (implies
    (and (not (wf-state-p s)) (equal (erl-val-kind v) :integer))
    (equal (apply-erl-binop op v (erl-state->in s)) (erl-state->in s)))
    :enable (wf-state-p apply-erl-binop erl-val-kind))

(defrule crock-2
  (implies
    (and (wf-state-p s) (equal (erl-val-kind v) :integer))
    (wf-state-p
      (UPDATE-ERL-STATE->BIND
          (UPDATE-ERL-STATE->IN S
                                v)
          (OMAP::UPDATE 'X v NIL)))))



(defrule help-crock
  (implies 
    (and
      (< 8 (erl-k->fuel k))

      ; the module and the world are correct
      (equal (erl-state->world s) (sum-test-w))
      (equal (erl-state->module s) 'local)
      
      ; the next continuation is a call to [sum]
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum)
      
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
       (APPLY-K
        (UPDATE-ERL-STATE->BIND
        (UPDATE-ERL-STATE->IN
          S
          (ERL-VAL-CONS
            (LIST (ERL-VAL-INTEGER
                        (+ -1
                          (ERL-VAL-INTEGER->VAL
                                (CAR (ERL-VAL-CONS->LST (ERL-STATE->IN S)))))))))
        (OMAP::UPDATE 'X
                      (CAR (ERL-VAL-CONS->LST (ERL-STATE->IN S)))
                      NIL))
        (LIST (ERL-K (+ -5 (ERL-K->FUEL K))
                    '(:LOCAL-CALL SUM))))
       ))

  
  :hints (
    ("Goal" :use ((:instance apply-k-of-local-call-when-match-wf)))))


(defrule help-crock-2
  (implies 
    (and
      (< 8 (erl-k->fuel k))

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

      ; the first (and only) argument is greater than or equal to 0.
      (> (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0)
    
      ; Let's assume the result is well-formed
      (wf-state-p (apply-k s (cons k nil))))
    (equal (erl-state->in (apply-k s (cons k nil)))
          (APPLY-ERL-BINOP
            '+
            (CAR (ERL-VAL-CONS->LST (ERL-STATE->IN S)))
            (erl-state->in
              (APPLY-K
              (UPDATE-ERL-STATE->BIND
              (UPDATE-ERL-STATE->IN
                S
                (ERL-VAL-CONS
                  (LIST (ERL-VAL-INTEGER
                              (+ -1
                                (ERL-VAL-INTEGER->VAL
                                      (CAR (ERL-VAL-CONS->LST (ERL-STATE->IN S)))))))))
              (OMAP::UPDATE 'X
                            (CAR (ERL-VAL-CONS->LST (ERL-STATE->IN S)))
                            NIL))
              (LIST (ERL-K (+ -5 (ERL-K->FUEL K))
                          '(:LOCAL-CALL SUM))))))))
  
  :disable help-crock

  :cases ((omap::compatiblep
          (erl-state->bind (APPLY-K
                (UPDATE-ERL-STATE->BIND
                (UPDATE-ERL-STATE->IN
                  S
                  (ERL-VAL-CONS
                  (LIST (ERL-VAL-INTEGER
                              (+ -1
                                (ERL-VAL-INTEGER->VAL
                                      (CAR (ERL-VAL-CONS->LST (ERL-STATE->IN S)))))))))
                (OMAP::UPDATE 'X
                              (CAR (ERL-VAL-CONS->LST (ERL-STATE->IN S)))
                              NIL))
                (LIST (ERL-K (+ -5 (ERL-K->FUEL K))
                            '(:LOCAL-CALL SUM)))))
        (OMAP::UPDATE 'X
            (CAR (ERL-VAL-CONS->LST (ERL-STATE->IN S)))
            NIL)))

  :hints (
    ("Goal" :use ((:instance apply-k-of-local-call-when-match)
                  (:instance help-crock)))))











(defrule apply-k-of-sum
  (implies 
    (and
      (< (* 8 (+ 1 (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s))))))
         (erl-k->fuel k))
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

      ; the first (and only) argument is greater than or equal to 0.
      (>= (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0)
      
      ; Let's assume the result is well-formed
      (wf-state-p (apply-k s (cons k nil))))
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (make-erl-val-integer 
        :val
          (sum (erl-val-integer->val 
                 (car (erl-val-cons->lst (erl-state->in s))))))))
  :induct (apply-k-of-sum-induct s k)
  :in-theory (enable sum))


(defrule apply-k-of-sum-2
  (implies 
    (and
      (equal (* 8 (+ x 2)) (erl-k->fuel k))
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

      ; the first (and only) argument is greater than or equal to 0.
      (natp x)
      (equal (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) x)
      
      ; Let's assume the result is well-formed
      (wf-state-p (apply-k s (cons k nil))))
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (make-erl-val-integer 
        :val (sum x))))
  :do-not-induct t
  :disable apply-k-of-sum
  :use (:instance apply-k-of-sum (s s) (k k))
)


(defrule cfs 
  (implies (natp n) (equal (sum n) (/ (* n (+ n 1)) 2)))
    :enable sum)

(defrule apply-k-of-sum-closed-form
  (implies 
    (and
      (equal (* 8 (+ x 2)) (erl-k->fuel k))
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

      ; the first (and only) argument is greater than or equal to 0.
      (natp x)
      (equal (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) x)
      
      ; Let's assume the result is well-formed
      (wf-state-p (apply-k s (cons k nil))))
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (make-erl-val-integer 
        :val  (/ (* x (+ x 1)) 2))))
  :do-not-induct t
  :disable apply-k-of-sum-2
  :use (:instance apply-k-of-sum-2 (s s) (k k))
)