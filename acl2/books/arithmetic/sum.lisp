(in-package "ACL2")
(include-book "../../erl-eval")
(include-book "../../theorems/core/top")
(include-book "../../theorems/state/state")
(include-book "std/lists/len" :dir :system)
; some things from state
; atomic, exprs, binop, functions, local-call

(set-induction-depth-limit 1)

; ACL2 sum-n
(define sum-n ((n natp))
  (b* ((n (nfix n))
       ((if (= n 0)) 0))
      (+ n (sum-n (1- n)))))

; Commenting this out, as it introduces rewrite rules that we do 
; not want yet.
; (defrule sum-n-formula
;   (implies (natp n)
;     (equal (sum-n n) (/ (* n (+ n 1)) 2)))
;   :enable (sum-n))

(define test-w ()
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

(defrule update-erl-state-in-bind-chain-rule
  (equal (update-erl-state->bind 
           (update-erl-state->in 
             (update-erl-state->bind 
               (update-erl-state->in s v1) 
                b1)
              v2)
            b2)
         (update-erl-state->bind (update-erl-state->in s v2) b2))
  :enable (update-erl-state->in update-erl-state->bind))

(defrule update-erl-state-in-bind-chain-rule-2
  (equal (update-erl-state->bind 
           (update-erl-state->in (update-erl-state->bind s b1) v)
            b2)
         (update-erl-state->bind (update-erl-state->in s v) b2))
  :enable (update-erl-state->in update-erl-state->bind))

(defrule update-erl-state-in-chain-rule
  (equal (update-erl-state->in (update-erl-state->in s v1) v2)
         (update-erl-state->in s v2))
  :enable (update-erl-state->in))


; TODO: ask mark how to generalize these
(defrule update-lookup-crock
  (equal (omap::lookup s (omap::update s x m)) x)
    :enable omap::lookup)

(defrule update-lookup-crock-2
  (implies 
    (not (equal s1 s2))
    (equal (omap::lookup s2 (omap::update s1 x1 (omap::update s2 x2 m))) x2))
    :enable omap::lookup)

(defrule additional-update-crock
  (equal (update-erl-state->in (update-erl-state->bind s b) in)
         (update-erl-state->bind (update-erl-state->in s in) b))
  :enable (update-erl-state->in update-erl-state->bind))

; TODO: generalize?
(defrule even-more-crock-lemmas-1
  (implies (and (erl-val-p x)
                (equal (erl-val-kind x) :integer)
                (equal (erl-val-integer->val x) 0))
           (equal x '(:integer 0)))
  :enable (erl-val-kind erl-val-integer->val erl-val-p)
  :expand (TRUE-LISTP (CDR X))
  :rule-classes :forward-chaining)

(defrule update-erl-state-bind-chain-rule
  (equal (update-erl-state->bind (update-erl-state->bind s b1) b2)
         (update-erl-state->bind s b2))
  :enable (update-erl-state->bind))

(defrule eval-clauses-of-sum-base-case
  (implies
    (and (wf-state-p s)
         (equal (erl-state->world s) (test-w))
         (equal (erl-state->module s) 'local)
         
         ; TODO: ask mark how to simplify this
         (erl-vlst-p args)
         (car args)
         (not (cdr args))
         (equal (erl-val-kind (car args)) :integer)
         (equal (erl-val-integer->val (car args)) 0))
    (equal (eval-clauses
             args
             '(((cases (:integer 0))
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
                                (:nil)))))))
                  (update-erl-state->bind s nil))
            (mv (update-erl-state->bind
                 (update-erl-state->in s (car args))
                 nil)
                (list (make-erl-val-integer :val 0)))))
  :enable 
    (eval-clauses
     eval-clauses-when-consp
     match-args
     eval-match
     eval-guard-seq
     EVAL-GUARD-SEQ-WHEN-CONSP
     EVAL-GUARD
     EVAL-GUARD-EXPR
     eval-bif
     apply-erl-binop
     apply-erl-comp-binop
     erl-compare)
  :do-not-induct t)

(defrule eval-clauses-of-sum-inductive-step
  (implies
    (and (wf-state-p s)
         (equal (erl-state->world s) (test-w))
         (equal (erl-state->module s) 'local)
         
         ; TODO: ask mark how to simplify this
         (erl-vlst-p args)
         (car args)
         (not (cdr args))
         (equal (erl-val-kind (car args)) :integer)
         (> (erl-val-integer->val (car args)) 0))
    (equal (eval-clauses
             args
             '(((cases (:integer 0))
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
                                (:nil)))))))
                  (update-erl-state->bind s nil))
           (mv (update-erl-state->bind
                 (update-erl-state->in s (car args))
                 (omap::update 'X (car args) nil))
               '((:binop 
                  + 
                  (:var X) 
                  (:call 
                    sum 
                    (:cons (:binop - (:var X) (:integer 1)) 
                          (:nil))))))))
  :enable 
    (eval-clauses
     eval-clauses-when-consp
     match-args
     eval-match
     eval-guard-seq
     EVAL-GUARD-SEQ-WHEN-CONSP
     EVAL-GUARD
     EVAL-GUARD-EXPR
     eval-bif
     apply-erl-binop
     apply-erl-comp-binop
     erl-compare)
  :do-not-induct t)

(defrule eval-clauses-of-sum-negative
  (implies
    (and (wf-state-p s)
         (equal (erl-state->world s) (test-w))
         (equal (erl-state->module s) 'local)
         
         ; TODO: ask mark how to simplify this
         (erl-vlst-p args)
         (car args)
         (not (cdr args))
         (equal (erl-val-kind (car args)) :integer)
         (< (erl-val-integer->val (car args)) 0))
    (equal (eval-clauses
             args
             '(((cases (:integer 0))
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
                                (:nil)))))))
                  (update-erl-state->bind s nil))
           (mv (update-erl-state->bind s nil) nil)))
  :enable 
    (eval-clauses
     eval-clauses-when-consp
     match-args
     eval-match
     eval-guard-seq
     EVAL-GUARD-SEQ-WHEN-CONSP
     EVAL-GUARD
     EVAL-GUARD-EXPR
     eval-bif
     apply-erl-binop
     apply-erl-comp-binop
     erl-compare)
  :do-not-induct t)


(defrule local-call-of-sum-base-case
  (implies
    (and (wf-state-p s)
         (equal (erl-state->world s) (test-w))
         (equal (erl-state->module s) 'local)
         (erl-vlst-p args)
         (car args)
         (not (cdr args))
         (equal (erl-val-kind (car args)) :integer)
         (equal (erl-val-integer->val (car args)) 0))
    (equal (eval-local-call s 'sum args)
           (mv (update-erl-state->bind
                 (update-erl-state->in s (car args))
                 nil)
               '((:integer 0)))))
    :enable eval-local-call)

(defrule local-call-of-sum-base-inductive
  (implies
    (and (wf-state-p s)
         (equal (erl-state->world s) (test-w))
         (equal (erl-state->module s) 'local)
         (erl-vlst-p args)
         (car args)
         (not (cdr args))
         (equal (erl-val-kind (car args)) :integer)
         (> (erl-val-integer->val (car args)) 0))
    (equal (eval-local-call s 'sum args)
           (mv (update-erl-state->bind
                 (update-erl-state->in s (car args))
                 (omap::update 'X (car args) nil))
               '((:binop 
                  + 
                  (:var X) 
                  (:call 
                    sum 
                    (:cons (:binop - (:var X) (:integer 1)) 
                          (:nil))))))))
    :enable eval-local-call)

(defrule local-call-of-sum
  (implies
    (and (wf-state-p s)
         (equal (erl-state->world s) (test-w))
         (equal (erl-state->module s) 'local)
         (erl-vlst-p args)
         (car args)
         (not (cdr args))
         (equal (erl-val-kind (car args)) :integer))
    (equal (eval-local-call s 'sum args)
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
    :enable eval-local-call)

(include-book "../../theorems/kont-step/local-call")
(include-book "../../theorems/kont-step/functions")
(include-book "../../theorems/kont-step/exprs")
(include-book "../../theorems/kont-step/binop")
(include-book "../../theorems/kont-step/atomic")

; (defrule lemma-apply-erl-binop
;   (implies 
;     (and (erl-val-p left)
;          (erl-val-p right)
;          (equal (erl-val-kind left) :integer)
;          (equal (erl-val-kind right) :integer))
;     (equal (apply-erl-binop '+ left right)
;            (make-erl-val-integer 
;             :val (+ (erl-val-integer->val left)
;                     (erl-val-integer->val right)))))
;   :enable (apply-erl-binop apply-erl-arithm-binop erl-add))

(defrule the-great-type-lemma
  (implies 
    (and 
      (wf-state-p s)
      (erl-k-p k)
      (equal (erl-state->world s) (test-w))
      (equal (erl-state->module s) 'local)
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum)
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s))))
             :integer)
      (>= (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0)
      (wf-state-p (apply-k s (cons k nil))))
    (equal (erl-val-kind (erl-state->in (apply-k s (cons k nil)))) :integer))
  :disable (eval-k-of-local-call->s eval-k-of-local-call->klst)
  :enable (apply-erl-binop apply-erl-arithm-binop erl-add)
  :expand (EVAL-K K S))


; THis is the path for when > 0


(in-theory (disable eval-k-of-local-call->s eval-k-of-local-call->klst))
(include-book "../../theorems/kont-step/cons")

(defrule chain-of-in-bind
  (equal (update-erl-state->in-bind (update-erl-state->in-bind s v1 b1) v2 b2)
             (update-erl-state->in-bind s v2 b2))
  :enable update-erl-state->in-bind)

(defrule in-bind-of-in
  (equal (update-erl-state->in-bind (update-erl-state->in s v1) v2 b2)
             (update-erl-state->in-bind s v2 b2))
  :enable (update-erl-state->in update-erl-state->in-bind))

(defrule in-bind-of-bind
  (equal (update-erl-state->in-bind (update-erl-state->bind s b1) v2 b2)
             (update-erl-state->in-bind s v2 b2))
  :enable (update-erl-state->bind update-erl-state->in-bind))


(include-book "std/omaps/top" :dir :system)

(defrule update*-dup
  (implies (omap::mapp map) (equal (omap::update* map map) map)))


(in-theory
  (disable 
    ERL-K-P-WHEN-MEMBER-EQUAL-OF-ERL-KLST-P
    EVAL-K-OF-CONS-MERGE-NONCONS->S
    EVAL-K-OF-CONS-MERGE-CONS-INCOMPATIBLE->S
    EVAL-K-OF-CONS-MERGE-CONS-COMPATIBLE->S
    ERL-VAL-FIX-WHEN-NONE
    ERL-VAL-FIX-WHEN-FLIMIT
    DEFAULT-<-2
    DEFAULT-<-1
    DEFAULT-+-2
    DEFAULT-+-1
    ERL-VAL-P-WHEN-MEMBER-EQUAL-OF-ERL-VLST-P
    ERL-KLST-P-WHEN-SUBSETP-EQUAL
    ERL-VAL-P-WHEN-ERL-FUN-P-REWRITE
    ERL-VAL-P-WHEN-ERL-FUN-P-REWRITE
    APPLY-K-OF-REJECT
    APPLY-K-OF-FLIMIT
    APPLY-K-OF-EXCPT))

(set-case-split-limitations '(5 4))

; runs faster when given fuel > 10
(defrule the-great-lemma-1
  (implies 
    (and
      (wf-state-p s)
      (erl-k-p k)
      (wf-state-p (apply-k s (cons k nil)))
      (equal (erl-state->world s) (test-w))
      (equal (erl-state->module s) 'local)
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum)
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s))))
             :integer)
      (> (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0)
      (equal (erl-val-kind (erl-state->in (apply-k s (cons k nil)))) :integer))
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (erl-add
        (CAR (ERL-VAL-CONS->LST (ERL-STATE->IN S)))
        (erl-state->in
          (apply-k 
            (update-erl-state->in-bind
              s
              (erl-val-cons
                (list (erl-val-integer
                        (+ -1 
                          (erl-val-integer->val 
                            (car (erl-val-cons->lst (erl-state->in s))))))))
              (omap::update 
                'x
                (car (erl-val-cons->lst (erl-state->in s)))
                nil))
            (list (ERL-K (+ -5 (ERL-K->FUEL K))
                '(:LOCAL-CALL SUM)))
            )))))
:expand (eval-k k s)
:do-not-induct t
:enable (apply-erl-binop APPLY-ERL-ARITHM-BINOP erl-sub erl-add))

(defrule the-great-lemma-2
  (implies 
    (and
      (wf-state-p s)
      (erl-k-p k)
      (wf-state-p (apply-k s (cons k nil)))
      (equal (erl-state->world s) (test-w))
      (equal (erl-state->module s) 'local)
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum)
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s))))
             :integer)
      (= (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0)
      (equal (erl-val-kind (erl-state->in (apply-k s (cons k nil)))) :integer))
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (make-erl-val-integer :val 0)))
:expand (eval-k k s)
:do-not-induct t
:enable (apply-erl-binop APPLY-ERL-ARITHM-BINOP erl-sub erl-add))

(set-induction-depth-limit 1)
(define sum-n ((n natp))
  (b* ((n (nfix n))
       ((if (= n 0)) 0))
      (+ n (sum-n (1- n)))))


(define crock-induct (args k)
  (declare (irrelevant k))
  :verify-guards nil
  :enabled t
  :measure (nfix (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in args)))))
  (if (< (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in args)))) 0)
      nil
      (if (= (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in args)))) 0)
          t
          (crock-induct
            (update-erl-state->in-bind
              args
              (erl-val-cons
                (list (erl-val-integer
                        (+ -1 
                          (erl-val-integer->val 
                            (car (erl-val-cons->lst (erl-state->in args))))))))
              (omap::update 
                'x
                (car (erl-val-cons->lst (erl-state->in args)))
                nil))
            (ERL-K (+ -5 (erl-k->fuel k))
                '(:LOCAL-CALL SUM))))))


(defrule the-great-lemma-3
  (implies 
    (and
      (wf-state-p s)
      (erl-k-p k)
      (wf-state-p (apply-k s (cons k nil)))
      (equal (erl-state->world s) (test-w))
      (equal (erl-state->module s) 'local)
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum)
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s))))
             :integer)
      (> (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0)
      (equal (erl-val-kind (erl-state->in (apply-k s (cons k nil)))) :integer))
    (equal
      (erl-val-kind 
        (erl-state->in
          (apply-k 
            (update-erl-state->in-bind
              s
              (erl-val-cons
                (list (erl-val-integer
                      (+ -1 
                        (erl-val-integer->val 
                          (car (erl-val-cons->lst (erl-state->in s))))))))
              (omap::update 
                'x
                (car (erl-val-cons->lst (erl-state->in s)))
                nil))
            (list (ERL-K (+ -5 (ERL-K->FUEL K))
                '(:LOCAL-CALL SUM))))))
    :integer))
  :use (:instance the-great-lemma-1)
  :enable erl-add)



(defrule the-great-induction
  (implies 
    (and
      (wf-state-p s)
      (erl-k-p k)
      (equal (erl-state->world s) (test-w))
      (equal (erl-state->module s) 'local)
      (equal (kont-kind (erl-k->kont k)) :local-call)
      (equal (kont-local-call->call (erl-k->kont k)) 'sum)
      (equal (erl-val-kind (erl-state->in s)) :cons)
      (car (erl-val-cons->lst (erl-state->in s)))
      (not (cdr (erl-val-cons->lst (erl-state->in s))))
      (equal (erl-val-kind (car (erl-val-cons->lst (erl-state->in s))))
             :integer)
      (>= (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s)))) 0)
      (wf-state-p (apply-k s (cons k nil))))
    (equal
      (erl-state->in (apply-k s (cons k nil)))
      (make-erl-val-integer 
        :val
          (sum-n (erl-val-integer->val (car (erl-val-cons->lst (erl-state->in s))))))))
:induct (crock-induct s k)
:disable (apply-k-of-step apply-k-of-consp)
:enable (sum-n erl-add))

