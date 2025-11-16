(in-package "ACL2")
(include-book "eval-guards")
(include-book "eval-match")

; Evaluate Erlang Clauses ------------------------------------------------------

; Returns the body of the first clause which has patterns that match args,
; and guards that evaluate to true. If no clauses match, nil is returned,
; and the caller can decide on the appropiate clause error.
(define eval-clauses ((args erl-vlst-p) (cs erl-clause-list-p) (bind bind-p))
  :returns (mv (v erl-val-p) (b bind-p) (body expr-list-p))
  :measure (len (erl-clause-list-fix cs))
  :verify-guards nil
  (b* ((args (erl-vlst-fix args))
       (cs (erl-clause-list-fix cs))
       (bind (bind-fix bind))
       ((if (null cs)) (mv (make-erl-val-none) nil nil))
       (cases (node-clause->cases (car cs)))
       (guards (node-clause->guards (car cs)))
       ((mv match-result match-bind) (match-args cases args bind))
       ((if (equal (erl-val-kind match-result) :reject)) 
        (mv match-result nil nil))
       ((if (equal (erl-val-kind match-result) :excpt)) 
        (eval-clauses args (cdr cs) bind))
       (guard-result (eval-guards guards match-bind))
       ((if (equal (erl-val-kind guard-result) :reject)) 
        (mv guard-result nil nil))
       ((unless (equal guard-result (make-erl-val-atom :val 'true))) 
        (eval-clauses args (cdr cs) bind)))
      (mv match-result match-bind (node-clause->body (car cs))))
  ///
    (verify-guards eval-clauses)
    (more-returns
      (v (or (equal (erl-val-kind v) :reject)
             (equal (erl-val-kind v) :none))
         :name val-kind-of-eval-clauses
         :hints 
          (("Subgoal *1/5.3'" 
            :use (:instance val-kind-of-match-args
                    (ps (node-clause->cases (car (erl-clause-list-fix cs))))
                    (vs (erl-vlst-fix args))
                    (bind (bind-fix bind)))
            :in-theory  (disable val-kind-of-match-args))
           ("Subgoal *1/6'''" 
            :use (:instance val-kind-of-match-args
                    (ps (node-clause->cases (car (erl-clause-list-fix cs))))
                    (vs (erl-vlst-fix args))
                    (bind (bind-fix bind)))
            :in-theory  (disable val-kind-of-match-args))))))