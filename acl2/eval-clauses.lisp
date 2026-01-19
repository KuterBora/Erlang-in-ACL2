(in-package "ACL2")
(include-book "eval-match")
(include-book "eval-guards")


; Evaluate Erlang Clauses ------------------------------------------------------

; Returns the body of the first clause which has patterns that can match the 
; given args, and a has guard sequence that is satisfied. If no clauses match, 
; nil is returned, and the caller can decide on the appropiate clause error.
;
;  Returns:
; - Rejections propagated, and the return value 'v' is set to keep track of them. 
;   If there are no rejections, then 'v' is set to :none. Otherwise the returned 
;   'bind' and 'body' are arbitrary. 
; - Bindings are accumulated in 'bind'.
;
(define eval-clauses-when-consp ((args erl-vlst-p) (cls erl-clause-list-p) (bind bind-p))
  :returns (mv (v erl-val-p) (b bind-p) (body expr-list-p))
  :measure (len (erl-clause-list-fix cls))
  (b* ((args (erl-vlst-fix args))
       (cls (erl-clause-list-fix cls))
       (bind (bind-fix bind))
       
       ; No clauses matched -- the caller can return the appropiate clause error.
       ((if (null cls)) (mv (make-erl-val-none) nil nil))

       ; Pick the first clause, get its cases and guards.
       (cases (node-clause->cases (car cls)))
       (guards (node-clause->guards (car cls)))

       ; Obtain the result of evaluating rest of the clauses.
       ; - This will be useful!
       ((mv rv rb rbody) (eval-clauses-when-consp args (cdr cls) bind))
       
       ; Attempt to match cases to args.
       ((mv match-result match-bind) (match-args cases args bind))
       
       ; Propagate rejections.
       ((if (equal (erl-val-kind match-result) :reject)) 
        (mv match-result nil nil))
       
       ; If a case fails to match, try rest of the clauses. 
       ((if (equal (erl-val-kind match-result) :excpt)) (mv rv rb rbody))
       
       ; Evaluate the guard sequence.
       (guard-result (eval-guard-seq guards match-bind))

       ; Propagate rejections.
       ((if (equal (erl-val-kind guard-result) :reject)) 
        (mv guard-result nil nil))
      
       ; If no guard in the sequence was satisfied, try rest of the clause.
       ((unless (equal guard-result (make-erl-val-atom :val 'true))) (mv rv rb rbody))
      
      ; Even if the chosen clause satisfies the cases and guards,
      ; ensure that there will be no rejection in the rest of the clauses.
      ((if (equal (erl-val-kind rv) :reject)) (mv rv rb rbody)))

      ; The chosen clause satisfied the cases and guards, return its body.
      (mv (make-erl-val-none) match-bind (node-clause->body (car cls))))
  ///
    (more-returns
      (v (or (equal (erl-val-kind v) :reject)
             (equal (erl-val-kind v) :none))
         :name val-kind-of-eval-clauses-when-consp
         :hints 
          (("Subgoal *1/5.3'" 
            :use (:instance val-kind-of-match-args
                    (ps (node-clause->cases (car (erl-clause-list-fix cls))))
                    (vs (erl-vlst-fix args))
                    (bind (bind-fix bind)))
            :in-theory  (disable val-kind-of-match-args))
           ("Subgoal *1/6'''" 
            :use (:instance val-kind-of-match-args
                    (ps (node-clause->cases (car (erl-clause-list-fix cls))))
                    (vs (erl-vlst-fix args))
                    (bind (bind-fix bind)))
            :in-theory  (disable val-kind-of-match-args))))))

; This is a wrapper around eval-clauses-when-consp which does not consider the
; case where no clauses are passed to the evaluator initially. If the evaluator 
; runs out of clauses to try, it returns nil, and the caller can decide the
; appropiate exception to throw. However, if, initially, no clauses are given to
; the evaluator, that is a cause for rejection -- Erlang expects at least one
; clause in a clause-list.

(define eval-clauses ((args erl-vlst-p) (cls erl-clause-list-p) (bind bind-p))
  :returns (mv (v erl-val-p) (b bind-p) (body expr-list-p))
  (b* ((args (erl-vlst-fix args))
       (cls (erl-clause-list-fix cls))
       (bind (bind-fix bind))
       ((if (null cls)) 
        (mv (make-erl-val-reject :err "eval-clauses: clause list cannot be empty.") nil nil)))
      (eval-clauses-when-consp args (cdr cls) bind)))