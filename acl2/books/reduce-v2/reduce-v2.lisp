(in-package "ACL2")
(include-book "wtree")

(set-induction-depth-limit 1)




; PROOF PLAN
; 
; - step 1: show that erl-step of a wtree returns a wtree
; - step 2: find the reqirements for the invariant
; - step 3: show that the invariant holds after running erl-step
;
; - step 4: for now, consider an erl-runner that terminates
;           -- complete the termination proof
;           -- if it terminates, reduce is satisfied by the invariant.
; - step 4.5 -- leaves should get GrandTotal
; - step 5 -- barrier instead of termination
; - step 6: extend the world, so that reduce workers can use the index to
;           compute/aquire their portion of work. Update the proofs accordingly.
; =============== This is probably all we have time for. ========================
;
; - step 7: funs instead of +
; - step 8: use skolem functions instead of the termination proof
;           to state that if the scheduler is weakly fair, eventually
;           the call to reduce will return to the master process with
;           the correct value, and the master process can evaluate (cdr klst)



; Here I need to show that if a proc in a tree is updated
; without modifying its pid and the bindings for Index, ChildPids,
; and Parent, then wtree-p of the new network holds.
; Then - if ACL2 cannot already figure it out - I can have a crock
; lemma for each case of erl-step.  

(skip-proofs (defrule wtree0-p-of-erl-step
  (implies
    (and (network-p net) (wtree0-p net net0 (omap::size net)))
    (wtree0-p (erl-step net) (erl-step net0) (omap::size (erl-step net))))
  :enable (wtree0-p erl-step proc-receive)))



(defrule wtree-p-of-erl-step
  (implies
    (and (network-p net) (wtree-p net))
    (wtree-p (erl-step net)))
  :enable wtree-p)

; TODO maybe I should make wtree-p a fixtype?
; Also, do I need to state that the wtree must have a root?

; First TODO: maybe I should combine inbox new and inbox tried???
; How will fuel work???

(define inv ((pid pid-p) (net network-p))
  :ignore-ok t
  :returns (r booleanp)
  (b* ((pid (pid-fix pid))
       (net (network-fix net))
       ((unless (omap::assoc pid net)) nil)
       (proc (omap::lookup pid net))
       ((unless (leaf-p proc)) t)
       (ps (proc->ps proc))
       (bind (erl-state->bind (proc->s ps)))
       (parent (omap::lookup 'Parent bind))
       (children (omap::lookup 'Children bind))
       (index (omap::lookup 'Index bind)))
      (case ps
        (:idle
          ; equal proc (make-reduce-proc ...)
          )
        (:terminated
          ; /\ equal s->in f(i, j) or i
          ; /\ if leaf
          ;    \/
          ;     /\ outbox = empty
          ;     /\ parent:
          ;         \/ message in parent inbox
          ;         \/ parent already received
          ;   \/ message in outbox
          ; /\ if root, empty outbox
          ; /\ message contains f(i, j), sent to parent
          ; /\ maybe the children have terminated?     
          ) 
        (:blocked
          ; /\ equal s->in :receive of next CPid
          ; /\
          ;    /\ s->bind Cpids correct regards to receive in s
          ;    /\ s->LeftTotal contains f(i, (index (car CPid)))
          ; /\ outbox is empty?
          ; /\
          ;   /\ inbox does not contain message from (car CPid).
          ;   /\ all messages in inbox contain the correct values.
          )
        (:receive
          ; /\ equal s->in :receive of next CPid
          ; /\
          ;    /\ s->bind Cpids correct regards to receive in s
          ;    /\ s->LeftTotal contains f(i, (index (car CPid)))
          ; /\ outbox is empty?
          ; /\ all messages in inbox contain the correct values.
          ; /\ next message to receive is not in inbox tried?
          ))))


; The invariant for reduce
(define reduce-inv0 ((net network-p) (net0 network-p))
  :returns (r booleanp)
  :measure (acl2-count (network-fix net))
  (b* ((net (network-fix net))
       (net0 (network-fix net0))
       ((if (omap::emptyp net)) t)
       (pid (omap::head-key net))
       (proc (omap::head-val net)))
      (and
        (cond
          ((root-p proc) (and (root-inv pid net)))
          ((leaf-p proc) (and (leaf-inv pid net)))
          (t nil))
        (reduce-inv0 (omap::tail net) net0)))
  ///
    (defcong network-equiv equal (reduce-inv0 net net0) 1)
    (defcong network-equiv equal (reduce-inv0 net net0) 2)
    
    (defrule reduce-inv0-of-tail
      (implies
        (and (network-p net) (network-p net0)
             (reduce-inv0 net net0))
        (reduce-inv0 (omap::tail net) net0))))

(define reduce-inv ((net network-p))
  :enabled t
  (b* ((net (network-fix net))
       ((unless (wtree-p net)) nil))
      (reduce-inv0 net net))
  ///
    (defcong network-equiv equal (reduce-inv net) 1))

(defrule inv0-of-erl-step
  (implies
    (and (network-p net) (network-p net0) (reduce-inv0 net net0))
    (reduce-inv0 (erl-step net) (erl-step net0)))
  :enable (root-inv leaf-inv reduce-inv0 erl-step proc-receive)
  :expand (reduce-inv0 (erl-step net) (erl-step net0)))

(defrule inv-of-erl-step
  (implies
    (and (network-p net) (reduce-inv net))
    (reduce-inv (erl-step net)))
  :enable reduce-inv)



; next, show that if the net is terminated,
; the root will have the sum of indices.