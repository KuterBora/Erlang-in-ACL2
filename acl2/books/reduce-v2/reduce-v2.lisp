(in-package "ACL2")
(include-book "wtree")

(set-induction-depth-limit 1)

; PROOF PLAN
; 
; - step 1: show that erl-step with a wtree returns a wtree
; - step 2: find the reqirements for the invariant
; - step 3: show that the invariant holds after running erl-step
; - step 4: for now, consider an erl-runner that terminates
;           -- complete the termination proof
;           -- if it terminates, reduce is satisfied by the invariant.
; - step 6: extend the world, so that reduce workers can use the index to
;           compute/aquire their portion of work. Update the proofs.
;           This is probably all we have time for.
; - step 7: funs instead of +
; - step 8: use skolem functions instead of the termination proof
;           to state that if the scheduler is weakly fair, eventually
;           the call to reduce will return to the master process with
;           the correct value, and the master process can evaluate (cdr klst)

(defrule terminated?-of-emptyp
  (implies (and (network-p net) (omap::emptyp net)) (terminated? net))
  :enable terminated?)

; I need add a constraint to network-p such that klst is erl-klst-p
(skip-proofs
  (defrule unsound-crock
    (implies
      (omap::assoc pid net)
      (erl-klst-p (proc->klst (omap::lookup pid net))))))

; Here I need to show that if a proc in a tree is updated
; without modify its pid and the bindings for Index, ChildPids,
; and Parent, then wtree-p of the new network holds.
; Then - if ACL2 cannot already figure it out - I can have a crock
; lemma for each case of erl-step.  

(skip-proofs (defrule wtree0-p-of-erl-step
  (implies
    (and (network-p net) (wtree0-p net net0 (omap::size net)))
    (wtree0-p (erl-step net) (erl-step net0) (omap::size (erl-step net))))
  :enable (wtree0-p erl-step proc-receive)
  :no-thanks t))

(defrule wtree-p-of-erl-step
  (implies
    (and (network-p net) (wtree-p net))
    (wtree-p (erl-step net)))
  :enable wtree-p)


; TODO maybe I should make wtree-p a fixtype?
; Also, do I need to state that the wtree must have a root?

; The invariant for reduce
(define reduce-inv0 ((net network-p) (net0 network-p))
  :returns (r booleanp)
  :measure (acl2-count (network-fix net))
  (b* ((net (network-fix net))
       (net0 (network-fix net0))
       ((if (omap::emptyp net)) t))
       (and
        ; pick a node
        ; if root
        ;; if terminated -- contains the sum
        ;; if blocked -- there exists a process that has is runnable
        ;;               or has a message for root.
        ;;            -- the next message to be received is not in inbox-tried
        ;;            -- LeftTotal is equal to sum(latest received value)
        ;;            -- CPids is a sublist of ChildPids, starting from
        ;;                latest received index.
        ;; if on receive -- there exists a process that is runnable
        ;;                    or has a message for root,
        ;;                  or, there exists a message in root's inbox-new
        ;;                  that can be received.
        ;;               -- inbox-tried is empty.
        ;;               -- LeftTotal is equal to sum(latest received value)
        ;; if idle, ok
        ;;
        
        ;; if leaf
        ;; if terminated -- either:
        ;;                  has message for parent in its outbox
        ;;                  or parent has its message in one of its inboxes
        ;;                  or parent has already received? How do I tell
        ;;                   that apart? another auxilary variable? or
        ;;                   it might be enough to say that the CPids does not
        ;;                    not contain this worker.
        ;; if blocked -- nil, because workers do not receive.
        ;; if receive -- nil, because workers do not receive.
        ;; if idle -- I am not sure if we need to say that the
        ;;            parent must not have received the message yet,
        ;;            and also does not have it in its inbox.
        (reduce-inv0 (omap::tail net) net0)))
  ///
    (defcong network-equiv equal (reduce-inv0 net net0) 1)
    (defcong network-equiv equal (reduce-inv0 net net0) 2)
    
    (defrule reduce-inv0-of-tail
      (implies (and (network-p net) (network-p net0) (reduce-inv0 net net0))
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
  :enable reduce-inv0)

(defrule inv-of-erl-step
  (implies
    (and (network-p net) (reduce-inv net))
    (reduce-inv (erl-step net)))
  :enable reduce-inv)

; next, show that of the net is terminated,
; the root will have the sum of indices.