(in-package "ACL2")
(include-book "../wtree/wtree-theorems")
(include-book "util")
(include-book "inv-helpers")


; Invariant for Reduce Correctness --------------------------------------------

(define inv ((pid pid-p) (net network-p))
  :ignore-ok t
  :returns (r booleanp)
  :guard-hints
    (("Goal"
      :in-theory (enable omap::from-lists wtree-nodes-are-leaf-or-root)
      :use (:instance wtree-nodes-are-leaf-or-root
            (net net)
            (pid
              (omap::lookup 'childhd
                (erl-state->bind (proc->s (omap::lookup pid net))))))))
  (b* ((pid (pid-fix pid))
       (net (network-fix net))
       ((unless (wtree-p net)) nil)
       ((unless (omap::assoc pid net)) nil)
       (proc (omap::lookup pid net))
       ; Every process in the network must have a well-formed continuation
       ((unless (erl-klst-p (proc->klst proc))) nil)
       ((unless (or (leaf-p proc) (root-p proc))) t)
       (ps (proc->ps proc))
       (bind (erl-state->bind (proc->s proc)))
       (parent (omap::lookup 'Parent bind))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids bind)))
       (index (erl-val-integer->val (omap::lookup 'Index bind))))
      (case ps
        (:idle
          ; If the process has not been run yet, it is has not changed
          ; at all since it was spawned. However, it might have received
          ; messages.
          ; - init-proc simulates a proc that has just been spawned,
          ;   having received no messages.
          (b* ((init-proc (make-reduce-proc pid parent children index))
               ((unless (equal (proc->s proc) (proc->s init-proc))) nil)
               ((unless (equal (proc->klst proc) (proc->klst init-proc))) nil)
               ((unless (null (proc->inbox-tried proc))) nil)
               ; nothing has been sent, so the parent has not received anything.
               ((unless (parent-still-waiting-p pid parent net)) nil)
               (inbox (proc->inbox-new proc)))
              (received-messages-wf inbox children net)))
        (:terminated
          (b* ((val (erl-state->in (proc->s proc)))
               ((unless (equal (erl-val-kind val) :integer)) nil)
               (val (erl-val-integer->val val))
               ; If the node has no children, it simply sends its index.
               ((if (null children))
                (and (equal val index)
                     (sent-message-wf proc (proc->outbox proc) parent net)))
               (cpid (rightmost-child pid net))
               
               ; TODO: this can be derived from wtree-p
               ((unless (omap::assoc cpid net)) nil)
               ((unless (leaf-p (omap::lookup cpid net))) nil)

               (cproc (omap::lookup cpid net))
               (cbind (erl-state->bind (proc->s cproc)))
               (cindex (erl-val-integer->val (omap::lookup 'Index cbind)))
               ((unless (<= index cindex)) nil))
              (and
                ; the value must be the sum of indices of this branch.
                (equal val (sum-range index cindex))
                ; message sent must be well formed, if any
                (sent-message-wf proc (proc->outbox proc) parent net)
                ; all messages have been received already   
                (null (proc->inbox-tried proc))
                (null (proc->inbox-new proc)))))
        (:blocked
          (b* (; if the node has no children, then it should not have blocked.
               ((if (null children)) nil)

               ; nothing has been sent yet, a node sends only when it
               ; terminates, so the parent the parent has not received.
               ((unless (parent-still-waiting-p pid parent net)) nil)

               ; during receive the latest value is wiped.
               (val (erl-state->in (proc->s proc)))
               ((unless (equal (erl-val-kind val) :none)) nil)

               ; Ensure the existance of bindings created during the reduce call.
               ((unless (omap::assoc 'ParentPid bind)) nil)
               ((unless (omap::assoc 'CPids bind)) nil)
               ((unless (omap::assoc 'ChildHd bind)) nil)
               ((unless (omap::assoc 'ChildTl bind)) nil)
               ((unless (omap::assoc 'LeftTotal bind)) nil)
               
               ; Parent never changes.
               ((unless (equal parent (omap::lookup 'ParentPid bind))) nil)
               
               ; the childpids are a non-empty list
               (cps (omap::lookup 'CPids bind))
               ((unless (equal (erl-val-kind Cps) :cons)) nil)
               (cps (erl-val-cons->lst cps))
               ((unless cps) nil)
               ; The remaining children are a postfix of the original children.
               ; TODO: I might need a better representation for this.
               ((unless (prefixp (rev cps) (rev children))))
               
               ; ChildHead and ChildTail are bound correctly.
               (chd (omap::lookup 'ChildHd bind))
               ((unless (equal chd (car cps))) nil)
               (ctl (omap::lookup 'ChildTl bind))
               ((unless (equal (erl-val-kind ctl) :cons)) nil)
               (ctl (erl-val-cons->lst ctl))
               ((unless (equal ctl (cdr cps))) nil)
              
               ; TODO: This follows from wtree-p
               ((unless (omap::assoc chd net)) nil)

               ; Acquire the index of the ChildHead
               ; we should know from the prefix that chd is a valid pid.
               (chdproc (omap::lookup chd net))
               
               ; TODO: This follows from wtree-p
               ((unless (proc-p chdproc)) nil)
               ((unless (leaf-p chdproc)) nil)

               (chdbind (erl-state->bind (proc->s chdproc)))
               (cindex (erl-val-integer->val (omap::lookup 'Index chdbind)))
               ((unless (< index cindex)) nil)

               ; LeftTotal
               ((unless (equal (erl-val-kind (omap::lookup 'LeftTotal bind)) :integer)) nil)
               (lt (erl-val-integer->val (omap::lookup 'LeftTotal bind)))
               ((unless (equal lt (sum-range index (1- cindex)))) nil)

               ; The outbox must be empty, as the process will only send a
               ; message when it is done computing the sum.
               ((unless (null (proc->outbox proc))) nil)
               ; ??? The parent, if any, must not have received the message yet.
               ; However, this could be a property of the parent.

               ; The world and module do not change
               ((unless (equal (erl-state->world (proc->s proc)) (sum-reduce-w))) nil)
               ((unless (equal (erl-state->module (proc->s proc)) 'local)) nil)

               ; Inbox-new is empty, else the process would be unblocked
               ((unless (null (proc->inbox-new proc))) nil)

               ; Inbox-tried does not contain chd, otherwise the process would
               ; have continued.
               (inbox (proc->inbox-tried proc))
               ((unless (received-messages-wf inbox cps net)) nil)
               ((if (inbox-contains inbox chd)) nil)

               ; ???: For messages not have yet received;
               ; the sender is either
               ; - not terminated
               ; - or has the message in the outbox

               ; Klst is correct
               (klst (proc->klst proc))
               (rbind
                (omap::from-lists
                  (list 'ChildPids 'Parent 'Index)
                  (list (make-erl-val-cons :lst children)
                        parent
                        (make-erl-val-integer :val index))))
               ((unless (reduce-receive-klst-p klst rbind)) nil))
             ; Deadlock freedom is deliberately not claimed here.  It is a
             ; property of the whole network, and a node that blocks may itself
             ; have been the last runnable one, so carrying it per node would
             ; make every step re-establish it -- and re-establishing it at a
             ; block means descending the ChildHd chain looking for a witness.
             ; It belongs in its own theorem over inv-all.
             t))
        (:receive
          (b* (; if the node has no children, then it should not try to receive.
               ((if (null children)) nil)

               ; nothing has been sent yet -- a node sends only when it
               ; terminates -- so the parent is still waiting for it
               ((unless (parent-still-waiting-p pid parent net)) nil)

               ; during receive the latest value is wiped.
               (val (erl-state->in (proc->s proc)))
               ((unless (equal (erl-val-kind val) :none)) nil)

               ; Ensure the existance of bindings created during the reduce call.
               ((unless (omap::assoc 'ParentPid bind)) nil)
               ((unless (omap::assoc 'CPids bind)) nil)
               ((unless (omap::assoc 'ChildHd bind)) nil)
               ((unless (omap::assoc 'ChildTl bind)) nil)
               ((unless (omap::assoc 'LeftTotal bind)) nil)
               
               ; Parent never changes.
               ((unless (equal parent (omap::lookup 'ParentPid bind))) nil)
               
               ; the childpids are a non-empty list
               (cps (omap::lookup 'CPids bind))
               ((unless (equal (erl-val-kind Cps) :cons)) nil)
               (cps (erl-val-cons->lst cps))
               ((unless cps) nil)
               ; TODO: I might need a better representation for this:
               ; The remaining children are a postfix of the original children.
               ; sublist might be sufficient.
               ((unless (prefixp (rev cps) (rev children))))
               
               ; ChildHead and ChildTail are bound correctly.
               (chd (omap::lookup 'ChildHd bind))
               ((unless (equal chd (car cps))) nil)
               (ctl (omap::lookup 'ChildTl bind))
               ((unless (equal (erl-val-kind ctl) :cons)) nil)
               (ctl (erl-val-cons->lst ctl))
               ((unless (equal ctl (cdr cps))) nil)

               ; TODO: this follows from wtree-p
               ((unless (omap::assoc chd net)) nil)

               ; Acquire the index of the ChildHead
               ; we should know from the preix that chd is a valid pid.
               (chdproc (omap::lookup chd net))

               ; TODO: this follows from wtree-p
               ((unless (proc-p chdproc)) nil)
               ((unless (leaf-p chdproc)) nil)

               (chdbind (erl-state->bind (proc->s chdproc)))
               (cindex (erl-val-integer->val (omap::lookup 'Index chdbind)))
               ; The other index ordering: the node sits strictly below the
               ; child it is waiting on.  The leftmost child starts at index+1,
               ; and each later child starts one past the previous child's
               ; rightmost descendant, which the :terminated arm bounds below
               ; by that child's index.
               ((unless (< index cindex)) nil)

               ; LeftTotal
               ((unless (equal (erl-val-kind (omap::lookup 'LeftTotal bind)) :integer)) nil)
               (lt (erl-val-integer->val (omap::lookup 'LeftTotal bind)))
               ((unless (equal lt (sum-range index (1- cindex)))) nil)

               ; The outbox must be empty, since the process will only send a
               ; message when it is done computing the sum.
               ((unless (null (proc->outbox proc))) nil)

               ; The world and module do not change
               ((unless (equal (erl-state->world (proc->s proc))
                               (sum-reduce-w))) nil)
               ((unless (equal (erl-state->module (proc->s proc)) 'local)) nil)

               ; Inbox-tried is empty, because the process has not started
               ; attempting to receive yet.
               ((unless (null (proc->inbox-tried proc))) nil)

               ; Inbox-new contains valid messages.
               (inbox (proc->inbox-new proc))
               ((unless (received-messages-wf inbox cps net)) nil)

               ; Klst is correct
               (klst (proc->klst proc))
               (rbind
                (omap::from-lists
                  (list 'ChildPids 'Parent 'Index)
                  (list (make-erl-val-cons :lst children)
                        parent
                        (make-erl-val-integer :val index))))
               ((unless (reduce-receive-klst-p klst rbind)) nil))
            t))))
  ///
    (defcong pid-equiv equal (inv pid net) 1)
    (defcong network-equiv equal (inv pid net) 2))


; The invariant should hold for every pid in the network. 
(define inv-all0 ((net network-p) (net0 network-p))
  :returns (r booleanp)
  :measure (acl2-count (network-fix net))
  (b* ((net (network-fix net))
       (net0 (network-fix net0))
       ((if (omap::emptyp net)) t))
      (and (inv (omap::head-key net) net0)
           (inv-all0 (omap::tail net) net0)))
  ///
    (defcong network-equiv equal (inv-all0 net net0) 1)
    (defcong network-equiv equal (inv-all0 net net0) 2)

    (defrule inv-of-inv-all0
      (implies
        (and (network-p net) (pid-p pid)
             (inv-all0 net net0) (omap::assoc pid net))
        (inv pid net0))
      :enable omap::lookup))

(define inv-all ((net network-p))
  :returns (r booleanp)
  (b* ((net (network-fix net)))
      (inv-all0 net net))
  ///
    (defcong network-equiv equal (inv-all net) 1)

    (defrule inv-of-inv-all
      (implies
        (and (network-p net) (pid-p pid)
             (inv-all net) (omap::assoc pid net))
        (inv pid net))))
