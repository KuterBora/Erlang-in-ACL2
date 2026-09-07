; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

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
      :in-theory (enable omap::from-lists wtree-nodes-are-leaf-or-root
                         reduce-receive-klst-p)
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
       (wbind (wtree-bind proc))
       (parent (omap::lookup 'Parent wbind))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (index (erl-val-integer->val (omap::lookup 'Index wbind))))
      (case ps
        (:idle
          ; If the process has not been run yet, it is has not changed
          ; at all since it was spawned. However, it might have received
          ; messages.
          ; - init-proc simulates a proc that has just been spawned,
          ;   having received no messages.
          (b* (; The process has not entered the reduce call, so the
               ; there should be no new bindings yet.
               ((unless (equal bind wbind)) nil)
               (init-proc (make-reduce-proc pid parent children index))
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
               (cbind (wtree-bind cproc))
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
               ; terminates, so the parent must not have received.
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

               ; RightTotal should not be bound. This ends up being
               ; a road block otherwise.
               ((if (omap::assoc 'RightTotal bind)) nil)
               
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

               (chdbind (wtree-bind chdproc))
               (cindex (erl-val-integer->val (omap::lookup 'Index chdbind)))
               ((unless (< index cindex)) nil)

               ; LeftTotal
               ((unless (equal (erl-val-kind (omap::lookup 'LeftTotal bind)) :integer)) nil)
               (lt (erl-val-integer->val (omap::lookup 'LeftTotal bind)))
               ((unless (equal lt (sum-range index (1- cindex)))) nil)

               ; The outbox must be empty, as the process will only send a
               ; message when it is done computing the sum.
               ((unless (null (proc->outbox proc))) nil)
               ; The parent, if any, must not have received the message yet.
               ; However, this could be a property of the parent.

               ; The world and module do not change
               ((unless (equal (erl-state->world (proc->s proc))
                               (sum-reduce-w))) nil)
               ((unless (equal (erl-state->module (proc->s proc)) 'local)) nil)

               ; Inbox-new is empty, else the process would be unblocked
               ((unless (null (proc->inbox-new proc))) nil)

               ; Inbox-tried does not contain chd, otherwise the process would
               ; have continued.
               (inbox (proc->inbox-tried proc))
               ((unless (received-messages-wf inbox cps net)) nil)
               ((if (inbox-contains inbox chd)) nil)

               ; For messages not have yet received;
               ; the sender is either
               ; - not terminated
               ; - or has the message in the outbox
               ; Though I check this on the sender side.
 
               ; Klst is correct
               (klst (proc->klst proc))
               ; TODO: passing rbind may have become unnecessary,
               ;  since the definition of wtree has changed. It does
               ;  not seem to hurt for now.
               (rbind
                (omap::from-lists
                  (list 'ChildPids 'Parent 'Index)
                  (list (make-erl-val-cons :lst children)
                        parent
                        (make-erl-val-integer :val index))))
               ((unless (reduce-receive-klst-p klst rbind)) nil)
               
               ; There must be enough fuel. calls to apply-k use 6 fuel.
               ; Meanwhile, I picked 100 as a minumum because I can.
               ((unless (> (erl-k->fuel (car klst))
                           (+ 100 (* 6 (len cps))))) nil))
             t))
        (:receive
          (b* (; if the node has no children, then it should not try to receive.
               ((if (null children)) nil)

               ; nothing has been sent yet, a node sends only when it
               ; terminates, so the parent must not have received.
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

               ; RightTotal should not be bound. This ends up being
               ; a road block otherwise.
               ((if (omap::assoc 'RightTotal bind)) nil)
               
               ; Parent never changes.
               ((unless (equal parent (omap::lookup 'ParentPid bind))) nil)
               
               ; the childpids are a non-empty list
               (cps (omap::lookup 'CPids bind))
               ((unless (equal (erl-val-kind Cps) :cons)) nil)
               (cps (erl-val-cons->lst cps))
               ((unless cps) nil)
               ; TODO: I might need a better representation for this:
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

               (chdbind (wtree-bind chdproc))
               (cindex (erl-val-integer->val (omap::lookup 'Index chdbind)))
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
               ; TODO: passing rbind may have become unnecessary,
               ;  since the definition of wtree has changed. It does
               ;  not seem to hurt for now.
               (rbind
                (omap::from-lists
                  (list 'ChildPids 'Parent 'Index)
                  (list (make-erl-val-cons :lst children)
                        parent
                        (make-erl-val-integer :val index))))
               ((unless (reduce-receive-klst-p klst rbind)) nil)

               ; There must be enough fuel. calls to apply-k use 6 fuel.
               ; Meanwhile, I picked 100 as a minumum because I can.
               ((unless (> (erl-k->fuel (car klst))
                           (+ 100 (* 6 (len cps))))) nil))
            t))))
  ///
    (defcong pid-equiv equal (inv pid net) 1)
    (defcong network-equiv equal (inv pid net) 2)
    
    (defrule wtree-p-of-inv
      (implies (inv pid net) (wtree-p net)))
    
    (defrule integer-value-of-inv-terminated
      (implies
        (and
          (network-p net) (pid-p pid)
          (or (leaf-p (omap::lookup pid net))
              (root-p (omap::lookup pid net)))
          (equal (proc->ps (omap::lookup pid net)) :terminated)
          (inv pid net))
        (equal
          (erl-val-kind
            (erl-state->in (proc->s (omap::lookup pid net))))
          :integer)))

    (defrule parent-still-waiting-p-of-inv
      (implies
        (and
          (network-p net) (pid-p pid)
          (or (leaf-p (omap::lookup pid net))
              (root-p (omap::lookup pid net)))
          (not (equal (proc->ps (omap::lookup pid net)) :terminated))
          (inv pid net))
        (parent-still-waiting-p pid
          (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
          net))))


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
        (and (network-p net) (omap::assoc pid net)
             (inv-all0 net net0))
        (inv pid net0))))

(define inv-all ((net network-p))
  :returns (r booleanp)
  (b* ((net (network-fix net)))
      (inv-all0 net net))
  ///
    (defcong network-equiv equal (inv-all net) 1)

    (defrule inv-of-inv-all
      (implies
        (and (network-p net) (omap::assoc pid net)
             (inv-all net))
        (inv pid net))))

; Theorems -----------------------------------------------------------------------

; Facts when a worker has a message in its outbox.
; TODO: this one is expensive.
(defruled sender-with-message-props
  (implies
    (and
      (network-p net) (wtree-p net) (inv src net)
      (pid-p src) (omap::assoc src net)
      (omap::assoc dst (proc->outbox (omap::lookup src net)))
      (omap::lookup dst (proc->outbox (omap::lookup src net))))
    (and
      (equal (proc->ps (omap::lookup src net)) :terminated)
      (not (equal src dst))
      (equal (omap::lookup 'Parent
                (wtree-bind (omap::lookup src net))) dst)
      (omap::assoc dst net)
      (not (equal (proc->ps (omap::lookup dst net)) :terminated))
      (omap::emptyp (omap::tail (proc->outbox (omap::lookup src net))))        
      (not (cdr (omap::lookup dst (proc->outbox (omap::lookup src net)))))
      (equal
        (erl-val-kind
          (car (omap::lookup dst (proc->outbox (omap::lookup src net)))))
          :tuple)
      (equal
        (len (erl-val-tuple->lst
              (car (omap::lookup dst
                      (proc->outbox (omap::lookup src net))))))
        2)
      (equal
        (car (erl-val-tuple->lst
                (car (omap::lookup dst
                        (proc->outbox (omap::lookup src net))))))
        src)
      (equal
        (cadr (erl-val-tuple->lst
          (car (omap::lookup dst
                (proc->outbox (omap::lookup src net))))))
        (erl-state->in (proc->s (omap::lookup src net))))
      (or
        (not
          (and (omap::assoc 'CPids
                 (erl-state->bind (proc->s (omap::lookup dst net))))
               (equal (erl-val-kind
                        (omap::lookup 'CPids
                          (erl-state->bind (proc->s (omap::lookup dst net)))))
                      :cons)))
        (member-equal src
          (erl-val-cons->lst
            (omap::lookup 'CPids
              (erl-state->bind (proc->s (omap::lookup dst net)))))))))
  :expand ((inv src net))
  :enable (sent-message-wf proc->outbox make-reduce-proc)
  :disable
    ((:type-prescription omap::lookup-when-emptyp) last assoc-of-runnable?
     (:type-prescription omap::tail-when-emptyp) omap::lookup-when-emptyp
     (:type-prescription omap::head-key-when-emptyp) received-messages-wf-fields
     omap::assoc-when-assoc-tail integer-value-of-inv-terminated wtree0-of-zero
     wtree-bind-when-no-function-return omap::assoc-when-assoc-of-tail-cheap)
  :use ((:instance wtree-nodes-are-leaf-or-root (pid src))
        (:instance omap::assoc-of-tail-when-not-head
          (key dst) (map (proc->outbox (omap::lookup src net))))
        (:instance omap::assoc-of-tail-when-not-head
          (key (omap::lookup 'Parent (wtree-bind (omap::lookup src net))))
          (map (proc->outbox (omap::lookup src net))))))


; received-messages-wf -----------------------------------------------------------

(defrule received-messages-wf-of-update
  (implies
    (and
      (network-p net) (omap::assoc p net)
      ; This is the deliver step, so procs cannot terminate.
      (or (equal (proc->ps proc) (proc->ps (omap::lookup p net)))
          (and (not (equal (proc->ps proc) :terminated))
               (not (equal (proc->ps (omap::lookup p net))
                    :terminated))))
      (equal (erl-state->in (proc->s proc))
             (erl-state->in (proc->s (omap::lookup p net))))
      (or (not (outbox-emptyp (proc->outbox (omap::lookup p net))))
          (outbox-emptyp (proc->outbox proc)))
      (network-p (omap::update p proc net))
      (received-messages-wf inbox cpids net))
    (received-messages-wf inbox cpids (omap::update p proc net)))
  :enable (received-messages-wf omap::lookup-of-update))

(defrule received-messages-wf-of-append-message
  (implies
    (and
      (network-p net) (omap::assoc sender net)
      (erl-vlst-p inbox) (erl-vlst-p cpids)
      (member-equal sender cpids)
      (not (inbox-contains inbox sender))
      (equal (proc->ps (omap::lookup sender net)) :terminated)
      (outbox-emptyp (proc->outbox (omap::lookup sender net)))
      (equal
        (erl-val-kind
          (erl-state->in (proc->s (omap::lookup sender net))))
        :integer)
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (car (erl-val-tuple->lst m)) sender)
      (equal (cadr (erl-val-tuple->lst m))
             (erl-state->in (proc->s (omap::lookup sender net))))
      (received-messages-wf inbox cpids net))
    (received-messages-wf (append inbox (list m)) cpids net))
  :enable (received-messages-wf inbox-contains)
  :induct (received-messages-wf inbox cpids net))

(defrule received-messages-wf-of-inbox-without-car
  (implies
    (and
      (network-p net) (erl-vlst-p cpids)
      (consp cpids) (pid-p (car cpids))
      (received-messages-wf inbox cpids net))
    (received-messages-wf
      (inbox-without inbox (car cpids)) (cdr cpids) net))
  :use
    ((:instance received-messages-wf-of-inbox-without (pid (car cpids)))
     (:instance received-messages-wf-monotone
      (inbox (inbox-without inbox (car cpids)))
      (cpids1 (remove-equal (car cpids) cpids))
      (cpids2 (cdr cpids))))
  :disable (received-messages-wf-of-inbox-without)
  :prep-lemmas
  ((defruled received-messages-wf-monotone
     (implies
       (and (network-p net) (erl-vlst-p inbox)
            (erl-vlst-p cpids1) (erl-vlst-p cpids2)
            (subsetp-equal cpids1 cpids2)
            (received-messages-wf inbox cpids1 net))
       (received-messages-wf inbox cpids2 net))
     :enable received-messages-wf)))

; sent-message-wf ----------------------------------------------------------------

(defrule sent-message-wf-of-update
  (implies
    (and
      (network-p net)
      (omap::assoc p net)
      (network-p (omap::update p proc net))
      (equal (erl-state->bind (proc->s proc))
             (erl-state->bind (proc->s (omap::lookup p net))))
      (erl-vlst-p msgs)
      (or
        ; process was already on receive (or in idle).
        (and (equal (proc->ps proc) (proc->ps (omap::lookup p net)))
             (equal (proc->inbox-tried proc)
                    (proc->inbox-tried (omap::lookup p net)))
             (equal (proc->inbox-new proc)
                    (append (proc->inbox-new (omap::lookup p net)) msgs)))
        ; process was unblocked after the delivery.
        (and (equal (proc->ps (omap::lookup p net)) :blocked)
              (equal (proc->ps proc) :receive)
              (null (proc->inbox-tried proc))
              (equal (proc->inbox-new proc)
                    (append (proc->inbox-tried (omap::lookup p net))
                            (proc->inbox-new (omap::lookup p net))
                            msgs))))
      (sent-message-wf self outbox parent net))
    (sent-message-wf self outbox parent (omap::update p proc net)))
  :enable (sent-message-wf omap::lookup-of-update)
  :disable
    (erl-val-fix-when-erl-val-p erl-val-p-when-erl-fun-p-rewrite
     erl-val-when-erl-fun omap::assoc-when-assoc-tail binary-append
     append-when-not-consp not-inbox-contains-of-received-messages-wf))

; BOZO: yes, this is very verbose, but it covers all the cases.
; TODO: comments
(defrule sent-message-wf-of-update-of-run
  (implies
    (and
      (network-p net) (network-p (omap::update p proc net))
      (proc-p proc) (omap::assoc p net)
      (not (equal (proc->ps proc) :idle))
      (proc-p self) (erl-val-p parent)
      (or
        (not (and (equal parent p)
                  (omap::assoc parent (outbox-fix outbox))
                  (omap::lookup parent (outbox-fix outbox))))
        (and
          (not (equal (proc->ps proc) :terminated))
          (or
            (not (and (omap::assoc 'CPids (erl-state->bind (proc->s proc)))
                      (equal (erl-val-kind
                              (omap::lookup 'CPids
                                (erl-state->bind (proc->s proc))))
                            :cons)))
            (member-equal (proc->pid self)
              (erl-val-cons->lst
                (omap::lookup 'CPids
                  (erl-state->bind (proc->s proc))))))))
      (or
        (not (equal parent p))
        (or (equal (proc->ps proc) :terminated)
            (inbox-contains (proc->inbox-new proc) (proc->pid self))
            (and (equal (proc->ps proc) :blocked)
                 (inbox-contains (proc->inbox-tried proc)
                                 (proc->pid self)))
            (and (omap::assoc 'CPids (erl-state->bind (proc->s proc)))
                 (equal (erl-val-kind
                          (omap::lookup 'CPids
                            (erl-state->bind (proc->s proc))))
                        :cons)
                 (not (member-equal (proc->pid self)
                        (erl-val-cons->lst
                          (omap::lookup 'CPids
                            (erl-state->bind (proc->s proc)))))))))
      (sent-message-wf self outbox parent net))
    (sent-message-wf self outbox parent (omap::update p proc net)))
  :enable (sent-message-wf omap::lookup-of-update)
  :disable sent-message-wf-of-update)

; sent-message-wf after a node termiates
(defruled sent-message-wf-of-terminating-node
  (implies
    (and
      (network-p net) (pid-p p) (proc-p proc)
      (network-p (omap::update p proc net))
      (omap::assoc p net)
      (equal (erl-state->self (proc->s proc)) p)
      (erl-val-p (omap::lookup 'Parent (wtree-bind proc)))
      (not (equal (omap::lookup 'Parent (wtree-bind proc)) p))
      (parent-still-waiting-p p
        (omap::lookup 'Parent (wtree-bind proc)) net)
      (equal (erl-val-kind (erl-state->in (proc->s proc))) :integer)
      (equal
        (proc->outbox proc)
        (if (pid-p (omap::lookup 'Parent (wtree-bind proc)))
            (omap::update (omap::lookup 'Parent (wtree-bind proc))
              (list (make-erl-val-tuple
                      :lst (list p (erl-state->in (proc->s proc)))))
              nil)
            nil)))
     (sent-message-wf proc
      (proc->outbox proc)
      (omap::lookup 'Parent (wtree-bind proc))
      (omap::update p proc net)))
  :enable
    (sent-message-wf proc->pid parent-still-waiting-p))

(defruled sent-message-wf-when-inv-terminated
  (implies
    (and
      (network-p net) (pid-p pid) (inv pid net)
      (equal (proc->ps (omap::lookup pid net)) :terminated)
      (or (leaf-p (omap::lookup pid net))
          (root-p (omap::lookup pid net))))
    (sent-message-wf (omap::lookup pid net)
      (proc->outbox (omap::lookup pid net))
      (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
      net))
  :enable inv)

; sent-message-wf after receive -> blocked
(defruled sent-message-wf-of-update-of-receive-to-blocked
  (implies
    (and
      (network-p net) (omap::assoc pid net) (omap::assoc p net)
      (network-p (omap::update p proc net))
      (proc-p proc) (not (equal pid p))      
      (erl-val-p (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))))
      (equal (proc->ps (omap::lookup p net)) :receive)
      (equal (proc->ps proc) :blocked)
      (null (proc->inbox-new proc))
      (equal (proc->inbox-tried proc)
             (proc->inbox-new (omap::lookup p net)))
      (equal (omap::lookup 'CPids (erl-state->bind (proc->s proc)))
             (omap::lookup 'CPids
               (erl-state->bind (proc->s (omap::lookup p net)))))
      (iff (omap::assoc 'CPids (erl-state->bind (proc->s proc)))
           (omap::assoc 'CPids
             (erl-state->bind (proc->s (omap::lookup p net)))))
      (sent-message-wf (omap::lookup pid net)
        (proc->outbox (omap::lookup pid net))
        (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
        net))
    (sent-message-wf (omap::lookup pid net)
      (proc->outbox (omap::lookup pid net))
      (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
      (omap::update p proc net)))
  :cases ((equal (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))) p))
  :enable (sent-message-wf proc->pid))

; receive -> receive
(defruled sent-message-wf-of-update-of-receive-match
  (implies
    (and
      (network-p net)
      (omap::assoc pid net) (omap::assoc p net)
      (proc-p proc) (not (equal pid p))
      (network-p (omap::update p proc net))
      (erl-val-p (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))))
      (equal (proc->ps (omap::lookup p net)) :receive)
      (pid-p (car (erl-val-cons->lst (omap::lookup 'CPids
                    (erl-state->bind (proc->s (omap::lookup p net)))))))
      (outbox-emptyp
        (proc->outbox
          (omap::lookup
            (car (erl-val-cons->lst (omap::lookup 'CPids
                   (erl-state->bind (proc->s (omap::lookup p net))))))
            net)))
      (omap::assoc 'CPids (erl-state->bind (proc->s (omap::lookup p net))))
      (equal (erl-val-kind
               (omap::lookup 'CPids
                 (erl-state->bind (proc->s (omap::lookup p net)))))
             :cons)
      (equal (proc->ps proc) :receive)
      (null (proc->inbox-tried proc))
      (equal (proc->inbox-new proc)
             (inbox-without (proc->inbox-new (omap::lookup p net))
               (car (erl-val-cons->lst (omap::lookup 'CPids
                      (erl-state->bind (proc->s (omap::lookup p net))))))))
      (omap::assoc 'CPids (erl-state->bind (proc->s proc)))
      (equal (erl-val-kind
               (omap::lookup 'CPids (erl-state->bind (proc->s proc))))
             :cons)
      (equal (erl-val-cons->lst
               (omap::lookup 'CPids (erl-state->bind (proc->s proc))))
             (cdr (erl-val-cons->lst (omap::lookup 'CPids
                    (erl-state->bind (proc->s (omap::lookup p net)))))))
      ; ChildHd is listed once, so dropping it really does consume it
      (not (member-equal
             (car (erl-val-cons->lst (omap::lookup 'CPids
                    (erl-state->bind (proc->s (omap::lookup p net))))))
             (cdr (erl-val-cons->lst (omap::lookup 'CPids
                    (erl-state->bind (proc->s (omap::lookup p net))))))))
      (sent-message-wf (omap::lookup pid net)
        (proc->outbox (omap::lookup pid net))
        (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
        net))
    (sent-message-wf (omap::lookup pid net)
      (proc->outbox (omap::lookup pid net))
      (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
      (omap::update p proc net)))
  :cases ((equal (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))) p))
  :enable (sent-message-wf proc->pid sent-message-wf-of-update-of-run)
  :prep-lemmas
    ((defrule car-not-member-implies-neq
       (implies (and (member-equal x (cdr l))
                     (not (member-equal (car l) (cdr l))))
                (not (equal x (car l)))))))

(defruled sent-message-wf-of-update-of-receive->terminated
  (implies
    (and
      (network-p net) (network-p (omap::update p proc net))
      (proc-p proc) (not (equal pid p))
      (omap::assoc pid net) (omap::assoc p net)
      (erl-val-p (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))))
      (equal (proc->ps (omap::lookup p net)) :receive)
      (omap::assoc 'CPids (erl-state->bind (proc->s (omap::lookup p net))))
      (equal (erl-val-kind
               (omap::lookup 'CPids
                 (erl-state->bind (proc->s (omap::lookup p net)))))
             :cons)
      (null (cdr (erl-val-cons->lst (omap::lookup 'CPids
                   (erl-state->bind (proc->s (omap::lookup p net)))))))
      (pid-p (car (erl-val-cons->lst (omap::lookup 'CPids
                    (erl-state->bind (proc->s (omap::lookup p net)))))))
      (outbox-emptyp
        (proc->outbox
          (omap::lookup
            (car (erl-val-cons->lst (omap::lookup 'CPids
                   (erl-state->bind (proc->s (omap::lookup p net))))))
            net)))
      (equal (proc->ps proc) :terminated)
      (sent-message-wf (omap::lookup pid net)
        (proc->outbox (omap::lookup pid net))
        (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
        net))
    (sent-message-wf (omap::lookup pid net)
      (proc->outbox (omap::lookup pid net))
      (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
      (omap::update p proc net)))

  :cases ((equal (omap::lookup 'Parent
                    (wtree-bind (omap::lookup pid net))) p))
  :enable (sent-message-wf proc->pid)
  :use ((:instance sent-message-wf-of-update-of-run
          (self (omap::lookup pid net))
          (outbox (proc->outbox (omap::lookup pid net)))
          (parent (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))))))

(defruled sent-message-wf-of-update-of-first-run-with-children
  (implies
    (and
      (network-p net) (network-p (omap::update p proc net))
      (proc-p proc) (not (equal pid p))
      (omap::assoc pid net) (omap::assoc p net)
      (erl-val-p (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))))
      (equal
        (proc->ps (omap::lookup p net)) :idle) (equal (proc->ps proc)
        :receive)
      (equal (proc->inbox-new proc) (proc->inbox-new (omap::lookup p net)))
      (omap::assoc 'CPids (erl-state->bind (proc->s proc)))
      (equal
        (erl-val-kind
          (omap::lookup 'CPids (erl-state->bind (proc->s proc))))
        :cons)
      (equal (erl-val-cons->lst
               (omap::lookup 'CPids (erl-state->bind (proc->s proc))))
             (erl-val-cons->lst
               (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))
      (or (not (equal (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))) p))
          (member-equal pid
            (erl-val-cons->lst
              (omap::lookup
                'ChildPids
                (wtree-bind (omap::lookup p net))))))
      (sent-message-wf (omap::lookup pid net)
                       (proc->outbox (omap::lookup pid net))
                       (omap::lookup 'Parent
                          (wtree-bind (omap::lookup pid net)))
                       net))
    (sent-message-wf (omap::lookup pid net)
                     (proc->outbox (omap::lookup pid net))
                     (omap::lookup 'Parent
                        (wtree-bind (omap::lookup pid net)))
                     (omap::update p proc net)))
  :cases ((equal (omap::lookup 'Parent
                    (wtree-bind (omap::lookup pid net))) p))
  :enable (sent-message-wf proc->pid))


; parent of inv node -------------------------------------------------------------

(defruled inv-node-parent-props
  (implies
    (and
      (network-p net) (wtree-p net) (inv pid net)
      (omap::assoc pid net))
    (and
      (erl-val-p (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))))
      (or
        (not (equal (proc->ps (omap::lookup pid net)) :terminated))
        (sent-message-wf (omap::lookup pid net)
          (proc->outbox (omap::lookup pid net))
          (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
          net))
      (or (equal (proc->ps (omap::lookup pid net)) :terminated)
          (parent-still-waiting-p pid
            (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
            net))))
  :use ((:instance wtree-nodes-are-leaf-or-root (pid pid))
        (:instance sent-message-wf-when-inv-terminated)))