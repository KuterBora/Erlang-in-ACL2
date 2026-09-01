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

; (skip-proofs (defrule wtree0-p-of-erl-step
;   (implies
;     (and (network-p net) (wtree0-p net net0 (omap::size net)))
;     (wtree0-p (erl-step net) (erl-step net0) (omap::size (erl-step net))))
;   :enable (wtree0-p erl-step proc-receive)))

; ; TODO for Mark
; (defrule wtree-p-of-erl-step
;   (implies
;     (and (network-p net) (wtree-p net))
;     (wtree-p (erl-step net)))
;   :enable wtree-p)

; TODO maybe I should make wtree-p a fixtype?
; Also, do I need to state that the wtree must have a root?
; How will fuel work?

; TODO: inbox-tried
                ; messages valid, but does not contain ClHd.
                ; forall received messages, sender has terminated. Thus, can use
                ; the inv from above
                ; 
; same as blocked, but inbox-tried is empty.
          ; inbox new messages are valid.
          ; Message valid means
          ;  - there exists x in CPids with message's pid
          ;  - message contains reduce up
          ;  - val in message is the val in terminated message.



(define sum ((n natp))
  (b* ((n (nfix n))
       ((if (= n 0)) 0))
      (+ n (sum (1- n)))))

; (sum-range 0 2) -> 3
; (sum-range 1 2) -> 3
; (sum-range 1 3) -> 6
; (sum-range 5 6) -> 11
(define sum-range ((i natp) (j natp))
  :returns (n natp)
  :measure (acl2-count (- (nfix j) (nfix i)))
  (b* ((i (nfix i))
       (j (nfix j))
       ((if (< j i)) 0)
       ((if (equal i j)) i))
      (+ i (sum-range (+ 1 i) j)))
  ///
    (defcong nat-equiv equal (sum-range i j) 1)
    (defcong nat-equiv equal (sum-range i j) 2)
    
    (defrule sum-range-of-add
      (implies
        (and (natp i) (natp j) (natp n) (<= i j) (< j n))
        (equal (+ (sum-range i j) (sum-range (+ j 1) n))
               (sum-range i n))))
    (defrule sum-range-of-sum
      (implies
        (and (natp i) (natp j) (<= i j))
        (equal (sum-range i j) (- (sum j) (sum (1- i)))))
      :enable sum)
    (defrule sum-range-of-one
      (implies (natp j) (equal (sum-range 1 j) (sum j)))
      :enable sum)
    (defrule sum-range-of-zero
      (implies (natp j) (equal (sum-range 0 j) (sum j)))
      :enable sum))

; forall messages in inbox
; the sender exists in cpids and net,
; the sender is terminated,
; the received message has the has value as the terminated
; process' value.
; TODO: Should I make sure there are no double messages?
(define received-messages-wf
  ((inbox erl-vlst-p) (cpids erl-vlst-p) (net network-p))
  :returns (r booleanp)
  :measure (acl2-count (erl-vlst-fix inbox))
  (b* ((inbox (erl-vlst-fix inbox))
       (cpids (erl-vlst-fix cpids))
       (net (network-fix net))
       ((unless inbox) t)
       (m (car inbox))
       ((unless (equal (erl-val-kind m) :tuple)) nil)
       (lst (erl-val-tuple->lst m))
       ; message should be in form: {sender, direction, value}
       ((unless (equal (len lst) 3)) nil)
       (sender (car lst))
       (dir (cadr lst))
       (val (caddr lst))
       ; the sender exists
       ((unless (member-equal sender cpids)) nil)
       ((unless (omap::assoc sender net)) nil)
       (sproc (omap::lookup sender net))
       ; the sender must have terminated
       ((unless (equal (proc->ps sproc) :terminated)) nil)
       ; the sender must have sent its own value
       ; which will be equal to its sum-range.
       ; This is simply an implementation detail,
       ; and the invariant should depend on a more general fact.
       (sval (erl-state->in (proc->s sproc)))
       ((unless (equal sval val)) nil)
       ; The direction is up
       ((unless
          (and (equal (erl-val-kind dir) :atom)
               (equal (erl-val-atom->val dir) 'reduce-up)))))
      (received-messages-wf (cdr inbox) cpids net))
  ///
    (defcong erl-vlst-equiv equal (received-messages-wf x y z) 1)
    (defcong erl-vlst-equiv equal (received-messages-wf x y z) 2)
    (defcong network-equiv equal (received-messages-wf x y z) 3))

; more helpers
(define inbox-contains ((inbox erl-vlst-p) (pid pid-p))
  :returns (r booleanp)
  :measure (acl2-count (erl-vlst-fix inbox))
  (b* ((inbox (erl-vlst-fix inbox))
       (pid (pid-fix pid))
       ((unless inbox) nil)
       (m (car inbox))
       ((if (equal m pid)) t))
      (inbox-contains (cdr inbox) pid))
  ///
    (defcong erl-vlst-equiv equal (inbox-contains x y) 1)
    (defcong pid-equiv equal (inbox-contains x y) 2))


(defrule head-of-outbox
  (implies
    (and (not (omap::emptyp m)) (outbox-p m))
    (and
      (pid-p (mv-nth 0 (omap::head m)))
      (erl-vlst-p (mv-nth 1 (omap::head m)))))
  :enable outbox-p)

(defrule head-of-outbox-consp
  (implies
    (and
      (not (omap::emptyp m)) (outbox-p m)
      (mv-nth 1 (omap::head m)))
    (consp (mv-nth 1 (omap::head m))))
  :enable (outbox-p erl-vlst-p)
  :disable head-of-outbox
  :use (:instance head-of-outbox))

  ; if outbox not null
  ;   it has a single message, same as the process's value
  ; if the outbox is null
  ; if the parent
  ;   is terminated ok
  ;   else
  ;     either inbox-new or inbox-tried contains the message
  ;     or Cpids does not contain the message,
  ;     ??? index of Chd is greater than self's index
(define sent-message-wf
  ((self proc-p) (outbox outbox-p) (parent erl-val-p) (net network-p))
  :returns (r booleanp)
  :enabled t
  ;guard-hints (("Goal" :use (:insrance )))
  (b* ((self (proc-fix self))
       (outbox (outbox-fix outbox))
       (parent (erl-val-fix parent))
       (net (network-fix net)) 
       ; the root does not send messages
       ((unless (pid-p parent)) (omap::emptyp outbox))
       ; the parent exists, though we know this when
       ;  calling this helper.
       ((unless (omap::assoc parent net)) nil)
       (pproc (omap::lookup parent net))
       (ps (proc->ps pproc))
       ; We can assume that self is terminated.
       (val (erl-state->in (proc->s self))))
      (if (omap::emptyp outbox)
          (case ps
            (:terminated t)
            ; message must be in the correct inbox
            ; the other helper already checks that it
            ; is the correct message, so here I
            ; only need to check that the message was
            ; received. 
            (:idle
              (inbox-contains (proc->inbox-new pproc)
                              (proc->pid self)))
            (:blocked
              ; same here, the main invariant makes
              ; sure other properties are correct.
              (or
                (inbox-contains (proc->inbox-new pproc)
                                (proc->pid self))
                (inbox-contains (proc->inbox-tried pproc)
                                (proc->pid self))))
            (:receive
              (inbox-contains (proc->inbox-new pproc)
                              (proc->pid self))))
          (b* ((ms (omap::head-val outbox))
               ; there is a single message
               ((unless (and ms (not (cdr ms)))) nil)
               (m (car ms))
               ; message is for the parent
               ((unless (equal (omap::head-key outbox) parent)) nil)
               ; this implementation sends no other message
               ((unless (omap::emptyp (omap::tail outbox))) nil)
               ; message should be in form: {sender, direction, value} 
               ((unless (equal (erl-val-kind m) :tuple)) nil)
               (lst (erl-val-tuple->lst m))
               ((unless (equal (len lst) 3)) nil)
               ((unless (equal (car lst) (proc->pid self))) nil)
               ((unless (equal (cadr lst) 'reduce_up)) nil)
               ((unless (equal (caddr lst) val)) nil))
              t)))
  ///
    (defcong proc-equiv equal (sent-message-wf a b c d) 1)
    (defcong outbox-equiv equal (sent-message-wf a b c d) 2)
    (defcong erl-val-equiv equal (sent-message-wf a b c d) 3)
    (defcong network-equiv equal (sent-message-wf a b c d) 4))

(define reduce-receive-klst-p ((klst erl-klst-p) (rbind bind-p))
  :returns (r booleanp)
  :enabled t
  (b* ((klst (erl-klst-fix klst))
       (rbind (bind-fix rbind))
       ((unless (equal (len klst) 3)) nil)
       (k1 (car klst))
       (k2 (cadr klst))
       (k3 (caddr klst))
       ; All continuations must have enough fuel, lets say 100
       ((unless (> (erl-k->fuel k1) 100)) nil)
       ((unless (> (erl-k->fuel k2) 100)) nil)
       ((unless (> (erl-k->fuel k3) 100)) nil)
       ; The three continuations must be the following:
       (kont1 (erl-k->kont k1))
       (kont2 (erl-k->kont k1))
       (kont3 (erl-k->kont k1)))
      (and
        (equal
          kont1
          (make-kont-receive
            :clauses '(((cases (:tuple (:cons (:var childhd)
                                             (:cons (:var righttotal) (:nil)))))
                        (guards)
                        (body (:call sum_reduce
                                     (:cons (:var parentpid)
                                            (:cons (:var childtl)
                                                   (:cons (:binop + (:var lefttotal)
                                                                    (:var righttotal))
                                                          (:nil))))))))))
        (equal kont2 (make-kont-exprs :exprs nil))
        (equal kont3
          (make-kont-function-return
            :bind rbind
            :module 'local))))
  ///
    (defcong erl-klst-equiv equal (reduce-receive-klst-p klst rbind) 1)
    (defcong bind-equiv equal (reduce-receive-klst-p klst rbind) 2))



(defrule pid-lst-crock
  (implies
    (and (prefixp (rev l2) (rev l1))
         l2 (erl-vlst-p l2) (pid-lst-p l1))
    (pid-lst-p l2))
  :use (:instance prefix-of-pid-lst-p
        (l1 (rev l1)) (l2 (rev l2)))
  :prep-lemmas
    ((defrule prefix-of-pid-lst-p
       (implies
         (and (pid-lst-p l1) (erl-vlst-p l2) (prefixp l2 l1))
         (pid-lst-p l2))
       :enable prefixp)))




; '???' notes constrains that might not be necessary.
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
                (erl-state->bind (proc->s (omap::lookup pid net))))))
      ))
  (b* ((pid (pid-fix pid))
       (net (network-fix net))
       ((unless (wtree-p net)) nil)
       ((unless (omap::assoc pid net)) nil)
       (proc (omap::lookup pid net))
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
          (b* (; init-proc simulates a proc that has just been spawned,
               ;  having received no messages.
               (init-proc (make-reduce-proc pid parent children index))
               ((unless (equal (proc->s proc) (proc->s init-proc))) nil)
               ((unless (equal (proc->klst proc) (proc->klst init-proc))) nil)
               ((unless (null (proc->inbox-tried proc))) nil)
               (inbox (proc->inbox-new proc)))
              (received-messages-wf inbox children net)))
        (:terminated
          (b* ((val (erl-state->in (proc->s proc)))
               ((unless (equal (erl-val-kind val) :integer)) nil)
               (val (erl-val-integer->val val))
               ((if (null children)) (equal val index))
               (cpid (rightmost-child pid net))
               
               ; TODO: this is a wtree-p property
              ((unless (omap::assoc cpid net)) nil)
              ((unless (leaf-p (omap::lookup cpid net))) nil)

               (cproc (omap::lookup cpid net))
               (cbind (erl-state->bind (proc->s cproc)))
               (cindex (erl-val-integer->val (omap::lookup 'Index cbind))))
              (and
                ; the value must be the sum of indices of this branch.
                (equal val (sum-range index cindex))
                ; message sent must be well formed, if any
                (sent-message-wf proc (proc->outbox proc) parent net)
                ; all messages have been received already   
                (null (proc->inbox-tried proc))
                (null (proc->inbox-new proc))
                ; ???: all children are terminated?
                )))   
        (:blocked
          (b* (; if the node has no children, then it should not have blocked.
               ((if (null children)) nil)
              
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

               ; TODO: this follows from wtree-p
               ((if (equal cindex index)) nil)

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
               ((unless (reduce-receive-klst-p klst rbind)) t))
             ; Check that there is no deadlock
             (not (terminated? net))))
        (:receive
          (b* (; if the node has no children, then it should not try to receive.
               ((if (null children)) nil)
              
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

               ; Inbox-tried is empty, because the process has not started
               ;  attempting to receive yet.
               ((unless (null (proc->inbox-tried proc))) nil)

               ; Inbox-new contains valid messages.
               (inbox (proc->inbox-tried proc))
               ((unless (received-messages-wf inbox cps net)) nil)
               
               ;???: For messages not have yet received;
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
               ((unless (reduce-receive-klst-p klst rbind)) t))
             ; Check that there is no deadlock
             (not (terminated? net))))))
  ///
    (defcong pid-equiv equal (inv pid net) 1)
    (defcong network-equiv equal (inv pid net) 2))


(defrule inv-of-erl-step
  (implies
    (and (pid-p pid) (network-p net) (inv pid net))
    (inv pid (erl-step net)))
  :enable (inv erl-step)
  :disable
    (scheduler-correct-when-run
     scheduler-correct-when-deliver)
  :use ((:instance scheduler-correct-when-run)
        (:instance scheduler-correct-when-deliver)))



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