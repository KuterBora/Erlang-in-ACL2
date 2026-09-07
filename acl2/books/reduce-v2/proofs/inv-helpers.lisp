(in-package "ACL2")
(include-book "util")

(set-induction-depth-limit 1)

; Helpers for the reduce invariant.

; Received Messages Well Formed -----------------------------------------------

; forall messages in inbox
; the sender exists in cpids and net,
; the sender is terminated and has drained its outbox,
; the received message has the same value as the terminated
; process' value,
; and no two messages have the same sender, which is enforced by
; dropping each sender from cpids as it goes.
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
       ; The message is in the form {sender, value}.
       ((unless (equal (len lst) 2)) nil)
       (sender (car lst))
       (val (cadr lst))
       ; the sender exists
       ((unless (member-equal sender cpids)) nil)
       ((unless (omap::assoc sender net)) nil)
       (sproc (omap::lookup sender net))
       ; the sender must have terminated
       ((unless (equal (proc->ps sproc) :terminated)) nil)
       ; and the sender must have already sent its message,
       ; else there would be duplicates.
       ((unless (outbox-emptyp (proc->outbox sproc))) nil)
       ; the sender must have sent its own value
       ; which will be equal to its sum-range.
       (sval (erl-state->in (proc->s sproc)))
       ((unless (equal sval val)) nil)
       ; the value is an integer
       ((unless (equal (erl-val-kind val) :integer)) nil))
      ; Ensure that no two messages have arrived from the same sender
      ; by dropping it from cpids.
      (received-messages-wf (cdr inbox) (remove-equal sender cpids) net))
  ///
    (defcong erl-vlst-equiv equal (received-messages-wf x y z) 1
      :hints (("Goal" :expand ((received-messages-wf x y z)
                               (received-messages-wf x-equiv y z)))))
    (defcong erl-vlst-equiv equal (received-messages-wf x y z) 2
      :hints (("Goal" :expand ((received-messages-wf x y z)
                               (received-messages-wf x y-equiv z)))))
    (defcong network-equiv equal (received-messages-wf x y z) 3
      :hints (("Goal" :expand ((received-messages-wf x y z)
                               (received-messages-wf x y z-equiv)))))
    
    (defrule received-messages-wf-of-nil
      (implies
        (and (erl-vlst-p inbox)
             (received-messages-wf inbox nil net))
        (not inbox))
      :rule-classes :forward-chaining)

    ; Removing a message from the inbox maintains the invariant.
    (defrule received-messages-wf-of-inbox-without
      (implies
        (and (network-p net)
             (erl-vlst-p cpids) (pid-p pid)
             (received-messages-wf inbox cpids net))
        (received-messages-wf (inbox-without inbox pid)
                              (remove-equal pid cpids) net))
      :enable inbox-without)
    
    (defrule not-inbox-contains-of-received-messages-wf
      (implies
        (and
          (network-p net) (omap::assoc sender net)
          (not (outbox-emptyp (proc->outbox (omap::lookup sender net))))
          (received-messages-wf inbox cpids net))
        (not (inbox-contains inbox sender)))
      :enable inbox-contains)
    
    (defrule received-messages-wf-of-update-of-non-terminated
      (implies
        (and
          (network-p net) (network-p (omap::update q qproc net))
          (omap::assoc q net)
          (not (equal (proc->ps (omap::lookup q net)) :terminated))
          (received-messages-wf inbox cpids net))
        (received-messages-wf inbox cpids (omap::update q qproc net)))
      :enable omap::lookup-of-update)
    
    (defrule received-messages-wf-fields
      (implies
        (and (network-p net) (pid-p pid)
             (received-messages-wf inbox cpids net)
             (inbox-contains inbox pid))
        (and (omap::assoc pid net)
             (equal (proc->ps (omap::lookup pid net)) :terminated)
             (outbox-emptyp (proc->outbox (omap::lookup pid net)))
             (equal (inbox->value inbox pid)
                    (erl-state->in (proc->s (omap::lookup pid net))))))
      :enable (inbox->value inbox-contains)))


; Sent Messages Well Formed ---------------------------------------------------

; TODO: better description
; if outbox not null
;   it has a single message, same as the process's value
; if the outbox is null
;   if the parent is terminated
;     ok
;     else: either inbox-new or inbox-tried contains the message
;           or Cpids does not contain the message,
;           index of Chd is greater than self's index
(define sent-message-wf
  ((self proc-p) (outbox outbox-p) (parent erl-val-p) (net network-p))
  :returns (r booleanp)
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
       (pbind (erl-state->bind (proc->s pproc)))
       ; Check if the message has been received and processed
       ; by the parent.
       (received
         (and (omap::assoc 'CPids pbind)
              (equal (erl-val-kind (omap::lookup 'CPids pbind)) :cons)
              (not (member-equal
                    (proc->pid self)
                    (erl-val-cons->lst (omap::lookup 'CPids pbind))))))
       (val (erl-state->in (proc->s self))))
      (if (not (and (omap::assoc parent outbox)
                    (omap::lookup parent outbox)))
          ; If there is no message for the parent
          (and
           ; all messages have been sent.
           (outbox-emptyp outbox)
           (case ps
            ; if the parent has terminated, we are done.
            (:terminated t)
            ; message must be in the correct inbox.
            ; The received helper checks that the message
            ; is also correct.
            (:idle
              (inbox-contains (proc->inbox-new pproc)
                              (proc->pid self)))
            (:blocked
              ; Either the message is in one of the inboxes,
              ; or it was already received and processed.
              (or
                (inbox-contains (proc->inbox-new pproc)
                                (proc->pid self))
                (inbox-contains (proc->inbox-tried pproc)
                                (proc->pid self))
                received))
            ; Same as above, but the process has not tried
            ; to receive the message yet.
            (:receive
              (or
                (inbox-contains (proc->inbox-new pproc)
                                (proc->pid self))
                received))))
          ; If there is a message for the parent:
          (b* ((ms (omap::lookup parent outbox))
               ; The parent should be have terminated,
               ; or received the message yet.
               ((if (equal ps :terminated)) nil)
               ((if received) nil)
               ; there is a single message
               ((unless (and ms (not (cdr ms)))) nil)
               (m (car ms))
               ; this implementation sends no other message
               ((unless (omap::emptyp (omap::tail outbox))) nil)
               ; message should be in form: {sender, value}
               ((unless (equal (erl-val-kind m) :tuple)) nil)
               (lst (erl-val-tuple->lst m))
               ((unless (equal (len lst) 2)) nil)
               ((unless (equal (car lst) (proc->pid self))) nil)
               ((unless (equal (cadr lst) val)) nil))
              t)))
  ///
    (defcong proc-equiv equal (sent-message-wf a b c d) 1)
    (defcong outbox-equiv equal (sent-message-wf a b c d) 2)
    (defcong erl-val-equiv equal (sent-message-wf a b c d) 3)
    (defcong network-equiv equal (sent-message-wf a b c d) 4)
    
    (defrule sent-message-wf-when-parent-has-message
      (implies
        (and
          (network-p net) (outbox-p outbox)
          (outbox-emptyp outbox)
          (omap::assoc parent net)
          (inbox-contains (proc->inbox-new (omap::lookup parent net))
                          (proc->pid self)))
        (sent-message-wf self outbox parent net))))

; Klst Well Formed ------------------------------------------------------------

; Initial klst
(defconst *reduce-receive-body*
  '((:call sum_reduce
           (:cons (:var parentpid)
                  (:cons (:var childtl)
                         (:cons (:binop + (:var lefttotal)
                                          (:var righttotal))
                                (:nil)))))))
; Continuation after the receive
(defconst *reduce-receive-clauses*
  '(((cases (:tuple (:cons (:var childhd)
                           (:cons (:var righttotal) (:nil)))))
     (guards)
     (body (:call sum_reduce
                  (:cons (:var parentpid)
                         (:cons (:var childtl)
                                (:cons (:binop + (:var lefttotal)
                                                 (:var righttotal))
                                       (:nil)))))))))

; TODO: This was another last minute realization. It is caused because
; my implementation of reduce is not tail recursive.
; As a worker node calls
; reduce again and again, it will accumluate a list of continuations
; where every three row of continuations are:
; 1- exprs nil, remaining form the body of the matched receive clauses
; 2- exprs nil, remaining from the body of reduce function clauses
; 3- function-return, the return from the call to reduce
; I would prefer to look for a better way to solve this problem, alas,
; I realized this very late when removing a skip-proofs, which is,
; after all, "a quick way to introduce unsoundness".
(define reduce-klst-lst-p ((klst erl-klst-p) (rbind bind-p))
  :returns (r booleanp)
  :measure (len (erl-klst-fix klst))
  (b* ((klst (erl-klst-fix klst))
       (rbind (bind-fix rbind))
       ((unless (<= 3 (len klst))) nil)
       (k1 (car klst))
       (k2 (cadr klst))
       (k3 (caddr klst))
       ((unless (> (erl-k->fuel k1) 100)) nil)
       ((unless (> (erl-k->fuel k2) 100)) nil)
       ((unless (> (erl-k->fuel k3) 100)) nil)
       ((unless (equal (erl-k->kont k1) (make-kont-exprs :exprs nil))) nil)
       ((unless (equal (erl-k->kont k2) (make-kont-exprs :exprs nil))) nil)
       ((unless (equal (kont-kind (erl-k->kont k3)) :function-return)) nil)
       ((unless (equal (kont-function-return->module (erl-k->kont k3)) 'local)) nil)
       ; The last bindings is the one the process was spawned with.
       ((unless (cdddr klst))
        (equal (kont-function-return->bind (erl-k->kont k3)) rbind)))
      (reduce-klst-lst-p (cdddr klst) rbind))
  ///
    (defcong erl-klst-equiv equal (reduce-klst-lst-p klst rbind) 1)
    (defcong bind-equiv equal (reduce-klst-lst-p klst rbind) 2)

    (defrule last-of-reduce-klst-lst-p
      (implies
        (reduce-klst-lst-p klst rbind)
        (and
          (equal
            (kont-kind (erl-k->kont (car (last (erl-klst-fix klst)))))
            :function-return)
          (equal
            (kont-function-return->bind
              (erl-k->kont (car (last (erl-klst-fix klst)))))
            (bind-fix rbind)))))
    (defrule wtree-bind0-of-reduce-klst-lst-p
      (implies (reduce-klst-lst-p klst rbind)
               (equal (wtree-bind0 bind klst) (bind-fix rbind)))
      :enable wtree-bind0))

; Check if the klst of a process that is awaiting to receive is well fromed. 
(define reduce-receive-klst-p ((klst erl-klst-p) (rbind bind-p))
  :returns (r booleanp)
  (b* ((klst (erl-klst-fix klst))
       (rbind (bind-fix rbind))
       ((unless (<= 3 (len klst))) nil)
       (k1 (car klst))
       (k2 (cadr klst))
       (k3 (caddr klst))
       ; There must be enough fuel, let's overshoot and say > 100.
       ((unless (> (erl-k->fuel k1) 100)) nil)
       ((unless (> (erl-k->fuel k2) 100)) nil)
       ((unless (> (erl-k->fuel k3) 100)) nil)
       ; The three continuations at the head must be the following:
       (kont1 (erl-k->kont k1))
       (kont2 (erl-k->kont k2))
       (kont3 (erl-k->kont k3))
       ((unless
          (equal kont1
                 (make-kont-receive :clauses *reduce-receive-clauses*)))
        nil)
       ((unless (equal kont2 (make-kont-exprs :exprs nil))) nil)
       ((unless (equal (kont-kind kont3) :function-return)) nil)
       ((unless (equal (kont-function-return->module kont3) 'local)) nil)
       ; Ensure that the auxillary varaibles have not changed.
       ((unless (cdddr klst))
        (equal (kont-function-return->bind kont3) rbind)))
      ; If there are more continuations, then they must be call stacks
      ; of previous calls to reduce.
      (reduce-klst-lst-p (cdddr klst) rbind))
  ///
    (defcong erl-klst-equiv equal (reduce-receive-klst-p klst rbind) 1)
    (defcong bind-equiv equal (reduce-receive-klst-p klst rbind) 2)

    (defrule wtree-bind0-of-reduce-receive-klst-p
      (implies (reduce-receive-klst-p nklst rbind)
               (equal (wtree-bind0 bind nklst) (bind-fix rbind)))
      :enable wtree-bind0)
    
    (defruled normalize-reduce-receive-klst-p
      (implies
        (reduce-receive-klst-p (proc->klst p) rbind)
        (reduce-receive-klst-p (proc->klst p) (wtree-bind p)))
      :enable wtree-bind
      :disable (wtree-bind0-to-wtree-bind reduce-receive-klst-p)))

(defrule reduce-receive-klst-p-new-call-stack
  (implies
    (and
      (reduce-receive-klst-p klst rbind)
      (> (erl-k->fuel (car klst)) 106))
    (reduce-receive-klst-p
      (append
        (list (erl-k (- (erl-k->fuel (car klst)) 6) (erl-k->kont (car klst)))
              (erl-k (- (erl-k->fuel (car klst)) 6)
                     (make-kont-exprs :exprs nil))
              (erl-k (- (erl-k->fuel (car klst)) 3)
                     (make-kont-function-return :bind b :module 'local))
              (erl-k (- (erl-k->fuel (car klst)) 1)
                     (make-kont-exprs :exprs nil)))
        (cdr klst))
      rbind))
  :enable (reduce-receive-klst-p reduce-klst-lst-p))

; Inbox Formed ----------------------------------------------------------------

(define wf-inbox-p ((inbox erl-vlst-p))
  :returns (r booleanp)
  :measure (acl2-count (erl-vlst-fix inbox))
  (b* ((inbox (erl-vlst-fix inbox))
       ((unless inbox) t)
       (m (car inbox))
       ((unless (equal (erl-val-kind m) :tuple)) nil)
       ((unless (equal (len (erl-val-tuple->lst m)) 2)) nil)
       ((unless (equal (erl-val-kind (cadr (erl-val-tuple->lst m))) :integer))
        nil))
      (wf-inbox-p (cdr inbox)))
  ///
    (defcong erl-vlst-equiv equal (wf-inbox-p inbox) 1
      :hints (("Goal" :expand ((wf-inbox-p inbox)
                               (wf-inbox-p inbox-equiv)))))

    (defrule wf-inbox-p-of-received-messages-wf
      (implies (received-messages-wf inbox cpids net)
               (wf-inbox-p inbox))
      :enable received-messages-wf
      :induct (received-messages-wf inbox cpids net))

    (defrule wf-inbox-p-of-car
      (implies
        (and (wf-inbox-p inbox) (erl-vlst-p inbox) (consp inbox))
        (and (erl-val-p (car inbox))
             (equal (erl-val-kind (car inbox)) :tuple)
             (equal (len (erl-val-tuple->lst (car inbox))) 2)
             (equal (erl-val-kind (cadr (erl-val-tuple->lst (car inbox))))
                    :integer)))
      :enable erl-vlst-p)

    (defrule wf-inbox-p-of-cdr
      (implies (and (wf-inbox-p inbox) (erl-vlst-p inbox))
               (wf-inbox-p (cdr inbox)))
      :enable erl-vlst-p))