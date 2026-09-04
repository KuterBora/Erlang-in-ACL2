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
       ((unless (equal sval val)) nil))
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
    (defcong network-equiv equal (sent-message-wf a b c d) 4))

; Klst Well Formed ------------------------------------------------------------

(define reduce-receive-klst-p ((klst erl-klst-p) (rbind bind-p))
  :returns (r booleanp)
  (b* ((klst (erl-klst-fix klst))
       (rbind (bind-fix rbind))
       ((unless (equal (len klst) 3)) nil)
       (k1 (car klst))
       (k2 (cadr klst))
       (k3 (caddr klst))
       ; All continuations must have enough fuel.
       ; Let's say at least 100. For this example,
       ; it is not that important. 
       ((unless (> (erl-k->fuel k1) 100)) nil)
       ((unless (> (erl-k->fuel k2) 100)) nil)
       ((unless (> (erl-k->fuel k3) 100)) nil)
       ; The three continuations must be the following:
       (kont1 (erl-k->kont k1))
       (kont2 (erl-k->kont k2))
       (kont3 (erl-k->kont k3)))
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
    (defcong bind-equiv equal (reduce-receive-klst-p klst rbind) 2)
    
    (defrule wtree-bind0-of-reduce-receive-klst-p
      (implies (reduce-receive-klst-p nklst rbind)
               (equal (wtree-bind0 bind nklst) (bind-fix rbind)))
      :enable wtree-bind0
      :prep-lemmas
        ((defrule car-of-last-of-len-3
           (implies (equal (len x) 3)
                    (equal (car (last x)) (caddr x)))
           :expand ((len x) (len (cdr x)) (len (cddr x))
                    (len (cdddr x)) (last x) (last (cdr x))
                    (last (cddr x))))))

    ; I needed this rule a few times, but it naturally slows down everything
    ; quite a bit if I enable it.
    (defruled normalize-reduce-receive-klst-p
      (implies
        (reduce-receive-klst-p klst rbind)
        (reduce-receive-klst-p
          klst
          (kont-function-return->bind (erl-k->kont (caddr (erl-klst-fix klst))))))))