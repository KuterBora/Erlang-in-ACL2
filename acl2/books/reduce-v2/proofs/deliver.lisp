(in-package "ACL2")
(include-book "inv")
(include-book "../../../theorems/top")

; Proving that the invariant holds after erl-step.

; Useless runes:
(local (in-theory
  (disable
    wtree-bind-when-no-function-return
    omap::assoc-when-assoc-tail member-equal
    assoc-of-runnable? pid-p-when-member-equal-of-pid-lst-p
    last consp-of-expr-list-p remove-equal pid-lst-crock
    omap::assoc-when-assoc-of-tail-cheap omap::lookup-when-emptyp
    runnable-of-tail (:type-prescription omap::tail-when-emptyp)
    pid-lst-p-when-not-consp default-cdr wtree0-of-zero
    subsetp-when-atom-right omap::mapp-non-nil-implies-not-emptyp
    consp-when-member-equal-of-symbol-truelist-alistp
    consp-when-member-equal-of-keyword-truelist-alistp
    leaf-when-assoc-of-tail-is-leaf outbox-p-of-tail
    parent-still-waiting-p-of-inv)))

; Inv of Deliver ----------------------------------------------------

; Facts when a worker has a message in its outbox.
; TODO: this one is expensive.
(local (defruled sender-with-message-props
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
          (map (proc->outbox (omap::lookup src net)))))))


; received-messages-wf -----------------------------------------------------------

(local (defrule received-messages-wf-of-update
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
  :enable (received-messages-wf omap::lookup-of-update)))

(local (defrule received-messages-wf-of-append-message
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
  :induct (received-messages-wf inbox cpids net)))


; sent-message-wf ----------------------------------------------------------------

(local (defrule sent-message-wf-of-update
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
     append-when-not-consp not-inbox-contains-of-received-messages-wf)))


; inv of unchanged nodes --------------------------------------------------------

(local (defrule inv-of-update-of-other-node
  (implies
    (and
      (network-p net) (inv pid net)
      (pid-p pid) (not (equal pid p))
      (not (terminated? (omap::update p proc net)))
      
      ; the node which was updated to proc
      (omap::assoc p net) (proc-p proc) (erl-vlst-p msgs)
      (network-p (omap::update p proc net))
      (equal (erl-state->self (proc->s proc)) p)
      (equal (erl-state->bind (proc->s proc))
             (erl-state->bind (proc->s (omap::lookup p net))))
      (equal (wtree-bind proc) (wtree-bind (omap::lookup p net)))
      (equal (erl-state->in (proc->s proc))
             (erl-state->in (proc->s (omap::lookup p net))))
      (or (not (outbox-emptyp (proc->outbox (omap::lookup p net))))
          (outbox-emptyp (proc->outbox proc)))
      (or
        ; process was already on receive (or on idle).
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
                            msgs)))))
    (inv pid (omap::update p proc net)))
  :enable inv
  :use ((:instance leaf-root-p-when-bind-equal
         (p1 proc) (p2 (omap::lookup p net)))
        (:instance wtree-nodes-are-leaf-or-root (pid p)))))


; inv of dst --------------------------------------------------------------------

; receiver is idle
(local (defruled inv-of-update-of-idle-dst-append
  (implies
    (and
      (network-p net) (inv dst net)
      (network-p (omap::update dst pdst net))
      (not (terminated? (omap::update dst pdst net)))

      ; src facts
      (pid-p src) (omap::assoc src net)
      (equal (proc->ps (omap::lookup src net)) :terminated)
      (outbox-emptyp (proc->outbox (omap::lookup src net)))
      (equal (erl-val-kind (erl-state->in (proc->s (omap::lookup src net))))
             :integer)
      
      ; dst facts, pdst is the proc after erl-step
      (pid-p dst) (proc-p pdst) (not (equal src dst))
      (omap::assoc dst net)
      (not (equal (proc->ps (omap::lookup dst net)) :terminated))
      (equal (erl-state->self (proc->s pdst)) dst)
      (equal (proc->s pdst) (proc->s (omap::lookup dst net)))
      (equal (proc->klst pdst) (proc->klst (omap::lookup dst net)))
      (equal (wtree-bind pdst) (wtree-bind (omap::lookup dst net)))
      (member-equal src
        (erl-val-cons->lst
          (omap::lookup 'ChildPids (wtree-bind (omap::lookup dst net)))))
      ; dst is idle, so CPids do not exist yet
      (not (and (omap::assoc 'CPids
               (erl-state->bind (proc->s (omap::lookup dst net))))
             (equal (erl-val-kind
                      (omap::lookup 'CPids
                        (erl-state->bind (proc->s (omap::lookup dst net)))))
                    :cons)))
      (not (inbox-contains (proc->inbox-new (omap::lookup dst net)) src))
      (not (inbox-contains (proc->inbox-tried (omap::lookup dst net)) src))
      (equal (proc->ps pdst) (proc->ps (omap::lookup dst net)))
      (not (equal (proc->ps (omap::lookup dst net)) :blocked))
      (equal (proc->inbox-tried pdst)
             (proc->inbox-tried (omap::lookup dst net)))
      (equal (proc->inbox-new pdst)
             (append (proc->inbox-new (omap::lookup dst net))
                     (list m)))
      ; message facts
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (car (erl-val-tuple->lst m)) src)
      (equal (cadr (erl-val-tuple->lst m))
             (erl-state->in (proc->s (omap::lookup src net)))))
    (inv dst (omap::update dst pdst net)))
  :enable (inv proc->outbox received-messages-wf)
  :disable
    (leaf-root-p-when-bind-equal wtree-nodes-are-leaf-or-root
     received-messages-wf-of-append-message)
  :use ((:instance leaf-root-p-when-bind-equal
          (p1 pdst) (p2 (omap::lookup dst net)))
        (:instance wtree-nodes-are-leaf-or-root (pid dst))
        (:instance received-messages-wf-of-append-message
          (net (omap::update dst pdst net))
          (sender src)
          (inbox (proc->inbox-new (omap::lookup dst net)))
          (cpids
            (erl-val-cons->lst
              (omap::lookup 'ChildPids
                (wtree-bind (omap::lookup dst net)))))))))

; receiver is in receive or blocked
(local (defrule inv-of-update-of-receiving-dst-append
  (implies
    (and
      (network-p net) (inv dst net)
      (network-p (omap::update dst pdst net))
      (not (terminated? (omap::update dst pdst net)))

      ; src facts
      (omap::assoc src net)
      (equal (proc->ps (omap::lookup src net)) :terminated)
      (outbox-emptyp (proc->outbox (omap::lookup src net)))
      (equal
        (erl-val-kind
          (erl-state->in (proc->s (omap::lookup src net))))
        :integer)
      ; dst facts, pdst is the proc after erl-step
      (proc-p pdst) (not (equal src dst))
      (omap::assoc dst net)
      (not (equal (proc->ps (omap::lookup dst net)) :terminated))
      (equal (erl-state->self (proc->s pdst)) dst)
      (equal (proc->s pdst) (proc->s (omap::lookup dst net)))
      (equal (proc->klst pdst) (proc->klst (omap::lookup dst net)))
      (equal (wtree-bind pdst) (wtree-bind (omap::lookup dst net)))
      (member-equal src
        (erl-val-cons->lst
          (omap::lookup 'ChildPids (wtree-bind (omap::lookup dst net)))))
      ; Cpids exists because dst has already run at least once.
      (member-equal src
        (erl-val-cons->lst
          (omap::lookup 'CPids
            (erl-state->bind (proc->s (omap::lookup dst net))))))
      (not (inbox-contains (proc->inbox-new (omap::lookup dst net)) src))
      (not (inbox-contains (proc->inbox-tried (omap::lookup dst net)) src))
      (equal (proc->ps pdst) (proc->ps (omap::lookup dst net)))
      (not (equal (proc->ps (omap::lookup dst net)) :blocked))
      (equal (proc->inbox-tried pdst)
             (proc->inbox-tried (omap::lookup dst net)))
      (equal (proc->inbox-new pdst)
             (append (proc->inbox-new (omap::lookup dst net))
                     (list m)))
      ; message facts
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (car (erl-val-tuple->lst m)) src)
      (equal (cadr (erl-val-tuple->lst m))
             (erl-state->in (proc->s (omap::lookup src net)))))
    (inv dst (omap::update dst pdst net)))
  :enable (inv proc->outbox received-messages-wf)
  :disable
    (leaf-root-p-when-bind-equal wtree-nodes-are-leaf-or-root
     received-messages-wf-of-append-message)
  :use ((:instance leaf-root-p-when-bind-equal
          (p1 pdst) (p2 (omap::lookup dst net)))
        (:instance wtree-nodes-are-leaf-or-root (pid dst))
        (:instance received-messages-wf-of-append-message
          (net (omap::update dst pdst net))
          (sender src)
          (inbox (proc->inbox-new (omap::lookup dst net)))
          (cpids (erl-val-cons->lst
                   (omap::lookup 'ChildPids (wtree-bind (omap::lookup dst net))))))
        (:instance received-messages-wf-of-append-message
          (net (omap::update dst pdst net))
          (sender src)
          (inbox (proc->inbox-new (omap::lookup dst net)))
          (cpids (erl-val-cons->lst
                   (omap::lookup 'CPids
                     (erl-state->bind (proc->s (omap::lookup dst net))))))))))

; inv of blocked -> receive, excpet this case cannot happen
; However, this split helps with performance, or at least it did.
(local (defrule inv-of-update-of-receiver-unblock-1
  (implies
    (and
      (network-p net) (inv dst net)
      (network-p (omap::update dst pdst net))
      (not (terminated? (omap::update dst pdst net)))
      ; src facts
      (omap::assoc src net)
      (equal (proc->ps (omap::lookup src net)) :terminated)
      (outbox-emptyp (proc->outbox (omap::lookup src net)))
      (equal
        (erl-val-kind
          (erl-state->in (proc->s (omap::lookup src net))))
        :integer)
      ; dst facts, pdst is the proc after erl-step
      (proc-p pdst) (not (equal src dst))
      (omap::assoc dst net)
      (not (equal (proc->ps (omap::lookup dst net)) :terminated))
      (equal (erl-state->self (proc->s pdst)) dst)
      (equal (proc->s pdst) (proc->s (omap::lookup dst net)))
      (equal (proc->klst pdst) (proc->klst (omap::lookup dst net)))
      (equal (wtree-bind pdst) (wtree-bind (omap::lookup dst net)))
      (member-equal src
        (erl-val-cons->lst
          (omap::lookup 'ChildPids (wtree-bind (omap::lookup dst net)))))
      ; Remark: this would never actually happen
      (not
        (and (omap::assoc 'CPids
               (erl-state->bind (proc->s (omap::lookup dst net))))
             (equal (erl-val-kind
                      (omap::lookup 'CPids
                        (erl-state->bind (proc->s (omap::lookup dst net)))))
                    :cons)))
      (not (inbox-contains (proc->inbox-new (omap::lookup dst net)) src))
      (not (inbox-contains (proc->inbox-tried (omap::lookup dst net)) src))
      (equal (proc->ps (omap::lookup dst net)) :blocked)
      (equal (proc->ps pdst) :receive)
      (null (proc->inbox-tried pdst))
      (equal (proc->inbox-new pdst)
             (append (proc->inbox-tried (omap::lookup dst net))
                     (proc->inbox-new (omap::lookup dst net))
                     (list m)))
      ; message facts
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (car (erl-val-tuple->lst m)) src)
      (equal (cadr (erl-val-tuple->lst m))
             (erl-state->in (proc->s (omap::lookup src net)))))
    (inv dst (omap::update dst pdst net)))
  :enable (inv proc->outbox received-messages-wf)
  :disable
    (leaf-root-p-when-bind-equal wtree-nodes-are-leaf-or-root
     received-messages-wf-of-append-message)
  :use ((:instance leaf-root-p-when-bind-equal
          (p1 pdst) (p2 (omap::lookup dst net)))
        (:instance wtree-nodes-are-leaf-or-root (pid dst))
        (:instance received-messages-wf-of-append-message
          (net (omap::update dst pdst net))
          (sender src)
          (inbox (proc->inbox-new (omap::lookup dst net)))
          (cpids (erl-val-cons->lst
                   (omap::lookup 'ChildPids (wtree-bind (omap::lookup dst net)))))))))

; the real inv of blocked -> receive
(local (defruled inv-of-update-of-receiver-unblock-2
  (implies
    (and
      (network-p net) (inv dst net)
      (network-p (omap::update dst pdst net))
      (not (terminated? (omap::update dst pdst net)))
      ; src facts
      (omap::assoc src net)
      (equal (proc->ps (omap::lookup src net)) :terminated)
      (outbox-emptyp (proc->outbox (omap::lookup src net)))
      (equal
        (erl-val-kind
          (erl-state->in (proc->s (omap::lookup src net))))
        :integer)
      ; dst facts, pdst is the proc after erl-step
      (pid-p dst) (proc-p pdst) (not (equal src dst))
      (omap::assoc dst net)
      (not (equal (proc->ps (omap::lookup dst net)) :terminated))
      (equal (erl-state->self (proc->s pdst)) dst)
      (equal (proc->s pdst) (proc->s (omap::lookup dst net)))
      (equal (proc->klst pdst) (proc->klst (omap::lookup dst net)))
      (equal (wtree-bind pdst) (wtree-bind (omap::lookup dst net)))
      (member-equal src
        (erl-val-cons->lst
          (omap::lookup 'ChildPids (wtree-bind (omap::lookup dst net)))))
      (member-equal src
        (erl-val-cons->lst
          (omap::lookup 'CPids
            (erl-state->bind (proc->s (omap::lookup dst net))))))
      (not (inbox-contains (proc->inbox-new (omap::lookup dst net)) src))
      (not (inbox-contains (proc->inbox-tried (omap::lookup dst net)) src))
      (equal (proc->ps (omap::lookup dst net)) :blocked)
      (equal (proc->ps pdst) :receive)
      (null (proc->inbox-tried pdst))
      (equal (proc->inbox-new pdst)
             (append (proc->inbox-tried (omap::lookup dst net))
                     (proc->inbox-new (omap::lookup dst net))
                     (list m)))
      ; message facts
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (car (erl-val-tuple->lst m)) src)
      (equal (cadr (erl-val-tuple->lst m))
             (erl-state->in (proc->s (omap::lookup src net)))))
    (inv dst (omap::update dst pdst net)))
  :enable (inv proc->outbox received-messages-wf)
  :disable
    (leaf-root-p-when-bind-equal wtree-nodes-are-leaf-or-root
     received-messages-wf-of-append-message)
  :use ((:instance leaf-root-p-when-bind-equal
          (p1 pdst) (p2 (omap::lookup dst net)))
        (:instance wtree-nodes-are-leaf-or-root (pid dst))
        (:instance received-messages-wf-of-append-message
          (net (omap::update dst pdst net))
          (sender src)
          (inbox (proc->inbox-new (omap::lookup dst net)))
          (cpids (erl-val-cons->lst
                   (omap::lookup 'ChildPids (wtree-bind (omap::lookup dst net))))))
        (:instance received-messages-wf-of-append-message
          (net (omap::update dst pdst net))
          (sender src)
          (inbox (proc->inbox-tried (omap::lookup dst net)))
          (cpids (erl-val-cons->lst
                   (omap::lookup 'CPids
                     (erl-state->bind (proc->s (omap::lookup dst net))))))))))

; inv of dst, all cases
(local (defrule inv-of-update-dst
  (implies
    (and
      (network-p net) (inv dst net)
      (network-p (omap::update dst pdst net))
      (not (terminated? (omap::update dst pdst net)))
      ; src facts
      (omap::assoc src net)
      (equal (proc->ps (omap::lookup src net)) :terminated)
      (outbox-emptyp (proc->outbox (omap::lookup src net)))
      (equal
        (erl-val-kind
          (erl-state->in (proc->s (omap::lookup src net))))
        :integer)
      ; dst facts, pdst is the proc after erl-step
      (proc-p pdst) (not (equal src dst))
      (omap::assoc dst net)
      (not (equal (proc->ps (omap::lookup dst net)) :terminated))
      (equal (erl-state->self (proc->s pdst)) dst)
      (equal (proc->s pdst) (proc->s (omap::lookup dst net)))
      (equal (proc->klst pdst) (proc->klst (omap::lookup dst net)))
      (equal (wtree-bind pdst) (wtree-bind (omap::lookup dst net)))
      (member-equal src
        (erl-val-cons->lst
          (omap::lookup 'ChildPids (wtree-bind (omap::lookup dst net)))))
      (or
        ; idle
        (not
          (and
            (omap::assoc 'CPids
              (erl-state->bind (proc->s (omap::lookup dst net))))
            (equal
              (erl-val-kind
                (omap::lookup 'CPids
                  (erl-state->bind
                    (proc->s (omap::lookup dst net)))))
              :cons)))
        ; blocked or receive
        (member-equal src
          (erl-val-cons->lst
            (omap::lookup 'CPids
              (erl-state->bind (proc->s (omap::lookup dst net)))))))
      (not (inbox-contains (proc->inbox-new (omap::lookup dst net)) src))
      (not (inbox-contains (proc->inbox-tried (omap::lookup dst net)) src))
      (or
        (and ; idle -> idle, or receive -> receive
          (equal (proc->ps pdst) (proc->ps (omap::lookup dst net)))
          (not (equal (proc->ps (omap::lookup dst net)) :blocked))
          (equal (proc->inbox-tried pdst)
                (proc->inbox-tried (omap::lookup dst net)))
          (equal (proc->inbox-new pdst)
                (append (proc->inbox-new (omap::lookup dst net))
                        (list m))))
        (and ; blocked -> receive
          (equal (proc->ps (omap::lookup dst net)) :blocked)
          (equal (proc->ps pdst) :receive)
          (null (proc->inbox-tried pdst))
          (equal (proc->inbox-new pdst)
                (append (proc->inbox-tried (omap::lookup dst net))
                        (proc->inbox-new (omap::lookup dst net))
                        (list m)))))
      ; message facts
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (car (erl-val-tuple->lst m)) src)
      (equal (cadr (erl-val-tuple->lst m))
             (erl-state->in (proc->s (omap::lookup src net)))))
    (inv dst (omap::update dst pdst net)))
  :use
    (inv-of-update-of-idle-dst-append
     inv-of-update-of-receiving-dst-append
     inv-of-update-of-receiver-unblock-1
     inv-of-update-of-receiver-unblock-2)))


; inv of src --------------------------------------------------------------------

(local (defruled inv-of-update-src
  (implies
    (and
      (network-p net) (inv src net)
      (omap::assoc src net)
      (pid-p src) (proc-p psrc)
      (network-p (omap::update src psrc net))
      (equal (erl-state->self (proc->s psrc)) src)
      (equal (erl-state->bind (proc->s psrc))
             (erl-state->bind (proc->s (omap::lookup src net))))
      (equal (erl-state->in (proc->s psrc))
             (erl-state->in (proc->s (omap::lookup src net))))
      (equal (proc->klst psrc) (proc->klst (omap::lookup src net)))
      (equal (wtree-bind psrc) (wtree-bind (omap::lookup src net)))
      (equal (proc->inbox-new psrc)
             (proc->inbox-new (omap::lookup src net)))
      (equal (proc->inbox-tried psrc)
             (proc->inbox-tried (omap::lookup src net)))
      ; sender is termiated
      (equal (proc->ps (omap::lookup src net)) :terminated)
      (equal (proc->ps psrc) :terminated)
      (sent-message-wf psrc (proc->outbox psrc)
        (omap::lookup 'Parent (wtree-bind psrc))
        (omap::update src psrc net)))
    (inv src (omap::update src psrc net)))
  :enable inv
  :use ((:instance leaf-root-p-when-bind-equal
          (p1 psrc) (p2 (omap::lookup src net)))
        (:instance wtree-nodes-are-leaf-or-root (pid src)))))


; inv of both updates -----------------------------------------------------------

; case where inbox-new of dst gets updated
(local (defrule inv-of-update-src-and-dst-inbox-new
  (implies
    (and
      (network-p net) (wtree-p net) (inv-all net)
      ; src facts, psrc is the proc after erl-step.
      (proc-p psrc) (omap::assoc src net)
      (equal (erl-state->self (proc->s psrc)) src)
      (equal (erl-state->bind (proc->s psrc))
             (erl-state->bind (proc->s (omap::lookup src net))))
      (equal (erl-state->in (proc->s psrc))
             (erl-state->in (proc->s (omap::lookup src net))))
      (equal (proc->klst psrc) (proc->klst (omap::lookup src net)))
      (equal (wtree-bind psrc) (wtree-bind (omap::lookup src net)))
      (equal (proc->inbox-new psrc) (proc->inbox-new (omap::lookup src net)))
      (equal (proc->inbox-tried psrc)
             (proc->inbox-tried (omap::lookup src net)))
      (equal (proc->ps psrc) :terminated)
      (outbox-emptyp (proc->outbox psrc)) (proc->outbox psrc)
      ; dst facts, pdst is the proc after erl-step.
      (proc-p pdst) (not (equal src dst))
      (omap::assoc dst (proc->outbox (omap::lookup src net)))
      (omap::lookup dst (proc->outbox (omap::lookup src net)))
      (equal (erl-state->self (proc->s pdst)) dst)
      (equal (proc->s pdst) (proc->s (omap::lookup dst net)))
      (equal (proc->klst pdst) (proc->klst (omap::lookup dst net)))
      (equal (wtree-bind pdst) (wtree-bind (omap::lookup dst net)))
      (equal (proc->ps pdst) (proc->ps (omap::lookup dst net)))
      (not (equal (proc->ps (omap::lookup dst net)) :blocked))
      (equal (proc->inbox-tried pdst)
             (proc->inbox-tried (omap::lookup dst net)))
      (equal (proc->inbox-new pdst)
             (append (proc->inbox-new (omap::lookup dst net))
                     (list (car (omap::lookup dst
                                  (proc->outbox (omap::lookup src net))))))))
    (inv src (omap::update src psrc (omap::update dst pdst net))))
  :enable (proc->pid proc->outbox)
  :disable
    (sender-with-message-props inv-of-inv-all
     not-terminated?-when-runnable-or-outbox
     inv-of-update-of-other-node inv-of-update-src
     inbox-contains-of-append-message
     inbox-contains-of-append-2
     sent-message-wf-when-parent-has-message)
  :use
    ((:instance sender-with-message-props)
     (:instance inv-of-inv-all (pid src))
     (:instance inv-of-inv-all (pid dst))
     (:instance not-terminated?-when-runnable-or-outbox
       (pid dst) (net (omap::update dst pdst net)))
     (:instance inv-of-update-of-other-node
      (pid src) (p dst) (proc pdst)
      (msgs
        (list (car (omap::lookup dst
                     (proc->outbox (omap::lookup src net)))))))
    (:instance inv-of-update-src (net (omap::update dst pdst net)))
    (:instance inbox-contains-of-append-message
      (l (proc->inbox-new (omap::lookup dst net))) (pid src)
      (m (car (omap::lookup dst (proc->outbox (omap::lookup src net))))))
    (:instance inbox-contains-of-append-2
      (pid src) (a (proc->inbox-tried (omap::lookup dst net)))
      (b (append (proc->inbox-new (omap::lookup dst net))
                 (list (car (omap::lookup dst
                              (proc->outbox (omap::lookup src net))))))))
    (:instance sent-message-wf-when-parent-has-message
      (self psrc) (outbox (proc->outbox psrc)) (parent dst)
      (net (omap::update src psrc (omap::update dst pdst net)))))))


; case where inbox-tried of dst gets updated
(local (defrule inv-of-update-src-and-dst-inbox-tried
  (implies
    (and
      (network-p net) (wtree-p net) (inv-all net)
      ; src facts, psrc is the proc after erl-step.
      (proc-p psrc) (omap::assoc src net)
      (equal (erl-state->self (proc->s psrc)) src)
      (equal (erl-state->bind (proc->s psrc))
             (erl-state->bind (proc->s (omap::lookup src net))))
      (equal (erl-state->in (proc->s psrc))
             (erl-state->in (proc->s (omap::lookup src net))))
      (equal (proc->klst psrc) (proc->klst (omap::lookup src net)))
      (equal (wtree-bind psrc) (wtree-bind (omap::lookup src net)))
      (equal (proc->inbox-new psrc) (proc->inbox-new (omap::lookup src net)))
      (equal (proc->inbox-tried psrc)
             (proc->inbox-tried (omap::lookup src net)))
      (equal (proc->ps psrc) :terminated)
      (outbox-emptyp (proc->outbox psrc)) (proc->outbox psrc)
      ; dst facts, pdst is the proc after erl-step.
      (proc-p pdst) (not (equal src dst))
      (omap::assoc dst (proc->outbox (omap::lookup src net)))
      (omap::lookup dst (proc->outbox (omap::lookup src net)))
      (equal (erl-state->self (proc->s pdst)) dst)
      (equal (proc->s pdst) (proc->s (omap::lookup dst net)))
      (equal (proc->klst pdst) (proc->klst (omap::lookup dst net)))
      (equal (wtree-bind pdst) (wtree-bind (omap::lookup dst net)))
      (equal (proc->ps (omap::lookup dst net)) :blocked)
      (equal (proc->ps pdst) :receive)
      (null (proc->inbox-tried pdst))
      (equal
        (proc->inbox-new pdst)
        (append (proc->inbox-tried (omap::lookup dst net))
                (proc->inbox-new (omap::lookup dst net))
                (list (car (omap::lookup dst
                              (proc->outbox (omap::lookup src net))))))))
    (inv src (omap::update src psrc (omap::update dst pdst net))))
  :enable (proc->pid proc->outbox)
  :disable
    (sender-with-message-props inv-of-inv-all
     not-terminated?-when-runnable-or-outbox
     inv-of-update-of-other-node inv-of-update-src
     inbox-contains-of-append-message
     inbox-contains-of-append-2
     sent-message-wf-when-parent-has-message)
  :use
    ((:instance sender-with-message-props)
     (:instance inv-of-inv-all (pid src))
     (:instance inv-of-inv-all (pid dst))
     (:instance not-terminated?-when-runnable-or-outbox
       (pid dst) (net (omap::update dst pdst net)))
     (:instance inv-of-update-of-other-node
       (pid src) (p dst) (proc pdst)
       (msgs
         (list (car (omap::lookup dst
                       (proc->outbox (omap::lookup src net)))))))
     (:instance inv-of-update-src
       (net (omap::update dst pdst net)))
     (:instance inbox-contains-of-append-message
       (l (proc->inbox-new (omap::lookup dst net))) (pid src)
       (m (car (omap::lookup dst (proc->outbox (omap::lookup src net))))))
     (:instance inbox-contains-of-append-2
       (a (proc->inbox-tried (omap::lookup dst net))) (pid src)
       (b (append (proc->inbox-new (omap::lookup dst net))
                  (list (car (omap::lookup dst
                               (proc->outbox (omap::lookup src net))))))))
     (:instance sent-message-wf-when-parent-has-message
       (self psrc) (outbox (proc->outbox psrc)) (parent dst)
       (net (omap::update src psrc (omap::update dst pdst net)))))))

; Helper for the next theorem
(local (defrule inv-of-inbox-of-non-empty-outbox
  (implies
    (and
      (network-p net) (inv dst net)
      (omap::assoc src net) (omap::assoc dst net)
      (not (outbox-emptyp (proc->outbox (omap::lookup src net))))
      (erl-val-cons->lst
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup dst net)))))
    (and (not (inbox-contains (proc->inbox-new (omap::lookup dst net)) src))
         (not (inbox-contains (proc->inbox-tried (omap::lookup dst net)) src))))
  :enable inv
  :expand ((inbox-contains nil src))
  :use ((:instance wtree-nodes-are-leaf-or-root (pid dst)))))


(local (defruled inv-of-dst-inbox-new
  (implies
    (and
      (network-p net) (wtree-p net) (inv-all net)
      ; src facts, psrc is the proc after erl-step.
      (proc-p psrc) (omap::assoc src net)
      (equal (erl-state->self (proc->s psrc)) src)
      (equal (erl-state->bind (proc->s psrc))
             (erl-state->bind (proc->s (omap::lookup src net))))
      (equal (erl-state->in (proc->s psrc))
             (erl-state->in (proc->s (omap::lookup src net))))
      (equal (proc->klst psrc) (proc->klst (omap::lookup src net)))
      (equal (wtree-bind psrc) (wtree-bind (omap::lookup src net)))
      (equal (proc->inbox-new psrc)
             (proc->inbox-new (omap::lookup src net)))
      (equal (proc->inbox-tried psrc)
             (proc->inbox-tried (omap::lookup src net)))
      (equal (proc->ps psrc) :terminated)
      (outbox-emptyp (proc->outbox psrc)) (proc->outbox psrc)
      (equal
        (erl-val-kind
          (erl-state->in (proc->s (omap::lookup src net))))
        :integer)
      ; dst facts, pdst is the proc after erl-step.
      (proc-p pdst) (not (equal src dst))
      (omap::assoc dst (proc->outbox (omap::lookup src net)))
      (omap::lookup dst (proc->outbox (omap::lookup src net)))
      (equal (erl-state->self (proc->s pdst)) dst)
      (equal (proc->s pdst) (proc->s (omap::lookup dst net)))
      (equal (proc->klst pdst) (proc->klst (omap::lookup dst net)))
      (equal (wtree-bind pdst) (wtree-bind (omap::lookup dst net)))
      (equal (proc->ps pdst) (proc->ps (omap::lookup dst net)))
      (not (equal (proc->ps (omap::lookup dst net)) :blocked))
      (equal (proc->inbox-tried pdst)
             (proc->inbox-tried (omap::lookup dst net)))
      (equal (proc->inbox-new pdst)
             (append (proc->inbox-new (omap::lookup dst net))
                     (list (car (omap::lookup dst
                                   (proc->outbox (omap::lookup src net))))))))
    (inv dst (omap::update dst pdst (omap::update src psrc net))))
  :enable (proc->pid check-parent)
  :disable
    (sender-with-message-props inv-of-update-of-other-node
     not-terminated?-when-runnable-or-outbox
     inv-of-inbox-of-non-empty-outbox inv-of-update-dst
     check-parent-of-wtree-p)
  :use
    ((:instance sender-with-message-props)
     (:instance inv-of-inv-all (pid dst))
     (:instance check-parent-of-wtree-p (pid src))
     (:instance not-terminated?-when-runnable-or-outbox
      (pid dst) (net (omap::update dst pdst (omap::update src psrc net))))
     (:instance not-terminated?-when-runnable-or-outbox
       (pid src) (net (omap::update src psrc net)))
     (:instance inv-of-update-of-other-node
       (pid dst) (p src) (proc psrc) (msgs nil))
     (:instance inv-of-inbox-of-non-empty-outbox)
     (:instance inv-of-update-dst
       (net (omap::update src psrc net))
       (m (car (omap::lookup dst
                  (proc->outbox (omap::lookup src net)))))))))

(local (defrule inv-of-dst-inbox-tried
  (implies
    (and
      (network-p net) (wtree-p net) (inv-all net)
      ; src facts, psrc is the proc after erl-step.
      (proc-p psrc) (omap::assoc src net)
      (equal (erl-state->self (proc->s psrc)) src)
      (equal (erl-state->bind (proc->s psrc))
             (erl-state->bind (proc->s (omap::lookup src net))))
      (equal (erl-state->in (proc->s psrc))
             (erl-state->in (proc->s (omap::lookup src net))))
      (equal (proc->klst psrc) (proc->klst (omap::lookup src net)))
      (equal (wtree-bind psrc) (wtree-bind (omap::lookup src net)))
      (equal (proc->inbox-new psrc)
             (proc->inbox-new (omap::lookup src net)))
      (equal (proc->inbox-tried psrc)
             (proc->inbox-tried (omap::lookup src net)))
      (equal (proc->ps psrc) :terminated)
      (outbox-emptyp (proc->outbox psrc)) (proc->outbox psrc)
      (equal
        (erl-val-kind
          (erl-state->in (proc->s (omap::lookup src net))))
        :integer)
      ; dst facts, pdst is the proc after erl-step.
      (proc-p pdst) (not (equal src dst))
      (omap::assoc dst (proc->outbox (omap::lookup src net)))
      (omap::lookup dst (proc->outbox (omap::lookup src net)))
      (equal (erl-state->self (proc->s pdst)) dst)
      (equal (proc->s pdst) (proc->s (omap::lookup dst net)))
      (equal (proc->klst pdst) (proc->klst (omap::lookup dst net)))
      (equal (wtree-bind pdst) (wtree-bind (omap::lookup dst net)))
      (equal (proc->ps (omap::lookup dst net)) :blocked)
      (equal (proc->ps pdst) :receive)
      (null (proc->inbox-tried pdst))
      (equal
        (proc->inbox-new pdst)
        (append (proc->inbox-tried (omap::lookup dst net))
                (proc->inbox-new (omap::lookup dst net))
                (list (car (omap::lookup dst
                              (proc->outbox (omap::lookup src net))))))))
    (inv dst (omap::update dst pdst (omap::update src psrc net))))
  :enable (proc->pid check-parent)
  :disable
    (sender-with-message-props inv-of-update-of-other-node
     not-terminated?-when-runnable-or-outbox
     inv-of-inbox-of-non-empty-outbox inv-of-update-dst
     check-parent-of-wtree-p)
  :use ((:instance sender-with-message-props)
        (:instance inv-of-inv-all (pid dst))
        (:instance check-parent-of-wtree-p (pid src))
        (:instance not-terminated?-when-runnable-or-outbox
          (pid dst) (net (omap::update dst pdst (omap::update src psrc net))))
        (:instance not-terminated?-when-runnable-or-outbox
          (pid src) (net (omap::update src psrc net)))
        (:instance inv-of-update-of-other-node
          (pid dst) (p src) (proc psrc) (msgs nil))
        (:instance inv-of-inbox-of-non-empty-outbox)
        (:instance inv-of-update-dst
          (net (omap::update src psrc net))
          (m (car (omap::lookup dst
                    (proc->outbox (omap::lookup src net)))))))))

; Other nodes are unchanged
(local (defrule inv-of-other-nodes
  (implies
    (and
      (network-p net) (wtree-p net) (inv-all net)
      (omap::assoc pid net)
      (not (equal pid src)) (not (equal pid dst))
      ; src facts
      (proc-p psrc) (omap::assoc src net)
      (equal (erl-state->self (proc->s psrc)) src)
      (equal (erl-state->bind (proc->s psrc))
             (erl-state->bind (proc->s (omap::lookup src net))))
      (equal (erl-state->in (proc->s psrc))
             (erl-state->in (proc->s (omap::lookup src net))))
      (equal (proc->klst psrc) (proc->klst (omap::lookup src net)))
      (equal (wtree-bind psrc) (wtree-bind (omap::lookup src net)))
      (equal (proc->inbox-new psrc)
             (proc->inbox-new (omap::lookup src net)))
      (equal (proc->inbox-tried psrc)
             (proc->inbox-tried (omap::lookup src net)))
      (equal (proc->ps psrc) :terminated)
      (outbox-emptyp (proc->outbox psrc)) (proc->outbox psrc)
      ; dst facts
      (proc-p pdst) (not (equal src dst))
      (omap::assoc dst (proc->outbox (omap::lookup src net)))
      (omap::lookup dst (proc->outbox (omap::lookup src net)))
      (equal (erl-state->self (proc->s pdst)) dst)
      (equal (proc->s pdst) (proc->s (omap::lookup dst net)))
      (equal (proc->klst pdst) (proc->klst (omap::lookup dst net)))
      (equal (wtree-bind pdst) (wtree-bind (omap::lookup dst net)))
      (or
        (and ; idle -> idle, or receive -> receive
          (equal (proc->ps pdst) (proc->ps (omap::lookup dst net)))
          (not (equal (proc->ps (omap::lookup dst net)) :blocked))
          (equal (proc->inbox-tried pdst)
                 (proc->inbox-tried (omap::lookup dst net)))
          (equal
            (proc->inbox-new pdst)
            (append (proc->inbox-new (omap::lookup dst net))
                    (list (car (omap::lookup dst
                                (proc->outbox (omap::lookup src net))))))))
        (and ; blocked -> receive
          (equal (proc->ps (omap::lookup dst net)) :blocked)
          (equal (proc->ps pdst) :receive)
          (null (proc->inbox-tried pdst))
          (equal
            (proc->inbox-new pdst)
            (append (proc->inbox-tried (omap::lookup dst net))
                    (proc->inbox-new (omap::lookup dst net))
                    (list (car (omap::lookup dst
                                  (proc->outbox (omap::lookup src net))))))))))
    (inv pid (omap::update dst pdst (omap::update src psrc net))))
  :enable (proc->pid proc->outbox)
  :disable
    (sender-with-message-props inv-of-update-of-other-node
     not-terminated?-when-runnable-or-outbox
     inv-of-update-of-other-node)
  :use ((:instance sender-with-message-props)
        (:instance inv-of-inv-all)
        (:instance not-terminated?-when-runnable-or-outbox
          (pid src) (net (omap::update src psrc net)))
        (:instance not-terminated?-when-runnable-or-outbox
          (pid dst) (net (omap::update dst pdst (omap::update src psrc net))))
        (:instance inv-of-update-of-other-node
          (p src) (proc psrc) (msgs nil))
        (:instance inv-of-update-of-other-node
          (p dst) (proc pdst) (net (omap::update src psrc net))
          (msgs (list (car (omap::lookup dst (proc->outbox (omap::lookup src net))))))))))

; All nodes, including src and dst, for dst idle -> idle, or receive -> receive
(local (defrule inv-of-deliver-of-not-blocked
  (implies
    (and
      (network-p net) (wtree-p net) (inv-all net)
      ; src facts
      (omap::assoc src net) (proc-p psrc)
      (equal (erl-state->self (proc->s psrc)) src)
      (equal (erl-state->bind (proc->s psrc))
             (erl-state->bind (proc->s (omap::lookup src net))))
      (equal (erl-state->in (proc->s psrc))
             (erl-state->in (proc->s (omap::lookup src net))))
      (equal (proc->klst psrc) (proc->klst (omap::lookup src net)))
      (equal (wtree-bind psrc) (wtree-bind (omap::lookup src net)))
      (equal (proc->inbox-new psrc)
             (proc->inbox-new (omap::lookup src net)))
      (equal (proc->inbox-tried psrc)
             (proc->inbox-tried (omap::lookup src net)))
      (equal (proc->ps psrc) :terminated)
      (outbox-emptyp (proc->outbox psrc)) (proc->outbox psrc)
      ; dst facts
      (not (equal src dst)) (proc-p pdst)
      (omap::assoc dst (proc->outbox (omap::lookup src net)))
      (omap::lookup dst (proc->outbox (omap::lookup src net)))
      (not (equal (proc->ps (omap::lookup dst net)) :blocked))
      (equal (erl-state->self (proc->s pdst)) dst)
      (equal (proc->s pdst) (proc->s (omap::lookup dst net)))
      (equal (proc->klst pdst) (proc->klst (omap::lookup dst net)))
      (equal (wtree-bind pdst) (wtree-bind (omap::lookup dst net)))
      (equal (proc->ps pdst) (proc->ps (omap::lookup dst net)))
      (equal (proc->inbox-tried pdst)
             (proc->inbox-tried (omap::lookup dst net)))
      (equal
        (proc->inbox-new pdst)
        (append (proc->inbox-new (omap::lookup dst net))
                (list (car (omap::lookup dst
                             (proc->outbox (omap::lookup src net)))))))
      (omap::assoc pid
        (omap::update src psrc (omap::update dst pdst net))))
    (inv pid (omap::update src psrc (omap::update dst pdst net))))
  :disable
    (sender-with-message-props inv-of-update-src-and-dst-inbox-new
     inv-of-update-src-and-dst-inbox-tried inv-of-dst-inbox-new
     inv-of-dst-inbox-tried wtree-nodes-are-leaf-or-root inv-of-other-nodes)
  :use ((:instance sender-with-message-props)
        (:instance inv-of-update-src-and-dst-inbox-new)
        (:instance inv-of-update-src-and-dst-inbox-tried)
        (:instance inv-of-dst-inbox-new)
        (:instance inv-of-dst-inbox-tried)
        (:instance wtree-nodes-are-leaf-or-root (pid src))
        (:instance inv-of-other-nodes))))

; All nodes, including src and dst, for dst blocked -> receive
(local (defrule inv-of-deliver-of-blocked
  (implies
    (and
      (network-p net) (wtree-p net) (inv-all net)
      ; src facts
      (omap::assoc src net) (proc-p psrc)
      (equal (erl-state->self (proc->s psrc)) src)
      (equal (erl-state->bind (proc->s psrc))
             (erl-state->bind (proc->s (omap::lookup src net))))
      (equal (erl-state->in (proc->s psrc))
             (erl-state->in (proc->s (omap::lookup src net))))
      (equal (proc->klst psrc) (proc->klst (omap::lookup src net)))
      (equal (wtree-bind psrc) (wtree-bind (omap::lookup src net)))
      (equal (proc->inbox-new psrc)
             (proc->inbox-new (omap::lookup src net)))
      (equal (proc->inbox-tried psrc)
             (proc->inbox-tried (omap::lookup src net)))
      (equal (proc->ps psrc) :terminated)
      (outbox-emptyp (proc->outbox psrc)) (proc->outbox psrc)
      ; dst facts
      (not (equal src dst)) (proc-p pdst)
      (omap::assoc dst (proc->outbox (omap::lookup src net)))
      (omap::lookup dst (proc->outbox (omap::lookup src net)))
      (equal (proc->ps (omap::lookup dst net)) :blocked)
      (equal (erl-state->self (proc->s pdst)) dst)
      (equal (proc->s pdst) (proc->s (omap::lookup dst net)))
      (equal (proc->klst pdst) (proc->klst (omap::lookup dst net)))
      (equal (wtree-bind pdst) (wtree-bind (omap::lookup dst net)))
      (equal (proc->ps pdst) :receive)
      (null (proc->inbox-tried pdst))
      (equal
        (proc->inbox-new pdst)
        (append (proc->inbox-tried (omap::lookup dst net))
                (proc->inbox-new (omap::lookup dst net))
                (list (car (omap::lookup dst
                            (proc->outbox (omap::lookup src net)))))))
      (omap::assoc pid
        (omap::update src psrc (omap::update dst pdst net))))
    (inv pid (omap::update src psrc (omap::update dst pdst net))))
  :disable
    (sender-with-message-props inv-of-update-src-and-dst-inbox-new
     inv-of-update-src-and-dst-inbox-tried inv-of-dst-inbox-new
     inv-of-dst-inbox-tried wtree-nodes-are-leaf-or-root inv-of-other-nodes)
  :use ((:instance sender-with-message-props)
        (:instance inv-of-update-src-and-dst-inbox-new)
        (:instance inv-of-update-src-and-dst-inbox-tried)
        (:instance inv-of-dst-inbox-new)
        (:instance inv-of-dst-inbox-tried)
        (:instance wtree-nodes-are-leaf-or-root (pid src))
        (:instance inv-of-other-nodes))))

; inv of deliver ---------------------------------------------------------------

; This is all we really want from this file.
(defrule inv-of-erl-step-of-deliver
  (implies
    (and
      (network-p net) (inv-all net)
      (not (terminated? net))
      (equal (scheduling-kind (schedule net)) :deliver)
      (omap::assoc pid (erl-step net)))
    (inv pid (erl-step net)))
  :enable (erl-step proc->pid proc->outbox
           has-message-for-dst? proc-has-message-for-dst?)
  :use ((:instance scheduler-correct-when-deliver)
        (:instance wtree-p-of-inv
          (pid (scheduling-deliver->p1 (schedule net))))
        (:instance sender-with-message-props
          (src (scheduling-deliver->p1 (schedule net)))
          (dst (scheduling-deliver->p2 (schedule net))))))