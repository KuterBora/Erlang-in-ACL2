(in-package "ACL2")
(include-book "inv")

; Show that reduce causes no deadlocks.

; Some helpers functions
(local (define node-index (pid net)
  :returns (n natp :rule-classes :type-prescription)
  :verify-guards nil
  (nfix (erl-val-integer->val
          (omap::lookup 'Index (wtree-bind (omap::lookup pid net)))))))

(local (define max-index ((net network-p))
  :returns (n natp :rule-classes :type-prescription)
  :measure (acl2-count (network-fix net))
  :verify-guards nil
  (b* ((net (network-fix net))
       ((if (omap::emptyp net)) 0))
      (max (nfix (erl-val-integer->val
                   (omap::lookup 'Index
                     (wtree-bind (omap::head-val net)))))
           (max-index (omap::tail net))))
  ///
    (defcong network-equiv equal (max-index net) 1)
    (defrule node-index-<=-max-index
      (implies
        (and (network-p net) (pid-p pid) (omap::assoc pid net))
        (<= (node-index pid net) (max-index net)))
      :rule-classes :linear
      :enable (node-index omap::lookup))))


; Some helper rules
(local (defrule ps-of-terminated-network
  (implies
    (and (network-p net) (pid-p pid)
         (omap::assoc pid net) (terminated? net))
    (and (not (equal (proc->ps (omap::lookup pid net)) :idle))
         (not (equal (proc->ps (omap::lookup pid net)) :receive))
         (not (proc->outbox (omap::lookup pid net)))))
  :enable (terminated? omap::lookup)))

(local (defrule member-equal-of-prefixp
  (implies (and (prefixp x y) (member-equal e x))
           (member-equal e y))
  :enable prefixp))

(local (defrule member-equal-of-rev-prefixp
  (implies (and (prefixp (rev l2) (rev l1)) (member-equal e l2))
           (member-equal e l1))
  :use ((:instance member-equal-of-prefixp
          (x (rev l2)) (y (rev l1))))))

(local (defruled parent-of-member-of-check-children
  (implies
    (and (network-p net) (pid-p pid) (pid-lst-p children)
         (member-equal cpid children)
         (check-children pid children net))
    (and (omap::assoc cpid net)
         (leaf-p (omap::lookup cpid net))
         (equal (omap::lookup 'Parent
                  (wtree-bind (omap::lookup cpid net)))
                pid)))
  :enable check-children
  :induct (check-children pid children net)))

(local (defrule inv-blocked-node-props
  (implies
    (and
      (inv pid net)
      (network-p net) (pid-p pid) (omap::assoc pid net)
      (or (leaf-p (omap::lookup pid net))
          (root-p (omap::lookup pid net)))
      (equal (proc->ps (omap::lookup pid net)) :blocked))
    (b* ((proc (omap::lookup pid net))
         (bind (erl-state->bind (proc->s proc)))
         (wbind (wtree-bind proc))
         (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
         (index (erl-val-integer->val (omap::lookup 'Index wbind)))
         (cps (erl-val-cons->lst (omap::lookup 'CPids bind)))
         (chd (omap::lookup 'ChildHd bind)))
      (and
        (omap::assoc 'CPids bind)
        (equal
          (erl-val-kind
            (omap::lookup 'CPids bind)) :cons)
        (consp cps)
        (equal chd (car cps))
        (prefixp (rev cps) (rev children))
        (omap::assoc chd net)
        (leaf-p (omap::lookup chd net))
        (< index
           (erl-val-integer->val
             (omap::lookup 'Index
               (wtree-bind (omap::lookup chd net)))))
        (null (proc->inbox-new proc))
        (not (inbox-contains (proc->inbox-tried proc) chd)))))
  :expand ((inv pid net))))

(local (defrule inv-blocked-node-child-props
  (implies
    (and
      (inv-all net) (network-p net)
      (pid-p pid) (omap::assoc pid net)
      (equal (proc->ps (omap::lookup pid net)) :blocked))
    (b* ((proc (omap::lookup pid net))
         (bind (erl-state->bind (proc->s proc)))
         (chd (omap::lookup 'ChildHd bind)))
      (and
        (pid-p chd)
        (omap::assoc chd net)
        (leaf-p (omap::lookup chd net))
        (equal (omap::lookup 'Parent
                 (wtree-bind (omap::lookup chd net))) pid)
        (omap::assoc 'CPids bind)
        (equal (erl-val-kind (omap::lookup 'CPids bind))
               :cons)
        (member-equal chd
          (erl-val-cons->lst (omap::lookup 'CPids bind)))
        (null (proc->inbox-new proc))
        (not (inbox-contains (proc->inbox-tried proc) chd))
        (< (node-index pid net) (node-index chd net)))))
  :enable node-index
  :disable wtree-p-of-inv
  :use
    ((:instance inv-of-inv-all)
     (:instance inv-blocked-node-props)
     (:instance wtree-nodes-are-leaf-or-root)
     (:instance wtree-p-of-inv)
     (:instance parent-of-member-of-check-children
       (cpid (omap::lookup 'ChildHd
               (erl-state->bind (proc->s (omap::lookup pid net)))))
       (children (erl-val-cons->lst
                   (omap::lookup 'ChildPids
                     (wtree-bind (omap::lookup pid net)))))))))

(local (defruled inv-terminated-node-sent-message-wf
  (implies
    (and
      (network-p net) (pid-p pid) (omap::assoc pid net)
      (or (leaf-p (omap::lookup pid net))
          (root-p (omap::lookup pid net)))
      (equal (proc->ps (omap::lookup pid net)) :terminated)
      (inv pid net))
    (sent-message-wf
      (omap::lookup pid net)
      (proc->outbox (omap::lookup pid net))
      (omap::lookup 'Parent 
        (wtree-bind (omap::lookup pid net)))
      net))
  :do-not-induct t
  :expand ((inv pid net))))

(local (defrule blocked-child-not-terminated
  (implies
    (and
      (network-p net) (pid-p pid) (pid-p chd)
      (omap::assoc pid net) (omap::assoc chd net)
      (equal (proc->ps (omap::lookup pid net)) :blocked)
      (equal (omap::lookup 'Parent
               (wtree-bind (omap::lookup chd net))) pid)
      (omap::assoc 'CPids
        (erl-state->bind (proc->s (omap::lookup pid net))))
      (equal
        (erl-val-kind
          (omap::lookup 'CPids
            (erl-state->bind (proc->s (omap::lookup pid net)))))
        :cons)
      (member-equal chd
        (erl-val-cons->lst
          (omap::lookup 'CPids
            (erl-state->bind
              (proc->s (omap::lookup pid net))))))
      (null (proc->inbox-new (omap::lookup pid net)))
      (not (inbox-contains
            (proc->inbox-tried (omap::lookup pid net))
            chd))
      (not (proc->outbox (omap::lookup chd net)))
      (or (leaf-p (omap::lookup chd net))
          (root-p (omap::lookup chd net)))
      (inv chd net))
    (not (equal (proc->ps (omap::lookup chd net)) :terminated)))
  :enable sent-message-wf
  :expand ((inbox-contains nil chd))
  :use ((:instance inv-terminated-node-sent-message-wf (pid chd)))))

(local (defruled proc-state-cases
  (implies (proc-p p)
    (or (equal (proc->ps p) :idle)
        (equal (proc->ps p) :terminated)
        (equal (proc->ps p) :receive)
        (equal (proc->ps p) :blocked)))
  :enable proc-state-p))

(local (defrule blocked-node-has-blocked-child-when-terminated
  (implies
    (and
      (network-p net) (inv-all net) (terminated? net)
      (pid-p pid) (omap::assoc pid net)
      (equal (proc->ps (omap::lookup pid net)) :blocked))
    (b* ((chd (omap::lookup 'ChildHd
                (erl-state->bind (proc->s (omap::lookup pid net))))))
      (and
        (pid-p chd)
        (omap::assoc chd net)
        (equal (proc->ps (omap::lookup chd net)) :blocked)
        (< (node-index pid net) (node-index chd net)))))
  :use ((:instance inv-blocked-node-child-props)
        (:instance inv-of-inv-all
          (pid (omap::lookup 'ChildHd
                 (erl-state->bind (proc->s (omap::lookup pid net))))))
        (:instance proc-state-cases
          (p (omap::lookup
               (omap::lookup 'ChildHd
                 (erl-state->bind (proc->s (omap::lookup pid net))))
               net))))))

(local (defrule no-blocked-node-when-terminated
  (implies
    (and
      (network-p net) (inv-all net) (terminated? net)
      (pid-p pid) (omap::assoc pid net))
    (not (equal (proc->ps (omap::lookup pid net)) :blocked)))
  :induct (index-induct pid net)
  :enable blocked-node-has-blocked-child-when-terminated
  :prep-lemmas
    ((define index-induct (pid net)
      :enabled t
      :irrelevant-formals-ok t
      :ignore-ok t
      :verify-guards nil
      :measure (nfix (- (max-index net) (node-index pid net)))
      (b* ((chd (omap::lookup 'ChildHd
                  (erl-state->bind (proc->s (omap::lookup pid net)))))
          ((unless (pid-p chd)) net)
          ((unless (< (node-index pid net) (node-index chd net))) net)
          ((unless (<= (node-index chd net) (max-index net))) net))
          (index-induct chd net))))))

; Finally:
(defrule terminated-of-inv
  (implies
    (and
      (inv-all net) (terminated? net) (network-p net)
      (pid-p pid) (omap::assoc pid net))
    (equal (proc->ps (omap::lookup pid net)) :terminated))
  :do-not-induct t
  :use ((:instance no-blocked-node-when-terminated)
        (:instance ps-of-terminated-network)
        (:instance proc-state-cases (p (omap::lookup pid net)))))
