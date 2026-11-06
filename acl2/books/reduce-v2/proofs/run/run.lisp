; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "../inv")
(local (include-book "run-idle-to-terminated"))
(local (include-book "run-idle-to-receive"))
(local (include-book "run-receive-to-blocked"))
(local (include-book "run-receive-to-receive"))
(local (include-book "run-receive-to-terminated"))

; Inv of Run -------------------------------------------------------------------

; BOZO: It is expesnive to expand inv, it causes way too many big subgoals.
; A temporary solution is the following lemmas.

(local (defruled run-idle-props
  (b* ((pp (omap::lookup p net))
       (wbind (wtree-bind pp))
       (parent (omap::lookup 'Parent wbind))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (ns (apply-k (proc->s pp) (proc->klst pp))))
  (implies
    (and
      (network-p net) (inv-all net)
      (pid-p p) (omap::assoc p net)
      (equal (proc->ps pp) :idle)
      (or (pid-p parent) (equal parent (make-erl-val-atom :val 'none)))
      (natp (erl-val-integer->val (omap::lookup 'Index wbind)))
      (pid-lst-p children))
    (and (equal (equal (erl-val-kind (erl-state->in ns)) :receive)
                (consp children))
         (implies (consp children)
                  (erl-klst-p (erl-val-receive->klst (erl-state->in ns)))))))
  :expand (inv p net)
  :disable inv-of-inv-all
  :use (:instance inv-of-inv-all (pid p))))

(local (defruled terminated-props
  (b* ((cp (omap::lookup c net))
       (r (rightmost-child c net))
       (ci (erl-val-integer->val (omap::lookup 'Index (wtree-bind cp))))
       (ri (erl-val-integer->val
             (omap::lookup 'Index (wtree-bind (omap::lookup r net))))))
  (implies
    (and (network-p net) (pid-p c) (inv c net)
         (equal (proc->ps cp) :terminated)
         (leaf-p cp))
    (and (natp ci) (natp ri) (<= ci ri)
         (equal (erl-val-integer->val (erl-state->in (proc->s cp)))
                (sum-range ci ri)))))
  :expand (inv c net)))

(local (defruled run-receive-props
  (b* ((pp (omap::lookup p net)))
  (implies
    (and
      (network-p net) (pid-p p) (inv p net)
      (equal (proc->ps pp) :receive)
      (not (equal (omap::lookup 'Parent (wtree-bind pp)) p)))
    (receiving-proc-p p pp net)))
  :expand (inv p net)))

(local (defruled run-receive-bind-props
  (b* ((pp (omap::lookup p net))
       (bind (erl-state->bind (proc->s pp)))
       (wbind (wtree-bind pp))
       (parent (omap::lookup 'Parent wbind))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind))))
  (implies
    (and
      (network-p net)
      (pid-p p) (omap::assoc p net)
      (receiving-proc-p p pp net)
      (or (pid-p parent) (equal parent (make-erl-val-atom :val 'none)))
      (pid-lst-p children))
    (and (pid-p (omap::lookup 'ChildHd bind))
         (pid-lst-p (erl-val-cons->lst (omap::lookup 'ChildTl bind)))
         (wf-inbox-p (proc->inbox-new pp))
         (or (equal (erl-val-kind (omap::lookup 'ParentPid bind)) :pid)
             (equal (omap::lookup 'ParentPid bind) (make-erl-val-atom :val 'none))))))
  :enable (remaining-children remaining-children-p)
  :use ((:instance pid-lst-crock
          (l2 (remaining-children (erl-state->bind (proc->s (omap::lookup p net)))))
          (l1 (erl-val-cons->lst
                (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))))))

(local (defruled run-receive-match-props
  (b* ((pp (omap::lookup p net))
       (bind (erl-state->bind (proc->s pp)))
       (wbind (wtree-bind pp))
       (index (erl-val-integer->val (omap::lookup 'Index wbind)))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (chd (omap::lookup 'ChildHd bind))
       (ctl (erl-val-cons->lst (omap::lookup 'ChildTl bind)))
       (c2 (car ctl))
       (inbox (proc->inbox-new pp)))
  (implies
    (and
      (network-p net) (inv-all net) (wtree-p net)
      (pid-p p) (omap::assoc p net)
      (equal (proc->ps pp) :receive)
      (receiving-proc-p p pp net)
      (natp index)
      (pid-lst-p children)
      (inbox-contains inbox chd)
      (consp ctl))
    (and
      (not (member-equal chd ctl))
      (omap::assoc c2 net)
      (leaf-p (omap::lookup c2 net))
      (not (equal c2 p))
      (< index (erl-val-integer->val
                 (omap::lookup 'Index (wtree-bind (omap::lookup c2 net)))))
      (equal (+ (erl-val-integer->val (omap::lookup 'LeftTotal bind))
                (erl-val-integer->val (inbox->value inbox chd)))
             (sum-range index
               (1- (erl-val-integer->val
                     (omap::lookup 'Index
                       (wtree-bind (omap::lookup c2 net))))))))))
  :enable remaining-children-p
  :disable (wtree-bind0-of-reduce-receive-klst-p sum-range-consequitve-2)
  :use ((:instance chd-not-in-ctl)
        (:instance sum-range-consequitve-2
          (i (erl-val-integer->val
               (omap::lookup 'Index (wtree-bind (omap::lookup p net)))))
          (j (erl-val-integer->val
               (omap::lookup 'Index
                 (wtree-bind
                   (omap::lookup
                     (omap::lookup 'ChildHd
                       (erl-state->bind (proc->s (omap::lookup p net))))
                     net)))))
          (n (erl-val-integer->val
               (omap::lookup 'Index
                 (wtree-bind
                   (omap::lookup
                     (rightmost-child
                       (omap::lookup 'ChildHd
                         (erl-state->bind (proc->s (omap::lookup p net))))
                       net)
                     net))))))
        (:instance terminated-props
          (c (omap::lookup 'ChildHd
               (erl-state->bind (proc->s (omap::lookup p net))))))
        (:instance check-indices-next-child
          (i (erl-val-integer->val
               (omap::lookup 'Index (wtree-bind (omap::lookup p net)))))
          (children (erl-val-cons->lst
                      (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))
          (cps (remaining-children
                 (erl-state->bind (proc->s (omap::lookup p net)))))))))

(local (defruled run-receive-to-terminated-props-1
  (b* ((pp (omap::lookup p net))
       (bind (erl-state->bind (proc->s pp)))
       (wbind (wtree-bind pp))
       (index (erl-val-integer->val (omap::lookup 'Index wbind)))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (chd (omap::lookup 'ChildHd bind))
       (ctl (erl-val-cons->lst (omap::lookup 'ChildTl bind)))
       (r (rightmost-child p net))
       (ri (erl-val-integer->val
             (omap::lookup 'Index (wtree-bind (omap::lookup r net)))))
       (inbox (proc->inbox-new pp)))
  (implies
    (and
      (network-p net) (inv-all net) (wtree-p net)
      (pid-p p) (omap::assoc p net)
      (equal (proc->ps pp) :receive)
      (receiving-proc-p p pp net)
      (natp index)
      (pid-lst-p children)
      (pid-p chd)
      (inbox-contains inbox chd)
      (not (consp ctl)))
    (and
      (omap::assoc r net)
      (leaf-p (omap::lookup r net))
      (<= index ri)
      (equal (+ (erl-val-integer->val (omap::lookup 'LeftTotal bind))
                (erl-val-integer->val (inbox->value inbox chd)))
             (sum-range index ri)))))
  :enable (remaining-children-p remaining-children)
  :disable (wtree-bind0-of-reduce-receive-klst-p
            sum-range-consequitve-2)
  :use ((:instance last-of-singleton-suffix
          (chd (omap::lookup 'ChildHd
                 (erl-state->bind (proc->s (omap::lookup p net)))))
          (children (erl-val-cons->lst
                      (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))))
        (:instance rightmost-child-of-last-child)
        (:instance sum-range-consequitve-2
          (i (erl-val-integer->val
               (omap::lookup 'Index (wtree-bind (omap::lookup p net)))))
          (j (erl-val-integer->val
               (omap::lookup 'Index
                 (wtree-bind
                   (omap::lookup
                     (omap::lookup 'ChildHd
                       (erl-state->bind (proc->s (omap::lookup p net))))
                     net)))))
          (n (erl-val-integer->val
               (omap::lookup 'Index
                 (wtree-bind
                   (omap::lookup
                     (rightmost-child
                       (omap::lookup 'ChildHd
                         (erl-state->bind (proc->s (omap::lookup p net))))
                       net)
                     net))))))
        (:instance terminated-props
          (c (omap::lookup 'ChildHd
               (erl-state->bind (proc->s (omap::lookup p net))))))
        (:instance node-p-of-rightmost-child (pid p))
        (:instance rightmost-child-of-wtree-node (pid p)))
  :prep-lemmas
    ((defruled last-of-singleton-suffix
       (implies
         (and (prefixp (rev (list chd)) (rev children)) (consp children))
         (equal (car (last children)) chd))
       :enable prefixp
       :use ((:instance car-of-rev-is-car-of-last (l children)))
       :prep-lemmas
         ((defruled car-of-rev-is-car-of-last
            (equal (car (rev l)) (car (last l)))
            :enable rev))))))

(local (defruled run-receive-to-terminated-props-2
  (b* ((pp (omap::lookup p net))
       (chd (omap::lookup 'ChildHd (erl-state->bind (proc->s pp)))))
  (implies
    (and (network-p net) (omap::assoc p net)
         (receiving-proc-p p pp net)
         (equal (proc->ps pp) :receive)
         (pid-p chd)
         (inbox-contains (proc->inbox-new pp) chd))
    (and (equal (proc->ps (omap::lookup chd net)) :terminated)
         (outbox-emptyp (proc->outbox (omap::lookup chd net)))
         (implies (not (consp (erl-val-cons->lst
                                (omap::lookup 'ChildTl
                                  (erl-state->bind (proc->s pp))))))
                  (not (inbox-without (proc->inbox-new pp) chd))))))
  :enable (remaining-children-p remaining-children)
  :disable (wtree-bind0-of-reduce-receive-klst-p)))

; receive -> blocked
(local (defruled inv-of-run-receive-no-match
  (b* ((pp (omap::lookup p net))
       (bind (erl-state->bind (proc->s pp)))
       (wbind (wtree-bind pp))
       (qp (omap::lookup pid net))
       (qparent (omap::lookup 'Parent (wtree-bind qp))))
  (implies
    (and
      (network-p net) (inv-all net)
      (pid-p p) (omap::assoc p net)
      (pid-p pid) (omap::assoc pid net)
      (equal (proc->ps pp) :receive)
      (receiving-proc-p p pp net)
      (not (equal (omap::lookup 'Parent wbind) p))
      (pid-lst-p (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
      (pid-p (omap::lookup 'ChildHd bind))
      (wf-inbox-p (proc->inbox-new pp))
      (not (inbox-contains (proc->inbox-new pp) (omap::lookup 'ChildHd bind)))
      (erl-val-p qparent)
      (or (not (equal (proc->ps qp) :terminated))
          (sent-message-wf qp (proc->outbox qp) qparent net))
      (or (equal (proc->ps qp) :terminated)
          (parent-still-waiting-p pid qparent net)))
    (inv pid (omap::update p (proc-receive pp) net))))
  :enable (remaining-children-p proc-receive-when-no-match)
  :disable (wtree-bind0-of-reduce-receive-klst-p)
  :use ((:instance inv-of-run-receive-to-blocked))))

; receive -> blocked / receive / terminated
(local (defruled inv-of-run-receive-all-cases
  (b* ((pp (omap::lookup p net))
       (bind (erl-state->bind (proc->s pp)))
       (wbind (wtree-bind pp))
       (parent (omap::lookup 'Parent wbind))
       (index (erl-val-integer->val (omap::lookup 'Index wbind)))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (chd (omap::lookup 'ChildHd bind))
       (ctl (erl-val-cons->lst (omap::lookup 'ChildTl bind)))
       (inbox (proc->inbox-new pp))
       (qp (omap::lookup pid net))
       (qparent (omap::lookup 'Parent (wtree-bind qp))))
  (implies
    (and
      (network-p net) (inv-all net) (wtree-p net)
      (pid-p p) (omap::assoc p net)
      (pid-p pid) (omap::assoc pid net)
      (equal (proc->ps pp) :receive)
      (receiving-proc-p p pp net)
      (or (pid-p parent) (equal parent (make-erl-val-atom :val 'none)))
      (not (equal parent p))
      (natp index)
      (pid-lst-p children)
      (pid-p chd)
      (pid-lst-p ctl)
      (wf-inbox-p inbox)
      (or (equal (erl-val-kind (omap::lookup 'ParentPid bind)) :pid)
          (equal (omap::lookup 'ParentPid bind) (make-erl-val-atom :val 'none)))
      (erl-val-p qparent)
      (or (not (equal (proc->ps qp) :terminated))
          (sent-message-wf qp (proc->outbox qp) qparent net))
      (or (equal (proc->ps qp) :terminated)
          (parent-still-waiting-p pid qparent net)))
    (inv pid (omap::update p (proc-receive pp) net))))
  :cases ((not (inbox-contains (proc->inbox-new (omap::lookup p net))
                 (omap::lookup 'ChildHd
                   (erl-state->bind (proc->s (omap::lookup p net))))))
          (consp (erl-val-cons->lst
                   (omap::lookup 'ChildTl
                     (erl-state->bind (proc->s (omap::lookup p net)))))))
  :disable (receiving-proc-p inv)
  :use ((:instance inv-of-run-receive-no-match)
        (:instance run-receive-to-terminated-props-2)
        (:instance run-receive-match-props)
        (:instance run-receive-to-terminated-props-1)
        (:instance inv-of-run-receive-to-receive)
        (:instance inv-of-run-receive-to-terminated))))

; inv of run --------------------------------------------------------------------

(local (defruled inv-of-run-props
  (b* ((qp (omap::lookup pid net))
       (qparent (omap::lookup 'Parent (wtree-bind qp))))
    (implies
      (and (network-p net) (pid-p pid) (inv pid net))
      (and
        (or (not (equal (proc->ps qp) :terminated))
            (sent-message-wf qp (proc->outbox qp) qparent net))
        (or (equal (proc->ps qp) :terminated)
            (parent-still-waiting-p pid qparent net)))))
  :expand (inv pid net)))

; receive -> any, for every node: the facts from inv-all.
(local (defruled inv-of-run-receive
  (implies
    (and
      (network-p net) (inv-all net)
      (pid-p p) (omap::assoc p net) (omap::assoc pid net)
      (equal (proc->ps (omap::lookup p net)) :receive))
    (inv pid (omap::update p (proc-receive (omap::lookup p net)) net)))
  :disable (receiving-proc-p inv inv-of-inv-all)
  :use ((:instance inv-of-inv-all (pid p))
        (:instance inv-of-inv-all)
        (:instance wtree-node-props)
        (:instance inv-of-run-props)
        (:instance run-receive-props)
        (:instance run-receive-bind-props)
        (:instance inv-of-run-receive-all-cases))))

(defrule inv-of-erl-step-of-run
  (implies
    (and
      (network-p net) (inv-all net) (not (terminated? net))
      (equal (scheduling-kind (schedule net)) :run)
      (omap::assoc pid (erl-step net)))
    (inv pid (erl-step net)))
  :enable (erl-step runnable? proc-runnable?)
  :disable (scheduler-correct-when-run inv-of-inv-all)
  :use
    (scheduler-correct-when-run
     (:instance inv-of-inv-all (pid (scheduling-run->p (schedule net))))
     (:instance inv-of-inv-all)
     (:instance wtree-node-props (p (scheduling-run->p (schedule net))))
     (:instance inv-of-run-props)
     (:instance run-idle-props (p (scheduling-run->p (schedule net))))
     (:instance inv-of-run-idle-to-receive (p (scheduling-run->p (schedule net))))
     (:instance inv-of-run-idle-to-terminated
       (p (scheduling-run->p (schedule net))))
     (:instance inv-of-run-receive (p (scheduling-run->p (schedule net))))))