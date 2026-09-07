; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "inv")
(include-book "proc-receive")
(local (include-book "props"))

; After proving the deliver case, I assumed the run case would be similar.
; I was wrong, I kept realizing I was missing one property or another.
; Many of these theorems are too big, hard to read, and do not perform very well.
; However, I really wanted to have the reduce example for the workshop 2026.
; The first TODO would be to split this file so that it can be certified
; in parallel.

; Proving that the invariant holds after erl-step, in the run branch.


; inv after updating the map ---------------------------------------------------

; Other nodes are not affected by the run update.
(local (defrule inv-of-update-other-node
  (implies
    (and
      (network-p net) (network-p (omap::update p proc net))
      (pid-p p) (proc-p proc) (omap::assoc p net)
      (equal (erl-state->self (proc->s proc)) p)
      (pid-p pid) (not (equal pid p)) (inv pid net)
      ; apply-k does not modify the following
      (equal (omap::lookup 'Index (wtree-bind proc))
             (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'Parent (wtree-bind proc))
             (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'ChildPids (wtree-bind proc))
             (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))
      (equal (leaf-p proc) (leaf-p (omap::lookup p net)))
      (equal (root-p proc) (root-p (omap::lookup p net)))
      ; the scheduler only runs a runnable process
      (not (equal (proc->ps (omap::lookup p net)) :terminated))
      (or ;if pid is terminated, its message is valid.
        (not (equal (proc->ps (omap::lookup pid net)) :terminated))
        (sent-message-wf (omap::lookup pid net)
          (proc->outbox (omap::lookup pid net))
          (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
          (omap::update p proc net)))
      (or ; if pid is not terminated, parent is still waiting
        (equal (proc->ps (omap::lookup pid net)) :terminated)
        (parent-still-waiting-p pid
          (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
          (omap::update p proc net))))
    (inv pid (omap::update p proc net)))
  :enable (inv proc->pid)
  :disable (sent-message-wf parent-still-waiting-p)
  :use (:instance wtree-nodes-are-leaf-or-root (pid p))))

; inv after process was run to the next receive
(local (defruled inv-of-update-to-receive
  (implies
    (and
      (network-p net) (wtree-p net) (proc-p proc)
      (omap::assoc p net)
      (network-p (omap::update p proc net))
      (not (equal (proc->ps (omap::lookup p net)) :terminated))
      (iff (omap::assoc 'Index (wtree-bind proc))
           (omap::assoc 'Index (wtree-bind (omap::lookup p net))))
      (iff (omap::assoc 'Parent (wtree-bind proc))
           (omap::assoc 'Parent (wtree-bind (omap::lookup p net))))
      (iff (omap::assoc 'ChildPids (wtree-bind proc))
           (omap::assoc 'ChildPids (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'Index (wtree-bind proc))
             (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'Parent (wtree-bind proc))
             (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'ChildPids (wtree-bind proc))
             (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))
      (equal (erl-state->self (proc->s proc))
             (erl-state->self (proc->s (omap::lookup p net))))
      (equal (proc->ps proc) :receive)
      (erl-klst-p (proc->klst proc))
      (consp (erl-val-cons->lst (omap::lookup 'ChildPids (wtree-bind proc))))
      (parent-still-waiting-p p (omap::lookup 'Parent (wtree-bind proc)) net)
      (not (equal (omap::lookup 'Parent (wtree-bind proc)) p))
      (equal (erl-val-kind (erl-state->in (proc->s proc))) :none)
      (equal (proc->outbox proc) nil)
      (equal (proc->inbox-tried proc) nil)
      (equal (erl-state->world (proc->s proc)) (sum-reduce-w))
      (equal (erl-state->module (proc->s proc)) 'local)
      (omap::assoc 'ParentPid (erl-state->bind (proc->s proc)))
      (omap::assoc 'CPids (erl-state->bind (proc->s proc)))
      (omap::assoc 'ChildHd (erl-state->bind (proc->s proc)))
      (omap::assoc 'ChildTl (erl-state->bind (proc->s proc)))
      (omap::assoc 'LeftTotal (erl-state->bind (proc->s proc)))
      ; RightTotal goes out of scope.
      (not (omap::assoc 'RightTotal (erl-state->bind (proc->s proc))))
      (> (erl-k->fuel (car (proc->klst proc)))
         (+ 100 (* 6 (len (erl-val-cons->lst
                            (omap::lookup 'CPids (erl-state->bind (proc->s proc))))))))
      (equal (omap::lookup 'ParentPid (erl-state->bind (proc->s proc)))
             (omap::lookup 'Parent (wtree-bind proc)))

      ; CPids are correct.
      (equal (erl-val-kind (omap::lookup 'CPids (erl-state->bind (proc->s proc))))
             :cons)
      (consp (erl-val-cons->lst
               (omap::lookup 'CPids (erl-state->bind (proc->s proc)))))
      (prefixp (rev (erl-val-cons->lst
                      (omap::lookup 'CPids (erl-state->bind (proc->s proc)))))
               (rev (erl-val-cons->lst
                      (omap::lookup 'ChildPids (wtree-bind proc)))))
      (equal (omap::lookup 'ChildHd (erl-state->bind (proc->s proc)))
             (car (erl-val-cons->lst
                    (omap::lookup 'CPids (erl-state->bind (proc->s proc))))))
      (equal (erl-val-kind (omap::lookup 'ChildTl (erl-state->bind (proc->s proc))))
             :cons)
      (equal (erl-val-cons->lst
               (omap::lookup 'ChildTl (erl-state->bind (proc->s proc))))
             (cdr (erl-val-cons->lst
                    (omap::lookup 'CPids (erl-state->bind (proc->s proc))))))
      ; ChildHd is correct
      (omap::assoc (omap::lookup 'ChildHd (erl-state->bind (proc->s proc))) net)
      (not (equal (omap::lookup 'ChildHd (erl-state->bind (proc->s proc))) p))
      (leaf-p (omap::lookup
                (omap::lookup 'ChildHd (erl-state->bind (proc->s proc))) net))
      (< (erl-val-integer->val (omap::lookup 'Index (wtree-bind proc)))
         (erl-val-integer->val
           (omap::lookup 'Index
             (wtree-bind (omap::lookup
                           (omap::lookup 'ChildHd (erl-state->bind (proc->s proc)))
                           net)))))

      ; LeftTotal is correct
      (equal (erl-val-kind (omap::lookup 'LeftTotal (erl-state->bind (proc->s proc))))
             :integer)
      (equal (erl-val-integer->val
               (omap::lookup 'LeftTotal (erl-state->bind (proc->s proc))))
             (sum-range
               (erl-val-integer->val (omap::lookup 'Index (wtree-bind proc)))
               (1- (erl-val-integer->val
                     (omap::lookup 'Index
                       (wtree-bind (omap::lookup
                                     (omap::lookup 'ChildHd
                                       (erl-state->bind (proc->s proc)))
                                     net)))))))

      ; the messages still to come
      (received-messages-wf (proc->inbox-new proc)
        (erl-val-cons->lst (omap::lookup 'CPids (erl-state->bind (proc->s proc))))
        net)
      (reduce-receive-klst-p (proc->klst proc)
        (omap::from-lists
          (list 'ChildPids 'Parent 'Index)
          (list (make-erl-val-cons
                  :lst (erl-val-cons->lst
                         (omap::lookup 'ChildPids (wtree-bind proc))))
                (omap::lookup 'Parent (wtree-bind proc))
                (make-erl-val-integer
                  :val (erl-val-integer->val
                         (omap::lookup 'Index (wtree-bind proc))))))))
    (inv p (omap::update p proc net)))
  :enable (inv proc->pid proc->outbox)
  :use ((:instance wtree-nodes-are-leaf-or-root (pid p)))))

; inv after a process blocked waiting for ChildHd's message
(local (defruled inv-of-update-to-blocked
  (implies
    (and
      (network-p net) (wtree-p net) (proc-p proc)
      (omap::assoc p net)
      (network-p (omap::update p proc net))
      (not (equal (proc->ps (omap::lookup p net)) :terminated))
      (iff (omap::assoc 'Index (wtree-bind proc))
           (omap::assoc 'Index (wtree-bind (omap::lookup p net))))
      (iff (omap::assoc 'Parent (wtree-bind proc))
           (omap::assoc 'Parent (wtree-bind (omap::lookup p net))))
      (iff (omap::assoc 'ChildPids (wtree-bind proc))
           (omap::assoc 'ChildPids (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'Index (wtree-bind proc))
             (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'Parent (wtree-bind proc))
             (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'ChildPids (wtree-bind proc))
             (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))
      (equal (erl-state->self (proc->s proc))
             (erl-state->self (proc->s (omap::lookup p net))))
      (equal (proc->ps proc) :blocked)
      (erl-klst-p (proc->klst proc))
      (consp (erl-val-cons->lst (omap::lookup 'ChildPids (wtree-bind proc))))
      (parent-still-waiting-p p (omap::lookup 'Parent (wtree-bind proc)) net)
      (not (equal (omap::lookup 'Parent (wtree-bind proc)) p))
      (equal (erl-val-kind (erl-state->in (proc->s proc))) :none)
      (equal (proc->outbox proc) nil)
      (equal (proc->inbox-new proc) nil)
      (equal (erl-state->world (proc->s proc)) (sum-reduce-w))
      (equal (erl-state->module (proc->s proc)) 'local)
      (omap::assoc 'ParentPid (erl-state->bind (proc->s proc)))
      (omap::assoc 'CPids (erl-state->bind (proc->s proc)))
      (omap::assoc 'ChildHd (erl-state->bind (proc->s proc)))
      (omap::assoc 'ChildTl (erl-state->bind (proc->s proc)))
      (omap::assoc 'LeftTotal (erl-state->bind (proc->s proc)))
      ; RightTotal goes out of scope.
      (not (omap::assoc 'RightTotal (erl-state->bind (proc->s proc))))
      (> (erl-k->fuel (car (proc->klst proc)))
         (+ 100 (* 6 (len (erl-val-cons->lst
                            (omap::lookup 'CPids (erl-state->bind (proc->s proc))))))))
      (equal (omap::lookup 'ParentPid (erl-state->bind (proc->s proc)))
             (omap::lookup 'Parent (wtree-bind proc)))

      ; CPids are correct.
      (equal (erl-val-kind (omap::lookup 'CPids (erl-state->bind (proc->s proc))))
             :cons)
      (consp (erl-val-cons->lst
               (omap::lookup 'CPids (erl-state->bind (proc->s proc)))))
      (prefixp (rev (erl-val-cons->lst
                      (omap::lookup 'CPids (erl-state->bind (proc->s proc)))))
               (rev (erl-val-cons->lst
                      (omap::lookup 'ChildPids (wtree-bind proc)))))
      (equal (omap::lookup 'ChildHd (erl-state->bind (proc->s proc)))
             (car (erl-val-cons->lst
                    (omap::lookup 'CPids (erl-state->bind (proc->s proc))))))
      (equal (erl-val-kind (omap::lookup 'ChildTl (erl-state->bind (proc->s proc))))
             :cons)
      (equal (erl-val-cons->lst
               (omap::lookup 'ChildTl (erl-state->bind (proc->s proc))))
             (cdr (erl-val-cons->lst
                    (omap::lookup 'CPids (erl-state->bind (proc->s proc))))))
      ; ChildHd is correct
      (omap::assoc (omap::lookup 'ChildHd (erl-state->bind (proc->s proc))) net)
      (not (equal (omap::lookup 'ChildHd (erl-state->bind (proc->s proc))) p))
      (leaf-p (omap::lookup
                (omap::lookup 'ChildHd (erl-state->bind (proc->s proc))) net))
      (< (erl-val-integer->val (omap::lookup 'Index (wtree-bind proc)))
         (erl-val-integer->val
           (omap::lookup 'Index
             (wtree-bind (omap::lookup
                           (omap::lookup 'ChildHd (erl-state->bind (proc->s proc)))
                           net)))))

      ; LeftTotal is correct
      (equal (erl-val-kind (omap::lookup 'LeftTotal (erl-state->bind (proc->s proc))))
             :integer)
      (equal (erl-val-integer->val
               (omap::lookup 'LeftTotal (erl-state->bind (proc->s proc))))
             (sum-range
               (erl-val-integer->val (omap::lookup 'Index (wtree-bind proc)))
               (1- (erl-val-integer->val
                     (omap::lookup 'Index
                       (wtree-bind (omap::lookup
                                     (omap::lookup 'ChildHd
                                       (erl-state->bind (proc->s proc)))
                                     net)))))))

      ; the messages already tried, none of them from ChildHd -- otherwise the
      ; node would have consumed it instead of blocking
      (received-messages-wf (proc->inbox-tried proc)
        (erl-val-cons->lst (omap::lookup 'CPids (erl-state->bind (proc->s proc))))
        net)
      (not (inbox-contains (proc->inbox-tried proc)
             (omap::lookup 'ChildHd (erl-state->bind (proc->s proc)))))
      (reduce-receive-klst-p (proc->klst proc)
        (omap::from-lists
          (list 'ChildPids 'Parent 'Index)
          (list (make-erl-val-cons
                  :lst (erl-val-cons->lst
                         (omap::lookup 'ChildPids (wtree-bind proc))))
                (omap::lookup 'Parent (wtree-bind proc))
                (make-erl-val-integer
                  :val (erl-val-integer->val
                         (omap::lookup 'Index (wtree-bind proc))))))))
    (inv p (omap::update p proc net)))
  :enable (inv proc->pid proc->outbox)
  :use ((:instance wtree-nodes-are-leaf-or-root (pid p)))))


; inv of updating the net with a terminatde node. 
(local (defruled inv-of-update-of-terminated
  (implies
    (and
      (network-p net) (wtree-p net)
      (omap::assoc p net) (proc-p proc)
      (equal (erl-state->self (proc->s proc)) p)
      (iff (omap::assoc 'Index (wtree-bind proc))
           (omap::assoc 'Index (wtree-bind (omap::lookup p net))))
      (iff (omap::assoc 'Parent (wtree-bind proc))
           (omap::assoc 'Parent (wtree-bind (omap::lookup p net))))
      (iff (omap::assoc 'ChildPids (wtree-bind proc))
           (omap::assoc 'ChildPids (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'Index (wtree-bind proc))
             (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'Parent (wtree-bind proc))
             (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'ChildPids (wtree-bind proc))
             (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))
      (equal (proc->ps proc) :terminated)
      (erl-klst-p (proc->klst proc))
      (consp (erl-val-cons->lst (omap::lookup 'ChildPids (wtree-bind proc))))
      (equal (erl-val-kind (erl-state->in (proc->s proc))) :integer)
      (omap::assoc
        (rightmost-child p (omap::update p proc net))
        (omap::update p proc net))
      (leaf-p 
        (omap::lookup (rightmost-child p (omap::update p proc net))
                      (omap::update p proc net)))
      (<= (erl-val-integer->val (omap::lookup 'Index (wtree-bind proc)))
          (erl-val-integer->val
            (omap::lookup 'Index
              (wtree-bind
                (omap::lookup
                  (rightmost-child p
                    (omap::update p proc net))
                  (omap::update p proc net))))))
      (equal
        (erl-val-integer->val (erl-state->in (proc->s proc)))
        (sum-range
          (erl-val-integer->val (omap::lookup 'Index (wtree-bind proc)))
          (erl-val-integer->val
            (omap::lookup 'Index
              (wtree-bind
                (omap::lookup
                  (rightmost-child p (omap::update p proc net))
                  (omap::update p proc net)))))))
      (sent-message-wf proc (proc->outbox proc)
        (omap::lookup 'Parent (wtree-bind proc))
        (omap::update p proc net))
      (null (proc->inbox-tried proc))
      (null (proc->inbox-new proc)))
    (inv p (omap::update p proc net)))
  :enable (inv proc->pid)))

; inv of updating the net with a terminatde node,
; same as inv-of-update-of-terminated. However, this time
; the hypotheses are with respect to the network before the update.
(local (defruled inv-of-update-of-terminated-2
  (implies
    (and
      (network-p net) (wtree-p net)
      (proc-p proc) (omap::assoc p net)
      (network-p (omap::update p proc net))
      (equal (erl-state->self (proc->s proc)) p)
      (iff (omap::assoc 'Index (wtree-bind proc))
           (omap::assoc 'Index (wtree-bind (omap::lookup p net))))
      (iff (omap::assoc 'Parent (wtree-bind proc))
           (omap::assoc 'Parent (wtree-bind (omap::lookup p net))))
      (iff (omap::assoc 'ChildPids (wtree-bind proc))
           (omap::assoc 'ChildPids (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'Index (wtree-bind proc))
             (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'Parent (wtree-bind proc))
             (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'ChildPids (wtree-bind proc))
             (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))
      (equal (proc->ps proc) :terminated)
      (erl-klst-p (proc->klst proc))
      (consp (erl-val-cons->lst (omap::lookup 'ChildPids (wtree-bind proc))))
      (equal (erl-val-kind (erl-state->in (proc->s proc))) :integer)
      ; This time state hyps with respect to net, instead of update of net
      (omap::assoc (rightmost-child p net) net)
      (leaf-p (omap::lookup (rightmost-child p net) net))
      (< (erl-val-integer->val
           (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
         (erl-val-integer->val
           (omap::lookup 'Index
             (wtree-bind (omap::lookup (rightmost-child p net) net)))))
      (equal (erl-val-integer->val (erl-state->in (proc->s proc)))
             (sum-range
               (erl-val-integer->val
                 (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
               (erl-val-integer->val
                 (omap::lookup 'Index
                   (wtree-bind
                     (omap::lookup (rightmost-child p net) net))))))
      (parent-still-waiting-p p (omap::lookup 'Parent (wtree-bind proc)) net)
      (equal (proc->outbox proc)
             (if (pid-p (omap::lookup 'Parent (wtree-bind proc)))
                 (omap::update (omap::lookup 'Parent (wtree-bind proc))
                   (list (make-erl-val-tuple
                           :lst (list p (erl-state->in (proc->s proc)))))
                   nil)
               nil))
      (null (proc->inbox-tried proc))
      (null (proc->inbox-new proc)))
    (inv p (omap::update p proc net)))
  :use ((:instance wtree-nodes-are-leaf-or-root (pid p))
        (:instance parent-not-self-of-wtree (pid p))
        (:instance sent-message-wf-of-terminating-node)
        (:instance leaf-root-p-when-wtree-bindings-equal
          (p1 proc) (p2 (omap::lookup p net)))
        (:instance inv-of-update-of-terminated))))


; inv of idle -> receive -------------------------------------------------------

; inv of a node with children, when it is run for the first time
; I call it self, because we are checking (inv p (update p net))
(local (defrule inv-of-idle-to-receive-self
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :idle)
      (erl-val-cons->lst
        (omap::lookup 'ChildPids
          (wtree-bind (omap::lookup p net))))
      (equal
        (erl-val-kind
          (erl-state->in
            (apply-k (proc->s (omap::lookup p net))
                     (proc->klst (omap::lookup p net)))))
        :receive)
      (network-p
        (omap::update p
          (change-proc (omap::lookup p net)
            :s (update-erl-state->in
                 (apply-k (proc->s (omap::lookup p net))
                          (proc->klst (omap::lookup p net)))
                 (make-erl-val-none))
            :ps :receive
            :klst (erl-val-receive->klst
                    (erl-state->in
                      (apply-k (proc->s (omap::lookup p net))
                               (proc->klst (omap::lookup p net))))))
          net)))
    (inv p
      (omap::update p
        (change-proc (omap::lookup p net)
          :s (update-erl-state->in
               (apply-k (proc->s (omap::lookup p net))
                        (proc->klst (omap::lookup p net)))
               (make-erl-val-none))
          :ps :receive
          :klst (erl-val-receive->klst
                  (erl-state->in
                    (apply-k (proc->s (omap::lookup p net))
                             (proc->klst (omap::lookup p net))))))
        net)))
  :enable inv
  :disable wtree-bind-of-new-proc
  :use
    ((:instance wtree-bind-of-new-proc
      (p (omap::lookup p net)) (self p)
      (parent (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
      (children (erl-val-cons->lst
                  (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))
      (index (erl-val-integer->val
                (omap::lookup 'Index (wtree-bind (omap::lookup p net))))))
    (:instance first-child-of-check-indices
      (pid p) (children (erl-val-cons->lst
                            (omap::lookup 'ChildPids
                              (wtree-bind (omap::lookup p net)))))
      (index (erl-val-integer->val
                (omap::lookup 'Index (wtree-bind (omap::lookup p net))))))
    (:instance wtree-nodes-are-leaf-or-root (pid p)))))


; inv of idle -> termianted ----------------------------------------------------

; inv of a node with no children, when it is run for the first time
; TODO: This is expensive, but good enough for now.
(local (defrule inv-of-idle-to-terminated-self
  (implies
    (and
      (network-p net) (wtree-p net)
      (pid-p p) (omap::assoc p net)
      (inv p net)
      (equal (proc->ps (omap::lookup p net)) :idle)
      (not (erl-val-cons->lst
             (omap::lookup 'ChildPids
              (wtree-bind (omap::lookup p net)))))
      (network-p
        (omap::update p
          (change-proc (omap::lookup p net)
            :s (apply-k (proc->s (omap::lookup p net))
                        (proc->klst (omap::lookup p net)))
            :ps :terminated
            :klst nil)
          net)))
    (inv p
      (omap::update p
        (change-proc (omap::lookup p net)
          :s (apply-k (proc->s (omap::lookup p net))
                      (proc->klst (omap::lookup p net)))
          :ps :terminated
          :klst nil)
        net)))
  :enable inv
  :disable (wtree-nodes-are-leaf-or-root
            apply-k-of-idle-no-children wtree-bind-of-new-proc
            wtree-p-of-update-when-wtree-bindings-equal)
  :use ((:instance wtree-nodes-are-leaf-or-root (pid p))
        (:instance apply-k-of-idle-no-children
          (s (proc->s (make-reduce-proc p '(:atom none) nil 0)))
          (klst (proc->klst (make-reduce-proc p '(:atom none) nil 0)))
          (self p) (parent '(:atom none)) (index 0))
        (:instance apply-k-of-idle-no-children
          (s (proc->s (omap::lookup p net))) (self p)
          (klst (proc->klst (omap::lookup p net)))
          (parent (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
          (index (erl-val-integer->val
                   (omap::lookup 'Index (wtree-bind (omap::lookup p net))))))
        (:instance sent-message-wf-of-terminating-node
          (proc (change-proc (omap::lookup p net)
                  :s (apply-k (proc->s (omap::lookup p net))
                              (proc->klst (omap::lookup p net)))
                  :ps :terminated
                  :klst nil)))
        (:instance wtree-bind-of-new-proc
          (p (omap::lookup p net)) (self p) (children nil)
          (parent (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
          (index (erl-val-integer->val
                   (omap::lookup 'Index (wtree-bind (omap::lookup p net))))))
        (:instance wtree-bind-of-new-proc
          (p (omap::lookup p net)) (self p)
          (parent '(:atom none)) (children nil) (index 0))
        (:instance wtree-p-of-update-when-wtree-bindings-equal
          (proc (change-proc (omap::lookup p net)
                  :s (apply-k (proc->s (omap::lookup p net))
                              (proc->klst (omap::lookup p net)))
                  :ps :terminated
                  :klst nil)))
       (:instance parent-not-self))
  :prep-lemmas
    ((defruled parent-not-self
      (implies
        (and
          (and (network-p net) (wtree-p net))
          (omap::assoc p net))
        (not
          (equal (omap::lookup 'Parent
                   (wtree-bind (omap::lookup p net))) p)))
       :use (:instance check-parent-of-wtree-p (pid p))))))


; inv of receive -> blocked ----------------------------------------------------

; receive -> blocked, the message on top is not from ChildHd.
; Remark: Thanks to the painful lemmas above, this one is easy.
(local (defruled inv-of-receive-to-blocked
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (pid-p p) (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (not
        (inbox-contains
          (proc->inbox-new (omap::lookup p net))
          (car (erl-val-cons->lst
                 (omap::lookup 'CPids
                    (erl-state->bind
                      (proc->s (omap::lookup p net))))))))
      (network-p
        (omap::update p (proc-receive (omap::lookup p net)) net)))
    (inv p (omap::update p (proc-receive (omap::lookup p net)) net)))
  :do-not-induct t
  :enable inv-of-update-to-blocked
  :disable (inv)
  :use ((:instance proc-receive-blocked-props))))


; inv of receive -> receive ----------------------------------------------------

(local (defrule inv-of-receive-run-more-children
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (pid-p p) (omap::assoc p net)
      (inv (car (erl-val-cons->lst (omap::lookup 'CPids
                  (erl-state->bind (proc->s (omap::lookup p net)))))) net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (inbox-contains (proc->inbox-new (omap::lookup p net))
        (car (erl-val-cons->lst (omap::lookup 'CPids
               (erl-state->bind (proc->s (omap::lookup p net)))))))
      (cdr (erl-val-cons->lst (omap::lookup 'CPids
             (erl-state->bind (proc->s (omap::lookup p net))))))
      (network-p (omap::update p (proc-receive (omap::lookup p net)) net)))
    (inv p (omap::update p (proc-receive (omap::lookup p net)) net)))
  :enable inv-of-update-to-receive
  :use proc-receive-match-props))


; inv of receive -> terminated -------------------------------------------------

; When proc-receive returns, parent is not self.
(local (defrule parent-not-self-of-proc-receive
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (pid-p p) (omap::assoc p net)   
      (inv (car (erl-val-cons->lst (omap::lookup 'CPids
           (erl-state->bind (proc->s (omap::lookup p net)))))) net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (inbox-contains
        (proc->inbox-new (omap::lookup p net))
        (car (erl-val-cons->lst (omap::lookup 'CPids
        (erl-state->bind (proc->s (omap::lookup p net)))))))
      (cdr (erl-val-cons->lst (omap::lookup 'CPids
      (erl-state->bind (proc->s (omap::lookup p net))))))
      (network-p (omap::update p (proc-receive (omap::lookup p net)) net)))
    (not (equal (omap::lookup 'Parent
                  (wtree-bind (proc-receive (omap::lookup p net)))) p)))
  :use
    ((:instance consumed-message-props)
     (:instance inv-receive-node-props)
     (:instance wtree-nodes-are-leaf-or-root (pid p))
     (:instance received-messages-wf-of-inbox-without-car
       (inbox (proc->inbox-new (omap::lookup p net)))
       (cpids (erl-val-cons->lst
                (omap::lookup 'CPids
                  (erl-state->bind (proc->s (omap::lookup p net)))))))
     (:instance proc-receive-of-match-with-more-children
      (p (omap::lookup p net))
      (rbind (bind-fix
        (omap::from-lists
          (list 'ChildPids 'Parent 'Index)
          (list
            (make-erl-val-cons
              :lst
                (erl-val-cons->lst
                  (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))
            (omap::lookup 'Parent (wtree-bind (omap::lookup p net)))
            (make-erl-val-integer
              :val
                (erl-val-integer->val
                  (omap::lookup 'Index (wtree-bind (omap::lookup p net)))))))))))))

; inv of receive -> terminated.
; Finally proved, after all those case lemmas.
(local (defrule inv-of-receive-to-terminated
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (omap::assoc p net)
      (inv (car (erl-val-cons->lst (omap::lookup 'CPids
                  (erl-state->bind (proc->s (omap::lookup p net)))))) net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (inbox-contains (proc->inbox-new (omap::lookup p net))
        (car (erl-val-cons->lst (omap::lookup 'CPids
               (erl-state->bind (proc->s (omap::lookup p net)))))))
      (null (cdr (erl-val-cons->lst (omap::lookup 'CPids
                   (erl-state->bind (proc->s (omap::lookup p net)))))))
      (network-p (omap::update p (proc-receive (omap::lookup p net)) net)))
    (inv p (omap::update p (proc-receive (omap::lookup p net)) net)))
  :use ((:instance terminating-node-sum)
        (:instance inv-receive-node-props)
        (:instance wtree-nodes-are-leaf-or-root (pid p))
        (:instance proc-receive-of-match-without-more-children
          (p (omap::lookup p net))
          (rbind (bind-fix
                   (omap::from-lists
                     (list 'ChildPids 'Parent 'Index)
                     (list
                       (make-erl-val-cons
                         :lst (erl-val-cons->lst
                                (omap::lookup 'ChildPids
                                  (wtree-bind (omap::lookup p net)))))
                       (omap::lookup 'Parent (wtree-bind (omap::lookup p net)))
                       (make-erl-val-integer
                         :val (erl-val-integer->val
                                (omap::lookup 'Index
                                  (wtree-bind (omap::lookup p net))))))))))
        (:instance inv-of-update-of-terminated-2
          (proc (proc-receive (omap::lookup p net)))))))


; inv of receive -> blocked for other nodes ------------------------------------

; the other nodes are not affected by the run step starting from receive
(local (defrule inv-of-receive-to-blocked-other
  (implies
    (and
      (network-p net) (wtree-p net)
      (not (equal pid p))
      (omap::assoc p net) (omap::assoc pid net)
      (inv pid net) (inv p net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (not (inbox-contains (proc->inbox-new (omap::lookup p net))
             (car (erl-val-cons->lst
                    (omap::lookup 'CPids
                      (erl-state->bind (proc->s (omap::lookup p net))))))))
      (network-p (omap::update p (proc-receive (omap::lookup p net)) net)))
    (inv pid (omap::update p (proc-receive (omap::lookup p net)) net)))
  :disable (omap::assoc-of-update)
  :use ((:instance inv-of-update-other-node
          (proc (proc-receive (omap::lookup p net))))
        (:instance proc-receive-blocked-props)
        (:instance inv-node-parent-props)
        (:instance inv-receive-node-props)
        (:instance sent-message-wf-of-update-of-receive-to-blocked
          (proc (proc-receive (omap::lookup p net)))))))


; inv of receive -> terminated for other nodes ---------------------------------

(local (defrule inv-of-receive-run-other-terminate
  (implies
    (and
      (network-p net) (wtree-p net) (pid-p p) (pid-p pid)
      (not (equal pid p))
      (omap::assoc p net) (omap::assoc pid net)
      (inv pid net) (inv p net)
      (inv (car (erl-val-cons->lst (omap::lookup 'CPids
                  (erl-state->bind (proc->s (omap::lookup p net)))))) net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (inbox-contains (proc->inbox-new (omap::lookup p net))
        (car (erl-val-cons->lst (omap::lookup 'CPids
               (erl-state->bind (proc->s (omap::lookup p net)))))))
      (null (cdr (erl-val-cons->lst (omap::lookup 'CPids
                   (erl-state->bind (proc->s (omap::lookup p net)))))))
      (network-p (omap::update p (proc-receive (omap::lookup p net)) net)))
    (inv pid (omap::update p (proc-receive (omap::lookup p net)) net)))
  :disable (equal-of-kont-function-return len)
  :use
    ((:instance inv-of-update-other-node
      (proc (proc-receive (omap::lookup p net))))
     (:instance proc-receive-terminate-props)
     (:instance inv-node-parent-props)
     (:instance inv-receive-node-props)
     (:instance terminating-node-sum)
     (:instance received-messages-wf-fields
       (pid (car (erl-val-cons->lst
                   (omap::lookup 'CPids
                    (erl-state->bind (proc->s (omap::lookup p net)))))))
      (inbox (proc->inbox-new (omap::lookup p net)))
      (cpids (erl-val-cons->lst
               (omap::lookup 'CPids
                 (erl-state->bind (proc->s (omap::lookup p net)))))))
    (:instance wtree-nodes-are-leaf-or-root (pid p))
    (:instance wtree-nodes-are-leaf-or-root (pid pid))
    (:instance sent-message-wf-of-update-of-receive->terminated
      (proc (proc-receive (omap::lookup p net))))
    (:instance parent-still-waiting-p-of-update-of-receive->terminate
      (proc (proc-receive (omap::lookup p net)))))))


; inv of receive -> any --------------------------------------------------------

; when the p is the node that is receiving.
(local (defrule inv-of-receive-self
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (omap::assoc p net)
      (inv
        (car
          (erl-val-cons->lst
            (omap::lookup 'CPids
             (erl-state->bind (proc->s (omap::lookup p net))))))
            net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (network-p (omap::update p (proc-receive (omap::lookup p net)) net)))
    (inv p (omap::update p (proc-receive (omap::lookup p net)) net)))
  :disable (equal-of-kont-function-return)
  :use
    ((:instance inv-of-receive-to-blocked)
     (:instance inv-of-receive-to-terminated))))


; inv of receive -> any for other nodes ----------------------------------------

; Same as above, but p is not equal to pid.
; i.e for p != pid, show (inv pid) when p receives.

(local (defrule inv-of-receive-match-other-node
  (implies
    (and
      (network-p net) (wtree-p net)
      (inv pid net) (inv p net)
      (not (equal pid p))
      (omap::assoc p net) (omap::assoc pid net) 
      (inv
        (car (erl-val-cons->lst
                (omap::lookup 'CPids
                   (erl-state->bind (proc->s (omap::lookup p net))))))
        net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (inbox-contains
        (proc->inbox-new (omap::lookup p net))
        (car (erl-val-cons->lst
               (omap::lookup 'CPids
                 (erl-state->bind
                     (proc->s (omap::lookup p net)))))))
      (cdr
        (erl-val-cons->lst
          (omap::lookup 'CPids
            (erl-state->bind (proc->s (omap::lookup p net))))))
      (network-p (omap::update p (proc-receive (omap::lookup p net)) net)))
    (inv pid (omap::update p (proc-receive (omap::lookup p net)) net)))
  :do-not '(preprocess)
  :enable (sent-message-wf-of-update-of-receive-match
            parent-still-waiting-p-of-update-of-receive->receive)
  :disable
    (assoc-of-runnable? omap::assoc-when-assoc-tail omap::tail-when-emptyp
     omap::assoc-when-assoc-of-tail-cheap root-when-assoc-of-tail-is-root
     runnable-of-tail leaf-when-assoc-of-tail-is-leaf omap::lookup-when-emptyp
     omap::assoc-when-emptyp assoc-of-non-root-segment leaf-equiv-when-bindings-equiv
     root-equiv-when-bindings-equiv wtree0-nodes-are-leaf-or-root
     wtree0-nodes-are-leaf-or-root-rev wtree0-of-zero reduce-receive-klst-p
     len inv equal-of-kont-function-return omap::assoc-of-update
     equal-of-kont-function-return sent-message-wf parent-still-waiting-p
     parent-of-root parent-of-leaf index-of-root index-of-leaf)
  :use
    ((:instance inv-of-update-other-node
        (proc (proc-receive (omap::lookup p net))))
     (:instance proc-receive-match-more-props)
     (:instance inv-node-parent-props)
     (:instance inv-receive-node-props)
     (:instance chd-not-in-rest-of-cpids)
     (:instance received-messages-wf-fields
       (pid (car
              (erl-val-cons->lst
                (omap::lookup 'CPids
                  (erl-state->bind
                    (proc->s (omap::lookup p net)))))))
       (inbox (proc->inbox-new (omap::lookup p net)))
       (cpids (erl-val-cons->lst
                (omap::lookup 'CPids
                   (erl-state->bind
                     (proc->s (omap::lookup p net)))))))
      (:instance wtree-nodes-are-leaf-or-root (pid p))
      (:instance wtree-nodes-are-leaf-or-root (pid pid)))))


; Combining all the "other node" cases for running a node from receive state. 
(local (defrule inv-of-receive-run-others
  (implies
    (and
      (network-p net) (wtree-p net)
      (inv pid net) (inv p net)
      (not (equal pid p))
      (omap::assoc p net) (omap::assoc pid net)
      (inv
        (car (erl-val-cons->lst
              (omap::lookup 'CPids
                (erl-state->bind (proc->s (omap::lookup p net))))))
        net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (network-p (omap::update p (proc-receive (omap::lookup p net)) net)))
    (inv pid (omap::update p (proc-receive (omap::lookup p net)) net)))
  :disable (inv omap::assoc-of-update equal-of-kont-function-return)
  :use
    ((:instance inv-of-receive-to-blocked-other)
     (:instance inv-of-receive-match-other-node)
     (:instance inv-of-receive-run-other-terminate))))

; inv of receive -> any --------------------------------------------------------

; TODO: Some of these should be renamed. This differs from inv of receive -> any
; above because it includes both p = pid and p != pid cases.

; Same as above, but for node in question (p).
(local (defrule inv-of-receive
  (implies
    (and
      (network-p net) (inv-all net)
      (pid-p p) (pid-p pid) (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (network-p (omap::update p
                   (proc-receive (omap::lookup p net)) net))
      (omap::assoc pid
        (omap::update p (proc-receive (omap::lookup p net)) net)))
    (inv pid (omap::update p (proc-receive (omap::lookup p net)) net)))
  :cases ((equal pid p))
  :disable
    (inv omap::assoc-of-update
     equal-of-kont-function-return omap::lookup-of-update)
  :use
    ((:instance inv-of-receive-self)
     (:instance inv-of-receive-run-others)
     (:instance inv-of-inv-all (pid p))
     (:instance inv-of-inv-all (pid pid))
     (:instance inv-receive-node-props)
     (:instance wtree-p-of-inv (pid p))
     (:instance wtree-nodes-are-leaf-or-root (pid p))
     (:instance inv-of-inv-all
        (pid (car (erl-val-cons->lst
                    (omap::lookup 'CPids
                      (erl-state->bind
                        (proc->s (omap::lookup p net)))))))))))


; inv of idle -> receive for other nodes ---------------------------------------

; idle -> receive, observed by another node
(local (defrule inv-of-idle-to-receive-other
  (implies
    (and
      (network-p net) (wtree-p net)
      (inv pid net) (inv p net)
      (pid-p p) (pid-p pid) (not (equal pid p))
      (omap::assoc p net) (omap::assoc pid net)
      (equal (proc->ps (omap::lookup p net)) :idle)
      (erl-val-cons->lst
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))
      (network-p
        (omap::update p
          (change-proc
            (omap::lookup p net)
            :s (update-erl-state->in
                (apply-k
                  (proc->s (omap::lookup p net))
                  (proc->klst (omap::lookup p net)))
                (make-erl-val-none))
            :ps :receive
            :klst (erl-val-receive->klst
                    (erl-state->in
                      (apply-k
                        (proc->s (omap::lookup p net))
                        (proc->klst (omap::lookup p net))))))
          net)))
    (inv pid
         (omap::update p
          (change-proc (omap::lookup p net)
            :s (update-erl-state->in
                  (apply-k
                    (proc->s (omap::lookup p net))
                    (proc->klst (omap::lookup p net)))
                  (make-erl-val-none))
            :ps :receive
            :klst (erl-val-receive->klst
                    (erl-state->in
                      (apply-k
                        (proc->s (omap::lookup p net))
                        (proc->klst (omap::lookup p net))))))
          net)))
  :enable (sent-message-wf-of-update-of-first-run-with-children)
  :do-not '(preprocess)
  :disable
    (inv omap::assoc-of-update sent-message-wf
     parent-still-waiting-p equal-of-kont-function-return
     inv-of-update-other-node wtree-nodes-are-leaf-or-root
     parent-of-root parent-of-leaf index-of-root index-of-leaf)
  :use
    ((:instance inv-of-update-other-node
        (proc
          (change-proc (omap::lookup p net)
            :s (update-erl-state->in
                  (apply-k
                    (proc->s (omap::lookup p net))
                    (proc->klst (omap::lookup p net)))
                  (make-erl-val-none))
            :ps :receive
            :klst (erl-val-receive->klst
                    (erl-state->in
                      (apply-k
                        (proc->s (omap::lookup p net))
                                  (proc->klst (omap::lookup p net))))))))
      (:instance idle-to-receive-bind)
      (:instance idle-to-receive-leaf-or-root)
      (:instance inv-node-parent-props)
      (:instance childpids-of-parent-of-node)
      (:instance wtree-nodes-are-leaf-or-root (pid p))
      (:instance wtree-nodes-are-leaf-or-root (pid pid)))))


; inv of idle -> terminated for other nodes ------------------------------------

; idle -> terminated, observed by another node.
(local (defrule inv-of-idle-to-terminated-other
  (implies
    (and
      (network-p net) (wtree-p net)
      (inv pid net) (inv p net)
      (pid-p p) (pid-p pid) (not (equal pid p))
      (omap::assoc p net) (omap::assoc pid net)
      (equal (proc->ps (omap::lookup p net)) :idle)
      (not
        (erl-val-cons->lst
          (omap::lookup 'ChildPids
            (wtree-bind (omap::lookup p net)))))
      (network-p
        (omap::update p
          (change-proc
            (omap::lookup p net)
            :s (apply-k
                (proc->s (omap::lookup p net))
                (proc->klst (omap::lookup p net)))
            :ps :terminated
            :klst nil)
          net)))
    (inv pid
         (omap::update p
            (change-proc (omap::lookup p net)
              :s (apply-k
                    (proc->s (omap::lookup p net))
                    (proc->klst (omap::lookup p net)))
              :ps :terminated
              :klst nil)
            net)))
  :disable
    (inv omap::assoc-of-update parent-of-root index-of-root
    equal-of-kont-function-return parent-of-leaf index-of-leaf)
  :use
    ((:instance inv-of-update-other-node
      (proc (change-proc (omap::lookup p net)
              :s (apply-k
                    (proc->s (omap::lookup p net))
                    (proc->klst (omap::lookup p net)))
              :ps :terminated
              :klst nil)))
      (:instance idle-to-terminated-props)
      (:instance inv-node-parent-props)
      (:instance childpids-of-parent-of-node)
      (:instance wtree-nodes-are-leaf-or-root (pid p))
      (:instance wtree-nodes-are-leaf-or-root (pid pid)))))


; inv of idle -> receive -------------------------------------------------------

; idle -> receive for the node in question.
(local (defrule inv-of-idle-to-receive
  (implies
    (and
      (network-p net) (inv-all net)
      (pid-p p) (pid-p pid) (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :idle)
      (erl-val-cons->lst
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))
      (network-p
        (omap::update p
          (change-proc
            (omap::lookup p net)
            :s (update-erl-state->in
                (apply-k
                  (proc->s (omap::lookup p net))
                  (proc->klst (omap::lookup p net)))
                (make-erl-val-none))
            :ps :receive
            :klst (erl-val-receive->klst
                    (erl-state->in
                      (apply-k
                        (proc->s (omap::lookup p net))
                        (proc->klst (omap::lookup p net))))))
          net))
      (omap::assoc pid
        (omap::update p
          (change-proc
            (omap::lookup p net)
            :s (update-erl-state->in
                (apply-k
                  (proc->s (omap::lookup p net))
                  (proc->klst (omap::lookup p net)))
                (make-erl-val-none))
            :ps :receive
            :klst (erl-val-receive->klst
                    (erl-state->in
                      (apply-k
                        (proc->s (omap::lookup p net))
                        (proc->klst (omap::lookup p net))))))
          net)))
    (inv pid
         (omap::update p
            (change-proc (omap::lookup p net)
              :s (update-erl-state->in
                    (apply-k
                      (proc->s (omap::lookup p net))
                      (proc->klst (omap::lookup p net)))
                    (make-erl-val-none))
              :ps :receive
              :klst (erl-val-receive->klst
                      (erl-state->in
                        (apply-k
                          (proc->s (omap::lookup p net))
                          (proc->klst (omap::lookup p net))))))
            net)))
  :use
    ((:instance inv-of-idle-to-receive-self (p p))
     (:instance inv-of-idle-to-receive-other)
     (:instance idle-to-receive-val)
     (:instance idle-to-receive-bind)
     (:instance idle-to-receive-leaf-or-root)
     (:instance inv-of-inv-all (pid p))
     (:instance inv-of-inv-all (pid pid))
     (:instance wtree-p-of-inv (pid p)))))


; inv of idle -> terminated ----------------------------------------------------

; idle -> terminated, for the node in question
(local (defrule inv-idle-to-terminated
  (implies
    (and
      (network-p net) (inv-all net)
      (pid-p p) (pid-p pid) (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :idle)
      (not (erl-val-cons->lst
             (omap::lookup 'ChildPids
               (wtree-bind (omap::lookup p net)))))
      (network-p
        (omap::update p
          (change-proc
            (omap::lookup p net)
            :s (apply-k
                (proc->s (omap::lookup p net))
                (proc->klst (omap::lookup p net)))
            :ps :terminated
            :klst nil)
          net))
      (omap::assoc pid
        (omap::update p
          (change-proc
            (omap::lookup p net)
            :s (apply-k
                (proc->s (omap::lookup p net))
                (proc->klst (omap::lookup p net)))
            :ps :terminated
            :klst nil)
          net)))
    (inv pid
        (omap::update p
          (change-proc (omap::lookup p net)
                      :s (apply-k
                            (proc->s (omap::lookup p net))
                            (proc->klst (omap::lookup p net)))
                      :ps :terminated
                      :klst nil)
          net)))
  :use
    ((:instance inv-of-idle-to-terminated-self (p p))
      (:instance inv-of-idle-to-terminated-other)
      (:instance inv-of-inv-all (pid p))
      (:instance inv-of-inv-all (pid pid))
      (:instance wtree-p-of-inv (pid p)))))


; inv of run -------------------------------------------------------------------

; Finally:
(defrule inv-of-erl-step-of-run
  (implies
    (and
      (network-p net) (inv-all net) (not (terminated? net))
      (equal (scheduling-kind (schedule net)) :run)
      (omap::assoc pid (erl-step net)))
    (inv pid (erl-step net)))
  :enable (erl-step runnable? proc-runnable? proc->pid)
  :use
    ((:instance scheduler-correct-when-run)
      (:instance wtree-p-of-inv (pid (scheduling-run->p (schedule net))))
      (:instance idle-to-receive-bind
        (p (scheduling-run->p (schedule net))))
      (:instance idle-to-receive-val
        (p (scheduling-run->p (schedule net))))
      (:instance idle-to-receive-leaf-or-root
        (p (scheduling-run->p (schedule net))))
      (:instance idle-to-terminated-props
        (p (scheduling-run->p (schedule net))))
      (:instance inv-of-idle-to-receive
        (p (scheduling-run->p (schedule net))))))