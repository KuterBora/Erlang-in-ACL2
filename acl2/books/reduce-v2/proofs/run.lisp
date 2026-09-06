(in-package "ACL2")
(include-book "inv")
(include-book "proc-receive")

; After proving the deliver case, I assumed the run case would be similar.
; I was wrong, I kept realizing I was missing one property or another.
; Many of these theorems are too big, hard to read, and do not perform very well.
; However, I really wanted to have the reduce example for the workshop 2026.
; The first TODO would be to split this file so that it can be certified
; in parallel.


; Proving that the invariant holds after erl-step, in the :run branch.

; Other nodes are not affected by the run update.
(local (defrule inv-of-update-of-running-node
  (implies
    (and
      (network-p net) (network-p (omap::update p proc net))
      (pid-p p) (proc-p proc) (omap::assoc p net)
      (equal (erl-state->self (proc->s proc)) p)
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
      (pid-p pid) (not (equal pid p)) (inv pid net)
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

(local (defruled inv-idle-node-facts
  (implies
    (and
      (network-p net) (pid-p p) (inv p net)
      (equal (proc->ps (omap::lookup p net)) :idle)
      (or (leaf-p (omap::lookup p net))
          (root-p (omap::lookup p net))))
    (and
      (erl-klst-p (proc->klst (omap::lookup p net)))
      (equal
        (proc->s (omap::lookup p net))
        (proc->s
          (make-reduce-proc p
            (omap::lookup 'Parent (wtree-bind (omap::lookup p net)))
            (erl-val-cons->lst
              (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))
            (erl-val-integer->val
              (omap::lookup 'Index (wtree-bind (omap::lookup p net)))))))
      (equal
        (proc->klst (omap::lookup p net))
        (proc->klst
          (make-reduce-proc p
            (omap::lookup 'Parent (wtree-bind (omap::lookup p net)))
            (erl-val-cons->lst
              (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))
            (erl-val-integer->val
              (omap::lookup 'Index (wtree-bind (omap::lookup p net)))))))
      (null (proc->inbox-tried (omap::lookup p net)))
      (parent-still-waiting-p p
        (omap::lookup 'Parent (wtree-bind (omap::lookup p net))) net)
      (received-messages-wf (proc->inbox-new (omap::lookup p net))
        (erl-val-cons->lst
          (omap::lookup 'ChildPids(wtree-bind (omap::lookup p net))))
        net)))
  :enable inv))

; inv after process was run to the next receive
(local (defruled inv-of-update-of-receive
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


; inv of a node with children, when it is run for the first time
(local (defrule inv-of-first-run-with-children
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

; inv of a node with no children, when it is run for the first time
; TODO: This is expensive, but good enough for now.
(local (defrule inv-of-first-run-without-children
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

; facts about inv of a receive node.
; This way I don't need to expand all cases of inv
(local (defruled inv-receive-node-facts
  (implies
    (and
      (network-p net) (inv p net) (pid-p p)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (or (leaf-p (omap::lookup p net))
          (root-p (omap::lookup p net))))
    (and
      (erl-klst-p (proc->klst (omap::lookup p net)))
      (consp (erl-val-cons->lst
               (omap::lookup 'ChildPids
                  (wtree-bind (omap::lookup p net)))))
      (parent-still-waiting-p p
        (omap::lookup 'Parent
          (wtree-bind (omap::lookup p net))) net)
      (equal
        (erl-val-kind
          (erl-state->in (proc->s (omap::lookup p net))))
        :none)
      (null (proc->outbox (omap::lookup p net)))
      (null (proc->inbox-tried (omap::lookup p net)))
      (equal (erl-state->world (proc->s (omap::lookup p net)))
             (sum-reduce-w))
      (equal (erl-state->module (proc->s (omap::lookup p net)))
             'local)
      (omap::assoc 'ParentPid
        (erl-state->bind (proc->s (omap::lookup p net))))
      (omap::assoc 'CPids
        (erl-state->bind (proc->s (omap::lookup p net))))
      (omap::assoc 'ChildHd
        (erl-state->bind (proc->s (omap::lookup p net))))
      (omap::assoc 'ChildTl
        (erl-state->bind (proc->s (omap::lookup p net))))
      (omap::assoc 'LeftTotal
        (erl-state->bind (proc->s (omap::lookup p net))))
      (not (omap::assoc 'RightTotal
             (erl-state->bind (proc->s (omap::lookup p net)))))
      (> (erl-k->fuel (car (proc->klst (omap::lookup p net))))
         (+ 100 (* 6 (len (erl-val-cons->lst
                            (omap::lookup 'CPids
                              (erl-state->bind
                                (proc->s (omap::lookup p net)))))))))
      (equal (omap::lookup 'ParentPid
               (erl-state->bind (proc->s (omap::lookup p net))))
             (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))

      ; CPids are correct.
      (equal (erl-val-kind
               (omap::lookup 'CPids
                 (erl-state->bind (proc->s (omap::lookup p net)))))
             :cons)
      (consp (erl-val-cons->lst
               (omap::lookup 'CPids
                 (erl-state->bind (proc->s (omap::lookup p net))))))
      (pid-lst-p (erl-val-cons->lst
                   (omap::lookup 'CPids
                     (erl-state->bind (proc->s (omap::lookup p net))))))
      (prefixp (rev (erl-val-cons->lst
                      (omap::lookup 'CPids
                        (erl-state->bind (proc->s (omap::lookup p net))))))
               (rev (erl-val-cons->lst
                      (omap::lookup 'ChildPids
                        (wtree-bind (omap::lookup p net))))))
      (equal (omap::lookup 'ChildHd
               (erl-state->bind (proc->s (omap::lookup p net))))
             (car (erl-val-cons->lst
                    (omap::lookup 'CPids
                      (erl-state->bind (proc->s (omap::lookup p net)))))))
      (equal (erl-val-kind
               (omap::lookup 'ChildTl
                 (erl-state->bind (proc->s (omap::lookup p net)))))
             :cons)
      (equal (erl-val-cons->lst
               (omap::lookup 'ChildTl
                 (erl-state->bind (proc->s (omap::lookup p net)))))
             (cdr (erl-val-cons->lst
                    (omap::lookup 'CPids
                      (erl-state->bind (proc->s (omap::lookup p net)))))))

      ; ChildHd is correct
      (omap::assoc (car (erl-val-cons->lst
                          (omap::lookup 'CPids
                            (erl-state->bind (proc->s (omap::lookup p net))))))
                   net)
      (leaf-p (omap::lookup
                (car (erl-val-cons->lst
                       (omap::lookup 'CPids
                         (erl-state->bind (proc->s (omap::lookup p net))))))
                net))
      (< (erl-val-integer->val
           (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
         (erl-val-integer->val
           (omap::lookup 'Index
             (wtree-bind
               (omap::lookup
                 (car (erl-val-cons->lst
                        (omap::lookup 'CPids
                          (erl-state->bind (proc->s (omap::lookup p net))))))
                 net)))))

      ; LeftTotal is correct
      (equal (erl-val-kind
               (omap::lookup 'LeftTotal
                 (erl-state->bind (proc->s (omap::lookup p net)))))
             :integer)
      (equal (erl-val-integer->val
               (omap::lookup 'LeftTotal
                 (erl-state->bind (proc->s (omap::lookup p net)))))
             (sum-range
               (erl-val-integer->val
                 (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
               (1- (erl-val-integer->val
                     (omap::lookup 'Index
                       (wtree-bind
                         (omap::lookup
                           (car (erl-val-cons->lst
                                  (omap::lookup 'CPids
                                    (erl-state->bind
                                      (proc->s (omap::lookup p net))))))
                           net)))))))

      ; the messages still to come
      (received-messages-wf (proc->inbox-new (omap::lookup p net))
        (erl-val-cons->lst
          (omap::lookup 'CPids (erl-state->bind (proc->s (omap::lookup p net)))))
        net)
      (reduce-receive-klst-p (proc->klst (omap::lookup p net))
        (omap::from-lists
          (list 'ChildPids 'Parent 'Index)
          (list (make-erl-val-cons
                  :lst (erl-val-cons->lst
                         (omap::lookup 'ChildPids
                           (wtree-bind (omap::lookup p net)))))
                (omap::lookup 'Parent (wtree-bind (omap::lookup p net)))
                (make-erl-val-integer
                  :val (erl-val-integer->val
                         (omap::lookup 'Index
                           (wtree-bind (omap::lookup p net))))))))))
  :enable inv))

; facts about inv of a terminated node.
; This way I don't need to expand all cases of inv
(local (defruled inv-terminated-node-facts
  (implies
    (and
      (network-p net) (pid-p p) (inv p net)
      (equal (proc->ps (omap::lookup p net)) :terminated)
      (or (leaf-p (omap::lookup p net))
          (root-p (omap::lookup p net))))
    (and
      (equal
        (erl-val-kind
          (erl-state->in (proc->s (omap::lookup p net))))
        :integer)
      (if (null (erl-val-cons->lst
                  (omap::lookup 'ChildPids
                    (wtree-bind (omap::lookup p net)))))
          (equal
            (erl-val-integer->val
              (erl-state->in (proc->s (omap::lookup p net))))
            (erl-val-integer->val
              (omap::lookup 'Index (wtree-bind (omap::lookup p net)))))
          (and (omap::assoc (rightmost-child p net) net)
               (leaf-p (omap::lookup (rightmost-child p net) net))
               (<= (erl-val-integer->val
                      (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
                   (erl-val-integer->val
                      (omap::lookup 'Index
                        (wtree-bind (omap::lookup (rightmost-child p net) net)))))
               (equal
                 (erl-val-integer->val
                   (erl-state->in (proc->s (omap::lookup p net))))
                     (sum-range
                      (erl-val-integer->val
                        (omap::lookup 'Index
                          (wtree-bind (omap::lookup p net))))
                      (erl-val-integer->val
                        (omap::lookup 'Index
                          (wtree-bind (omap::lookup (rightmost-child p net) net))))))))))
  :enable inv))


; TODO: another huge lemma, but least it is fast.
; This is the part that reason about sum-range.
(local (defruled consumed-message-facts
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (pid-p p) (omap::assoc p net)
      (inv (car (erl-val-cons->lst
                  (omap::lookup 'CPids
                    (erl-state->bind (proc->s (omap::lookup p net))))))
           net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (inbox-contains (proc->inbox-new (omap::lookup p net))
        (car (erl-val-cons->lst
               (omap::lookup 'CPids
                 (erl-state->bind (proc->s (omap::lookup p net)))))))
      (cdr (erl-val-cons->lst
             (omap::lookup 'CPids
               (erl-state->bind (proc->s (omap::lookup p net)))))))
    (and
      ; the next child is a leaf, and sits above p in the index order
      (omap::assoc (cadr (erl-val-cons->lst
                           (omap::lookup 'CPids
                             (erl-state->bind (proc->s (omap::lookup p net))))))
                   net)
      (leaf-p (omap::lookup
                (cadr (erl-val-cons->lst
                        (omap::lookup 'CPids
                          (erl-state->bind (proc->s (omap::lookup p net))))))
                net))
      (not (equal (cadr (erl-val-cons->lst
                          (omap::lookup 'CPids
                            (erl-state->bind (proc->s (omap::lookup p net))))))
                  p))
      (< (erl-val-integer->val
           (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
         (erl-val-integer->val
           (omap::lookup 'Index
             (wtree-bind
               (omap::lookup
                 (cadr (erl-val-cons->lst
                         (omap::lookup 'CPids
                           (erl-state->bind (proc->s (omap::lookup p net))))))
                 net)))))

      ; the message from ChildHd is that child's total, and adding it to
      ; LeftTotal covers every index below the next child
      (equal (erl-val-kind
               (inbox->value (proc->inbox-new (omap::lookup p net))
                 (car (erl-val-cons->lst
                        (omap::lookup 'CPids
                          (erl-state->bind (proc->s (omap::lookup p net))))))))
             :integer)
      (equal (+ (erl-val-integer->val
                  (omap::lookup 'LeftTotal
                    (erl-state->bind (proc->s (omap::lookup p net)))))
                (erl-val-integer->val
                  (inbox->value (proc->inbox-new (omap::lookup p net))
                    (car (erl-val-cons->lst
                           (omap::lookup 'CPids
                             (erl-state->bind
                               (proc->s (omap::lookup p net)))))))))
             (sum-range
               (erl-val-integer->val
                 (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
               (1- (erl-val-integer->val
                     (omap::lookup 'Index
                       (wtree-bind
                         (omap::lookup
                           (cadr (erl-val-cons->lst
                                   (omap::lookup 'CPids
                                     (erl-state->bind
                                       (proc->s (omap::lookup p net))))))
                           net)))))))))
  :use
    ((:instance inv-receive-node-facts)
     (:instance wtree-nodes-are-leaf-or-root (pid p))
     (:instance check-indices-of-wtree-node (pid p))
     (:instance inv-terminated-node-facts
      (p (car (erl-val-cons->lst
                (omap::lookup 'CPids
                  (erl-state->bind (proc->s (omap::lookup p net))))))))
     (:instance received-messages-wf-fields
      (pid (car (erl-val-cons->lst
                  (omap::lookup 'CPids
                    (erl-state->bind (proc->s (omap::lookup p net)))))))
      (inbox (proc->inbox-new (omap::lookup p net)))
      (cpids (erl-val-cons->lst
                (omap::lookup 'CPids
                  (erl-state->bind (proc->s (omap::lookup p net)))))))
    (:instance check-indices-of-suffix
      (cps (erl-val-cons->lst
              (omap::lookup 'CPids
                (erl-state->bind (proc->s (omap::lookup p net))))))
      (children (erl-val-cons->lst
                  (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))
      (i (erl-val-integer->val
            (omap::lookup 'Index (wtree-bind (omap::lookup p net))))))
    (:instance sum-range-fold
      (i (erl-val-integer->val
            (omap::lookup 'Index (wtree-bind (omap::lookup p net)))))
      (c (erl-val-integer->val
            (omap::lookup 'Index
              (wtree-bind
                (omap::lookup
                  (car (erl-val-cons->lst
                        (omap::lookup 'CPids
                          (erl-state->bind (proc->s (omap::lookup p net))))))
                  net)))))
      (r (erl-val-integer->val
            (omap::lookup 'Index
              (wtree-bind
                (omap::lookup
                  (rightmost-child
                    (car (erl-val-cons->lst
                          (omap::lookup 'CPids
                            (erl-state->bind (proc->s (omap::lookup p net))))))
                    net)
                  net))))))
    (:instance check-indices-props
      (cps (erl-val-cons->lst
              (omap::lookup 'CPids
                (erl-state->bind (proc->s (omap::lookup p net))))))
      (i (+ -1
            (erl-val-integer->val
              (omap::lookup 'Index
                (wtree-bind
                  (omap::lookup
                    (car (erl-val-cons->lst
                            (omap::lookup 'CPids
                              (erl-state->bind (proc->s (omap::lookup p net))))))
                    net))))))))))

; TODO: another huge lemma, but least it is fast.
; What proc recieve does for receive->blocked node.
; Thanks to this, I get a preformance improvement later,
; because I do not have to expand inv.
(local (defruled proc-receive-blocked-facts
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (pid-p p) (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (not (inbox-contains (proc->inbox-new (omap::lookup p net))
            (car (erl-val-cons->lst (omap::lookup 'CPids
              (erl-state->bind (proc->s (omap::lookup p net)))))))))
    (and
      (iff (omap::assoc 'Index
             (wtree-bind (proc-receive (omap::lookup p net))))
           (omap::assoc 'Index (wtree-bind (omap::lookup p net))))
      (iff (omap::assoc 'Parent
              (wtree-bind (proc-receive (omap::lookup p net))))
           (omap::assoc 'Parent (wtree-bind (omap::lookup p net))))
      (iff (omap::assoc 'ChildPids
              (wtree-bind (proc-receive (omap::lookup p net))))
           (omap::assoc 'ChildPids (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'Index
              (wtree-bind (proc-receive (omap::lookup p net))))
             (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'Parent
               (wtree-bind (proc-receive (omap::lookup p net))))
             (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'ChildPids
               (wtree-bind (proc-receive (omap::lookup p net))))
             (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))
      (equal (leaf-p (proc-receive (omap::lookup p net)))
             (leaf-p (omap::lookup p net)))
      (equal (root-p (proc-receive (omap::lookup p net)))
             (root-p (omap::lookup p net)))
      (iff (omap::assoc 'CPids
             (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
           (omap::assoc 'CPids
             (erl-state->bind (proc->s (omap::lookup p net)))))
      (equal (omap::lookup 'CPids
               (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
             (omap::lookup 'CPids
               (erl-state->bind (proc->s (omap::lookup p net)))))
      (equal
        (erl-state->self
          (proc->s (proc-receive (omap::lookup p net))))
        (erl-state->self (proc->s (omap::lookup p net))))
      (equal (erl-state->self (proc->s (proc-receive (omap::lookup p net)))) p)
      (equal (proc->ps (proc-receive (omap::lookup p net))) :blocked)
      (erl-klst-p (proc->klst (proc-receive (omap::lookup p net))))
      (consp
        (erl-val-cons->lst
          (omap::lookup 'ChildPids
            (wtree-bind (proc-receive (omap::lookup p net))))))
      (parent-still-waiting-p p
        (omap::lookup 'Parent
          (wtree-bind (proc-receive (omap::lookup p net)))) net)
      (not
        (equal
          (omap::lookup 'Parent
            (wtree-bind (proc-receive (omap::lookup p net)))) p))
      (equal
        (erl-val-kind
          (erl-state->in (proc->s (proc-receive (omap::lookup p net)))))
        :none)
      (equal (proc->outbox (proc-receive (omap::lookup p net))) nil)
      (equal (proc->inbox-new (proc-receive (omap::lookup p net))) nil)
      (equal (proc->inbox-tried (proc-receive (omap::lookup p net)))
             (proc->inbox-new (omap::lookup p net)))
      (equal (erl-state->world (proc->s (proc-receive (omap::lookup p net))))
             (sum-reduce-w))
      (equal (erl-state->module (proc->s (proc-receive (omap::lookup p net))))
             'local)
      (omap::assoc 'ParentPid
        (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
      (omap::assoc 'CPids
        (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
      (omap::assoc 'ChildHd
        (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
      (omap::assoc 'ChildTl
        (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
      (omap::assoc 'LeftTotal
        (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
      (not (omap::assoc 'RightTotal
             (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))))
      (> (erl-k->fuel (car (proc->klst (proc-receive (omap::lookup p net)))))
         (+ 100 (* 6 (len (erl-val-cons->lst
                            (omap::lookup 'CPids
                              (erl-state->bind
                                (proc->s (proc-receive (omap::lookup p net))))))))))
      (equal (omap::lookup 'ParentPid
                (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
             (omap::lookup 'Parent
                (wtree-bind (proc-receive (omap::lookup p net)))))
      (equal
        (erl-val-kind
          (omap::lookup 'CPids
            (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))))
        :cons)
      (consp (erl-val-cons->lst
               (omap::lookup 'CPids
                  (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))))
      (prefixp (rev (erl-val-cons->lst
                      (omap::lookup 'CPids
                        (erl-state->bind
                          (proc->s (proc-receive (omap::lookup p net)))))))
               (rev (erl-val-cons->lst
                      (omap::lookup 'ChildPids
                        (wtree-bind (proc-receive (omap::lookup p net)))))))
      (equal
        (omap::lookup 'ChildHd
          (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
        (car (erl-val-cons->lst
              (omap::lookup 'CPids
                (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))))))
      (equal
        (erl-val-kind
          (omap::lookup 'ChildTl
            (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))))
        :cons)
      (equal
        (erl-val-cons->lst
          (omap::lookup 'ChildTl
            (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))))
        (cdr (erl-val-cons->lst
                (omap::lookup 'CPids
                  (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))))))
      (omap::assoc
        (omap::lookup 'ChildHd
          (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))) net)
      (not
        (equal
          (omap::lookup 'ChildHd
            (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
        p))
      (leaf-p (omap::lookup
                (omap::lookup 'ChildHd
                  (erl-state->bind
                    (proc->s (proc-receive (omap::lookup p net))))) net))
      (< (erl-val-integer->val
            (omap::lookup 'Index
              (wtree-bind (proc-receive (omap::lookup p net)))))
         (erl-val-integer->val
           (omap::lookup 'Index
             (wtree-bind
              (omap::lookup
                (omap::lookup 'ChildHd
                  (erl-state->bind
                    (proc->s (proc-receive (omap::lookup p net)))))
                net)))))
      (equal
        (erl-val-kind
          (omap::lookup 'LeftTotal
            (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))))
        :integer)
      (equal  
        (erl-val-integer->val
          (omap::lookup 'LeftTotal
            (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))))
        (sum-range
          (erl-val-integer->val
            (omap::lookup 'Index (wtree-bind (proc-receive (omap::lookup p net)))))
          (1- (erl-val-integer->val
                (omap::lookup 'Index
                  (wtree-bind
                    (omap::lookup
                      (omap::lookup 'ChildHd
                        (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
                      net)))))))
      (received-messages-wf
        (proc->inbox-tried (proc-receive (omap::lookup p net)))
        (erl-val-cons->lst
          (omap::lookup 'CPids
            (erl-state->bind
              (proc->s (proc-receive (omap::lookup p net))))))
        net)
      (not
        (inbox-contains
          (proc->inbox-tried (proc-receive (omap::lookup p net)))
          (omap::lookup 'ChildHd
            (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))))
      (reduce-receive-klst-p
        (proc->klst (proc-receive (omap::lookup p net)))
        (omap::from-lists
          (list 'ChildPids 'Parent 'Index)
          (list
            (make-erl-val-cons
              :lst (erl-val-cons->lst
                     (omap::lookup 'ChildPids
                       (wtree-bind (proc-receive (omap::lookup p net))))))
            (omap::lookup 'Parent
              (wtree-bind (proc-receive (omap::lookup p net))))
            (make-erl-val-integer
              :val (erl-val-integer->val
                     (omap::lookup 'Index
                        (wtree-bind (proc-receive (omap::lookup p net)))))))))))
  :enable (proc->outbox proc->pid
    normalize-reduce-receive-klst-p)
  :disable
    (inv wtree-nodes-are-leaf-or-root omap::lookup-when-emptyp
     wtree-bind-when-no-function-return omap::assoc-when-assoc-tail
    (:type-prescription omap::emptyp) last lookup-when-outbox-emptyp
    (:type-prescription omap::assoc-when-emptyp) erl-val-kind-of-pid-p
    (:type-prescription omap::lookup-when-emptyp)
    consp-of-cdr-of-erl-vlst pid-p-when-member-equal-of-pid-lst-p)
  :use
    ((:instance inv-receive-node-facts)
     (:instance proc-receive-when-no-match
       (p (omap::lookup p net))
       (rbind (wtree-bind (omap::lookup p net))))
     (:instance wtree-nodes-are-leaf-or-root (pid p))
     (:instance parent-not-self-of-wtree
       (pid (car (erl-val-cons->lst
                  (omap::lookup 'CPids
                    (erl-state->bind
                      (proc->s (omap::lookup p net))))))))
    (:instance parent-not-self-of-wtree (pid p))
    (:instance wtree-bind-when-fields-equal
      (p1 (proc-receive (omap::lookup p net)))
      (p2 (omap::lookup p net)))
    (:instance leaf-root-p-when-wtree-bindings-equal
      (p1 (proc-receive (omap::lookup p net)))
      (p2 (omap::lookup p net))))))

; receive -> blocked, the message on top is not from ChildHd.
; Remark: Thanks to the painful lemmas above, this one is easy.
(local (defruled inv-of-receive-run-blocked
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
  :use ((:instance proc-receive-blocked-facts))))

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
    ((:instance consumed-message-facts)
     (:instance inv-receive-node-facts)
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

; facts about proc-receive with a matching message
(local (defruled proc-receive-match-facts
  (implies
    (and
      (network-p net) (wtree-p net) (pid-p p) (omap::assoc p net)
      (inv p net)
      (inv (car (erl-val-cons->lst (omap::lookup 'CPids
                  (erl-state->bind (proc->s (omap::lookup p net)))))) net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (inbox-contains (proc->inbox-new (omap::lookup p net))
        (car (erl-val-cons->lst (omap::lookup 'CPids
               (erl-state->bind (proc->s (omap::lookup p net)))))))
      (cdr (erl-val-cons->lst (omap::lookup 'CPids
             (erl-state->bind (proc->s (omap::lookup p net))))))
      (network-p (omap::update p (proc-receive (omap::lookup p net)) net)))
    (and
      (iff (omap::assoc 'Index 
             (wtree-bind (proc-receive (omap::lookup p net))))
           (omap::assoc 'Index (wtree-bind (omap::lookup p net))))
      (iff (omap::assoc 'Parent
             (wtree-bind (proc-receive (omap::lookup p net))))
           (omap::assoc 'Parent (wtree-bind (omap::lookup p net))))
      (iff (omap::assoc 'ChildPids
             (wtree-bind (proc-receive (omap::lookup p net))))
           (omap::assoc 'ChildPids (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'Index
               (wtree-bind (proc-receive (omap::lookup p net))))
             (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'Parent
                (wtree-bind (proc-receive (omap::lookup p net))))
             (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'ChildPids
                (wtree-bind (proc-receive (omap::lookup p net))))
             (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))
      (equal (erl-state->self (proc->s (proc-receive (omap::lookup p net))))
             (erl-state->self (proc->s (omap::lookup p net))))
      (equal (proc->ps (proc-receive (omap::lookup p net))) :receive)
      (erl-klst-p (proc->klst (proc-receive (omap::lookup p net))))
      (consp (erl-val-cons->lst (omap::lookup 'ChildPids
               (wtree-bind (proc-receive (omap::lookup p net))))))
      (parent-still-waiting-p p
        (omap::lookup 'Parent
          (wtree-bind (proc-receive (omap::lookup p net))))
        net)
      (not
        (equal
          (omap::lookup 'Parent
            (wtree-bind (proc-receive (omap::lookup p net)))) p))
      (equal
        (erl-val-kind
          (erl-state->in (proc->s (proc-receive (omap::lookup p net)))))
        :none)
      (equal (proc->outbox (proc-receive (omap::lookup p net))) nil)
      (equal (proc->inbox-tried (proc-receive (omap::lookup p net))) nil)
      (equal (erl-state->world (proc->s (proc-receive (omap::lookup p net))))
             (sum-reduce-w))
      (equal (erl-state->module (proc->s (proc-receive (omap::lookup p net))))
             'local)
      (omap::assoc 'ParentPid
        (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
      (omap::assoc 'CPids
        (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
      (omap::assoc 'ChildHd
        (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
      (omap::assoc 'ChildTl
        (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
      (omap::assoc 'LeftTotal
        (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
      (not (omap::assoc 'RightTotal
             (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))))
      (> (erl-k->fuel (car (proc->klst (proc-receive (omap::lookup p net)))))
         (+ 100 (* 6 (len (erl-val-cons->lst
                            (omap::lookup 'CPids
                              (erl-state->bind
                                (proc->s (proc-receive (omap::lookup p net))))))))))
      (equal (omap::lookup 'ParentPid
               (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
             (omap::lookup 'Parent
               (wtree-bind (proc-receive (omap::lookup p net)))))
      (equal (erl-val-kind
               (omap::lookup 'CPids
                 (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))))
             :cons)
      (consp (erl-val-cons->lst
               (omap::lookup 'CPids
                 (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))))
      (prefixp (rev (erl-val-cons->lst
                      (omap::lookup 'CPids
                        (erl-state->bind
                          (proc->s (proc-receive (omap::lookup p net)))))))
               (rev (erl-val-cons->lst
                      (omap::lookup 'ChildPids
                        (wtree-bind (proc-receive (omap::lookup p net)))))))
      (equal (omap::lookup 'ChildHd
               (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
             (car (erl-val-cons->lst
                    (omap::lookup 'CPids
                      (erl-state->bind
                        (proc->s (proc-receive (omap::lookup p net))))))))
      (equal (erl-val-kind
               (omap::lookup 'ChildTl
                 (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))))
             :cons)
      (equal (erl-val-cons->lst
               (omap::lookup 'ChildTl
                 (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))))
             (cdr (erl-val-cons->lst
                    (omap::lookup 'CPids
                      (erl-state->bind
                        (proc->s (proc-receive (omap::lookup p net))))))))
      (omap::assoc
        (omap::lookup 'ChildHd
          (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
        net)
      (not
        (equal
          (omap::lookup 'ChildHd
            (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))) p))
      (leaf-p (omap::lookup
                (omap::lookup 'ChildHd
                  (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
                net))
      (< (erl-val-integer->val
           (omap::lookup 'Index (wtree-bind (proc-receive (omap::lookup p net)))))
         (erl-val-integer->val
           (omap::lookup 'Index
             (wtree-bind (omap::lookup
                           (omap::lookup 'ChildHd
                             (erl-state->bind
                               (proc->s (proc-receive (omap::lookup p net)))))
                           net)))))
      (equal (erl-val-kind
               (omap::lookup 'LeftTotal
                 (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))))
             :integer)
      (equal (erl-val-integer->val
               (omap::lookup 'LeftTotal
                 (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))))
             (sum-range
               (erl-val-integer->val
                 (omap::lookup 'Index
                   (wtree-bind (proc-receive (omap::lookup p net)))))
               (1- (erl-val-integer->val
                     (omap::lookup 'Index
                       (wtree-bind (omap::lookup
                                     (omap::lookup 'ChildHd
                                       (erl-state->bind
                                         (proc->s
                                           (proc-receive (omap::lookup p net)))))
                                     net)))))))
      (received-messages-wf
        (proc->inbox-new (proc-receive (omap::lookup p net)))
        (erl-val-cons->lst
          (omap::lookup 'CPids
            (erl-state->bind (proc->s (proc-receive (omap::lookup p net))))))
        net)
      (reduce-receive-klst-p
        (proc->klst (proc-receive (omap::lookup p net)))
        (omap::from-lists
          (list 'ChildPids 'Parent 'Index)
          (list
            (make-erl-val-cons
              :lst (erl-val-cons->lst
                     (omap::lookup 'ChildPids
                       (wtree-bind (proc-receive (omap::lookup p net))))))
            (omap::lookup 'Parent
              (wtree-bind (proc-receive (omap::lookup p net))))
            (make-erl-val-integer
              :val (erl-val-integer->val
                     (omap::lookup 'Index
                       (wtree-bind (proc-receive (omap::lookup p net)))))))))))
  :enable (proc->outbox proc->pid)
  :disable (equal-of-kont-function-return len)
  :use
    ((:instance consumed-message-facts)
     (:instance prefixp-of-rev-of-cdr
       (l (erl-val-cons->lst
            (omap::lookup 'CPids
              (erl-state->bind (proc->s (omap::lookup p net))))))
       (x (rev (erl-val-cons->lst
                 (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))))
     (:instance inv-receive-node-facts)
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
                      :lst (erl-val-cons->lst
                             (omap::lookup 'ChildPids
                               (wtree-bind (omap::lookup p net)))))
                    (omap::lookup 'Parent (wtree-bind (omap::lookup p net)))
                    (make-erl-val-integer
                      :val (erl-val-integer->val
                             (omap::lookup 'Index
                               (wtree-bind (omap::lookup p net)))))))))))))

; inv dor receive -> receive
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
  :enable inv-of-update-of-receive
  :use proc-receive-match-facts))

; When there is a single child left, that child is the rightmost child
(local (defruled rightmost-child-of-last-child
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (null (cdr (erl-val-cons->lst (omap::lookup 'CPids
                   (erl-state->bind (proc->s (omap::lookup p net))))))))
    (and
      (equal (rightmost-child p net)
             (rightmost-child
               (car (erl-val-cons->lst (omap::lookup 'CPids
                      (erl-state->bind (proc->s (omap::lookup p net)))))) net))
      (rightmost-child p net)))
  :use ((:instance inv-receive-node-facts)
        (:instance wtree-nodes-are-leaf-or-root (pid p))
        (:instance rightmost-child-of-parent-is-rightmost-of-last-child (pid p))
        (:instance rightmost-child-of-wtree-node (pid p)))
  :prep-lemmas
    ((defrule car-of-rev-is-car-of-last
       (equal (car (rev l)) (car (last l)))
       :enable rev)
     (defrule last-of-singleton-suffix
       (implies
         (and (prefixp (rev cps) (rev children)) (consp cps) (null (cdr cps))
              children)
         (equal (car (last children)) (car cps)))
       :enable prefixp))))

; What a terminated node satisfies if inv holds
(local (defruled termianted-node-facts
  (implies
    (and
      (network-p net) (pid-p p) (inv p net) (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :terminated)
      (leaf-p (omap::lookup p net)))
    (and
      (omap::assoc (rightmost-child p net) net)
      (leaf-p (omap::lookup (rightmost-child p net) net))
      (<= (erl-val-integer->val
            (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
          (erl-val-integer->val
            (omap::lookup 'Index
              (wtree-bind (omap::lookup (rightmost-child p net) net)))))
      (equal (erl-val-kind (erl-state->in (proc->s (omap::lookup p net))))
             :integer)
      (equal (erl-val-integer->val
               (erl-state->in (proc->s (omap::lookup p net))))
             (sum-range
               (erl-val-integer->val
                 (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
               (erl-val-integer->val
                 (omap::lookup 'Index
                   (wtree-bind
                     (omap::lookup (rightmost-child p net) net))))))))
  :use inv-terminated-node-facts))


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

; sum contained by a terminated node
(local (defruled terminated-node-sum
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
      (equal (rightmost-child p net)
             (rightmost-child
               (car (erl-val-cons->lst (omap::lookup 'CPids
                      (erl-state->bind (proc->s (omap::lookup p net)))))) net)))
    (and
      (omap::assoc (rightmost-child p net) net)
      (leaf-p (omap::lookup (rightmost-child p net) net))
      (< (erl-val-integer->val
           (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
         (erl-val-integer->val
           (omap::lookup 'Index
             (wtree-bind (omap::lookup (rightmost-child p net) net)))))
      (equal (erl-val-kind
               (inbox->value (proc->inbox-new (omap::lookup p net))
                 (car (erl-val-cons->lst (omap::lookup 'CPids
                        (erl-state->bind (proc->s (omap::lookup p net))))))))
             :integer)
      (equal (+ (erl-val-integer->val
                  (omap::lookup 'LeftTotal
                    (erl-state->bind (proc->s (omap::lookup p net)))))
                (erl-val-integer->val
                  (inbox->value (proc->inbox-new (omap::lookup p net))
                    (car (erl-val-cons->lst (omap::lookup 'CPids
                           (erl-state->bind
                             (proc->s (omap::lookup p net)))))))))
             (sum-range
               (erl-val-integer->val
                 (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
               (erl-val-integer->val
                 (omap::lookup 'Index
                   (wtree-bind
                     (omap::lookup (rightmost-child p net) net))))))))
  :use ((:instance inv-receive-node-facts)
        (:instance termianted-node-facts
          (p (car (erl-val-cons->lst (omap::lookup 'CPids
                    (erl-state->bind (proc->s (omap::lookup p net))))))))
        (:instance received-messages-wf-fields
          (pid (car (erl-val-cons->lst (omap::lookup 'CPids
                      (erl-state->bind (proc->s (omap::lookup p net)))))))
          (inbox (proc->inbox-new (omap::lookup p net)))
          (cpids (erl-val-cons->lst (omap::lookup 'CPids
                   (erl-state->bind (proc->s (omap::lookup p net)))))))
        (:instance wtree-nodes-are-leaf-or-root (pid p)))))

; sum contained by a node is going from receive -> terminated
(local (defruled terminating-node-sum
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
                   (erl-state->bind (proc->s (omap::lookup p net))))))))
    (and
      (omap::assoc (rightmost-child p net) net)
      (leaf-p (omap::lookup (rightmost-child p net) net))
      (< (erl-val-integer->val
           (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
         (erl-val-integer->val
           (omap::lookup 'Index
             (wtree-bind (omap::lookup (rightmost-child p net) net)))))
      (equal (erl-val-kind
               (inbox->value (proc->inbox-new (omap::lookup p net))
                 (car (erl-val-cons->lst (omap::lookup 'CPids
                        (erl-state->bind (proc->s (omap::lookup p net))))))))
             :integer)
      (equal (+ (erl-val-integer->val
                  (omap::lookup 'LeftTotal
                    (erl-state->bind (proc->s (omap::lookup p net)))))
                (erl-val-integer->val
                  (inbox->value (proc->inbox-new (omap::lookup p net))
                    (car (erl-val-cons->lst (omap::lookup 'CPids
                           (erl-state->bind
                             (proc->s (omap::lookup p net)))))))))
             (sum-range
               (erl-val-integer->val
                 (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
               (erl-val-integer->val
                 (omap::lookup 'Index
                   (wtree-bind
                     (omap::lookup (rightmost-child p net) net))))))
      (null (inbox-without (proc->inbox-new (omap::lookup p net))
              (car (erl-val-cons->lst (omap::lookup 'CPids
                     (erl-state->bind (proc->s (omap::lookup p net))))))))))
  :use ((:instance wtree-nodes-are-leaf-or-root (pid p))
        (:instance rightmost-child-of-last-child)
        (:instance terminated-node-sum)
        (:instance inv-receive-node-facts)
        (:instance received-messages-wf-of-inbox-without-car
          (inbox (proc->inbox-new (omap::lookup p net)))
          (cpids (erl-val-cons->lst (omap::lookup 'CPids
                   (erl-state->bind (proc->s (omap::lookup p net)))))))
        (:instance received-messages-wf-of-nil
          (inbox (inbox-without (proc->inbox-new (omap::lookup p net))
                   (car (erl-val-cons->lst (omap::lookup 'CPids
                          (erl-state->bind
                            (proc->s (omap::lookup p net))))))))))))

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
        (:instance inv-receive-node-facts)
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

; the other nodes are not affected by the run step starting from receive
(local (defrule inv-of-receive-run-other-blocked
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
  :use ((:instance inv-of-update-of-running-node
          (proc (proc-receive (omap::lookup p net))))
        (:instance proc-receive-blocked-facts)
        (:instance inv-node-parent-props)
        (:instance inv-receive-node-facts)
        (:instance sent-message-wf-of-update-of-receive-to-blocked
          (proc (proc-receive (omap::lookup p net)))))))

;  proc receive of receive -> terminate
(local (defruled proc-receive-terminate-props
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (inbox-contains (proc->inbox-new (omap::lookup p net))
        (car (erl-val-cons->lst (omap::lookup 'CPids
               (erl-state->bind (proc->s (omap::lookup p net)))))))
      (null (cdr (erl-val-cons->lst (omap::lookup 'CPids
                   (erl-state->bind (proc->s (omap::lookup p net)))))))
      (equal (erl-val-kind
               (inbox->value (proc->inbox-new (omap::lookup p net))
                 (car (erl-val-cons->lst (omap::lookup 'CPids
                        (erl-state->bind (proc->s (omap::lookup p net))))))))
             :integer))
    (and
      (equal (erl-state->self (proc->s (proc-receive (omap::lookup p net)))) p)
      (equal (omap::lookup 'Index
               (wtree-bind (proc-receive (omap::lookup p net))))
             (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'Parent
               (wtree-bind (proc-receive (omap::lookup p net))))
             (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
      (equal (omap::lookup 'ChildPids
               (wtree-bind (proc-receive (omap::lookup p net))))
             (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))
      (iff (omap::assoc 'Index
             (wtree-bind (proc-receive (omap::lookup p net))))
           (omap::assoc 'Index (wtree-bind (omap::lookup p net))))
      (iff (omap::assoc 'Parent
             (wtree-bind (proc-receive (omap::lookup p net))))
           (omap::assoc 'Parent (wtree-bind (omap::lookup p net))))
      (iff (omap::assoc 'ChildPids
             (wtree-bind (proc-receive (omap::lookup p net))))
           (omap::assoc 'ChildPids (wtree-bind (omap::lookup p net))))
      (equal (leaf-p (proc-receive (omap::lookup p net)))
             (leaf-p (omap::lookup p net)))
      (equal (root-p (proc-receive (omap::lookup p net)))
             (root-p (omap::lookup p net)))
      (equal (proc->ps (proc-receive (omap::lookup p net))) :terminated)))
  :enable normalize-reduce-receive-klst-p
  :use ((:instance proc-receive-of-match-without-more-children
          (p (omap::lookup p net))
          (rbind (wtree-bind (omap::lookup p net))))
        (:instance inv-receive-node-facts)
        (:instance wtree-nodes-are-leaf-or-root (pid p))
        (:instance leaf-root-p-when-wtree-bindings-equal
          (p1 (proc-receive (omap::lookup p net))) (p2 (omap::lookup p net))))))

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
    ((:instance inv-of-update-of-running-node
      (proc (proc-receive (omap::lookup p net))))
     (:instance proc-receive-terminate-props)
     (:instance inv-node-parent-props)
     (:instance inv-receive-node-facts)
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
    ((:instance inv-of-receive-run-blocked)
     (:instance inv-of-receive-to-terminated))))



; HERE ==================================================================================