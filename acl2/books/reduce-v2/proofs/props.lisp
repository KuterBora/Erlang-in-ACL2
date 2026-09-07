
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


; BOZO: This is the worst file in the project
; This file contains a very shameful, but (for the moment) wokring
; way to avoid enable and expand hints in run.lips that cause performance
; problems. They are all disabled theorems about what a function returns
; when run with very specific arguments. However, before I try clean this
; up, I would rather make changes to my representation of wtree and inv
; that might avoid most of these to begin with.

; Even now, some of these can easily be merged or deleted completely.  

(local (defruled inv-idle-node-props
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

; facts about inv of a receive node.
; This way I don't need to expand all cases of inv
(defruled inv-receive-node-props
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
  :enable inv)

; facts about inv of a terminated node.
; This way I don't need to expand all cases of inv
(local (defruled inv-terminated-node-props
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
(defruled consumed-message-props
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
    ((:instance inv-receive-node-props)
     (:instance wtree-nodes-are-leaf-or-root (pid p))
     (:instance check-indices-of-wtree-node (pid p))
     (:instance inv-terminated-node-props
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
                    net)))))))))

; TODO: another huge lemma, but least it is fast.
; What proc recieve does for receive->blocked node.
; Thanks to this, I get a preformance improvement later,
; because I do not have to expand inv.
(defruled proc-receive-blocked-props
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
    ((:instance inv-receive-node-props)
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
      (p2 (omap::lookup p net)))))

; facts about proc-receive with a matching message
(defruled proc-receive-match-props
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
    ((:instance consumed-message-props)
     (:instance prefixp-of-rev-of-cdr
       (l (erl-val-cons->lst
            (omap::lookup 'CPids
              (erl-state->bind (proc->s (omap::lookup p net))))))
       (x (rev (erl-val-cons->lst
                 (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))))
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
                      :lst (erl-val-cons->lst
                             (omap::lookup 'ChildPids
                               (wtree-bind (omap::lookup p net)))))
                    (omap::lookup 'Parent (wtree-bind (omap::lookup p net)))
                    (make-erl-val-integer
                      :val (erl-val-integer->val
                             (omap::lookup 'Index
                               (wtree-bind (omap::lookup p net))))))))))))


; What a terminated node satisfies if inv holds
(defruled terminated-node-props
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
  :use inv-terminated-node-props)


; sum contained by a terminated node
(defruled terminated-node-sum
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
  :use ((:instance inv-receive-node-props)
        (:instance terminated-node-props
          (p (car (erl-val-cons->lst (omap::lookup 'CPids
                    (erl-state->bind (proc->s (omap::lookup p net))))))))
        (:instance received-messages-wf-fields
          (pid (car (erl-val-cons->lst (omap::lookup 'CPids
                      (erl-state->bind (proc->s (omap::lookup p net)))))))
          (inbox (proc->inbox-new (omap::lookup p net)))
          (cpids (erl-val-cons->lst (omap::lookup 'CPids
                   (erl-state->bind (proc->s (omap::lookup p net)))))))
        (:instance wtree-nodes-are-leaf-or-root (pid p))))

; When there is a single child left, that child is the rightmost child
(defruled rightmost-child-of-last-child
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
  :use ((:instance inv-receive-node-props)
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
       :enable prefixp)))

; sum contained by a node is going from receive -> terminated
(defruled terminating-node-sum
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
        (:instance inv-receive-node-props)
        (:instance received-messages-wf-of-inbox-without-car
          (inbox (proc->inbox-new (omap::lookup p net)))
          (cpids (erl-val-cons->lst (omap::lookup 'CPids
                   (erl-state->bind (proc->s (omap::lookup p net)))))))
        (:instance received-messages-wf-of-nil
          (inbox (inbox-without (proc->inbox-new (omap::lookup p net))
                   (car (erl-val-cons->lst (omap::lookup 'CPids
                          (erl-state->bind
                            (proc->s (omap::lookup p net)))))))))))

;  proc receive of receive -> terminate
(defruled proc-receive-terminate-props
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
        (:instance inv-receive-node-props)
        (:instance wtree-nodes-are-leaf-or-root (pid p))
        (:instance leaf-root-p-when-wtree-bindings-equal
          (p1 (proc-receive (omap::lookup p net))) (p2 (omap::lookup p net)))))


; props of proc-receive after a message match
(defruled proc-receive-match-node-type
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (inbox-contains
        (proc->inbox-new (omap::lookup p net))
        (car (erl-val-cons->lst
               (omap::lookup 'CPids
                 (erl-state->bind
                   (proc->s (omap::lookup p net)))))))
      (cdr (erl-val-cons->lst
             (omap::lookup 'CPids
               (erl-state->bind (proc->s (omap::lookup p net))))))
      (equal
        (erl-val-kind
          (inbox->value
            (proc->inbox-new
              (omap::lookup p net))
            (car
              (erl-val-cons->lst
                (omap::lookup
                  'CPids
                  (erl-state->bind
                    (proc->s (omap::lookup p net))))))))
             :integer)
      (inv
        (car (erl-val-cons->lst
               (omap::lookup 'CPids
                 (erl-state->bind (proc->s (omap::lookup p net))))))
        net)
      (network-p (omap::update p (proc-receive (omap::lookup p net)) net)))
    (and
      (equal (erl-state->self (proc->s (proc-receive (omap::lookup p net)))) p)
      (equal (leaf-p (proc-receive (omap::lookup p net)))
             (leaf-p (omap::lookup p net)))
      (equal (root-p (proc-receive (omap::lookup p net)))
             (root-p (omap::lookup p net)))))
  :use
    ((:instance proc-receive-match-props)
     (:instance proc-receive-of-match-with-more-children
       (p (omap::lookup p net)) (rbind (wtree-bind (omap::lookup p net))))
     (:instance inv-receive-node-props)
     (:instance wtree-nodes-are-leaf-or-root (pid p))
     (:instance leaf-root-p-when-wtree-bindings-equal
                 (p1 (proc-receive (omap::lookup p net)))
                 (p2 (omap::lookup p net)))))


; The inbox is the same but with ChildHd removed.
(defruled proc-receive-match-inbox
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (omap::assoc p net) 
      (equal (proc->ps (omap::lookup p net)) :receive)
      (inbox-contains
        (proc->inbox-new (omap::lookup p net))
        (car (erl-val-cons->lst
                (omap::lookup 'CPids
                              (erl-state->bind
                                (proc->s (omap::lookup p net)))))))
      (cdr (erl-val-cons->lst
            (omap::lookup 'CPids
              (erl-state->bind (proc->s (omap::lookup p net))))))
      (equal
        (erl-val-kind
          (inbox->value
            (proc->inbox-new (omap::lookup p net))
            (car (erl-val-cons->lst
                   (omap::lookup 'CPids
                      (erl-state->bind
                        (proc->s (omap::lookup p net))))))))
        :integer)
      (inv (car (erl-val-cons->lst
                  (omap::lookup 'CPids
                    (erl-state->bind (proc->s (omap::lookup p net))))))
           net)
      (network-p (omap::update p (proc-receive (omap::lookup p net)) net)))
    (equal (proc->inbox-new (proc-receive (omap::lookup p net)))
           (inbox-without
              (proc->inbox-new (omap::lookup p net))
              (car (erl-val-cons->lst
                      (omap::lookup 'CPids
                        (erl-state->bind (proc->s (omap::lookup p net)))))))))
  :disable
    (assoc-of-runnable? omap::assoc-when-assoc-tail omap::tail-when-emptyp
     omap::assoc-when-assoc-of-tail-cheap root-when-assoc-of-tail-is-root
     runnable-of-tail leaf-when-assoc-of-tail-is-leaf omap::lookup-when-emptyp
     omap::assoc-when-emptyp assoc-of-non-root-segment leaf-equiv-when-bindings-equiv
     root-equiv-when-bindings-equiv wtree0-nodes-are-leaf-or-root
     wtree0-nodes-are-leaf-or-root-rev wtree0-of-zero reduce-receive-klst-p
     len inv equal-of-kont-function-return)
  :use
    ((:instance proc-receive-match-props)
     (:instance normalize-reduce-receive-klst-p
      (p (omap::lookup p net))
      (rbind (omap::from-lists
               (list 'ChildPids 'Parent 'Index)
               (list (make-erl-val-cons
                        :lst (erl-val-cons->lst
                               (omap::lookup 'ChildPids
                                 (wtree-bind (omap::lookup p net)))))
                     (omap::lookup 'Parent
                       (wtree-bind (omap::lookup p net)))
                     (make-erl-val-integer
                       :val (erl-val-integer->val
                              (omap::lookup 'Index
                                (wtree-bind (omap::lookup p net)))))))))
      (:instance proc-receive-of-match-with-more-children
                 (p (omap::lookup p net))
                 (rbind (wtree-bind (omap::lookup p net))))
      (:instance inv-receive-node-props)
      (:instance wtree-nodes-are-leaf-or-root (pid p))
      (:instance leaf-root-p-when-wtree-bindings-equal
                 (p1 (proc-receive (omap::lookup p net)))
                 (p2 (omap::lookup p net)))))


; The CPids are the same but with ChildHd removed.
(defruled proc-receive-match-cpids
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (inbox-contains
        (proc->inbox-new (omap::lookup p net))
        (car (erl-val-cons->lst
                (omap::lookup 'CPids
                              (erl-state->bind
                                (proc->s (omap::lookup p net)))))))
      (cdr (erl-val-cons->lst
              (omap::lookup 'CPids
                (erl-state->bind (proc->s (omap::lookup p net))))))
      (equal
        (erl-val-kind
          (inbox->value
            (proc->inbox-new (omap::lookup p net))
            (car
              (erl-val-cons->lst
                (omap::lookup
                  'CPids
                  (erl-state->bind
                    (proc->s (omap::lookup p net))))))))
          :integer)
      (inv (car (erl-val-cons->lst
                  (omap::lookup 'CPids
                    (erl-state->bind (proc->s (omap::lookup p net))))))
           net)
      (network-p (omap::update p (proc-receive (omap::lookup p net)) net)))
    (equal (erl-val-cons->lst
             (omap::lookup 'CPids
               (erl-state->bind
                 (proc->s (proc-receive (omap::lookup p net))))))
           (cdr (erl-val-cons->lst
                  (omap::lookup 'CPids
                    (erl-state->bind (proc->s (omap::lookup p net))))))))
  :disable
    (assoc-of-runnable? omap::assoc-when-assoc-tail omap::tail-when-emptyp
     omap::assoc-when-assoc-of-tail-cheap root-when-assoc-of-tail-is-root
     runnable-of-tail leaf-when-assoc-of-tail-is-leaf omap::lookup-when-emptyp
     omap::assoc-when-emptyp assoc-of-non-root-segment leaf-equiv-when-bindings-equiv
     root-equiv-when-bindings-equiv wtree0-nodes-are-leaf-or-root
     wtree0-nodes-are-leaf-or-root-rev wtree0-of-zero reduce-receive-klst-p
     len inv equal-of-kont-function-return)
  :use
    ((:instance proc-receive-match-props)
     (:instance normalize-reduce-receive-klst-p
      (p (omap::lookup p net))
      (rbind (omap::from-lists
               (list 'ChildPids 'Parent 'Index)
               (list (make-erl-val-cons
                        :lst (erl-val-cons->lst
                               (omap::lookup 'ChildPids
                                 (wtree-bind (omap::lookup p net)))))
                     (omap::lookup 'Parent
                       (wtree-bind (omap::lookup p net)))
                     (make-erl-val-integer
                       :val (erl-val-integer->val
                              (omap::lookup 'Index
                                (wtree-bind (omap::lookup p net)))))))))
      (:instance proc-receive-of-match-with-more-children
                 (p (omap::lookup p net))
                 (rbind (wtree-bind (omap::lookup p net))))
      (:instance inv-receive-node-props)
      (:instance wtree-nodes-are-leaf-or-root (pid p))
      (:instance leaf-root-p-when-wtree-bindings-equal
                 (p1 (proc-receive (omap::lookup p net)))
                 (p2 (omap::lookup p net)))))

; TODO: I thought of removing this after proving the three helpers aboove.
; However, instances of those do not help with perfomance despite what I expect.
(defruled proc-receive-match-more-props
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (inbox-contains
        (proc->inbox-new (omap::lookup p net))
        (car (erl-val-cons->lst
                (omap::lookup 'CPids
                              (erl-state->bind
                                (proc->s (omap::lookup p net)))))))
      (cdr (erl-val-cons->lst
              (omap::lookup 'CPids
                (erl-state->bind (proc->s (omap::lookup p net))))))
      (equal
        (erl-val-kind
          (inbox->value
            (proc->inbox-new (omap::lookup p net))
            (car
              (erl-val-cons->lst
                (omap::lookup 'CPids
                  (erl-state->bind
                    (proc->s (omap::lookup p net))))))))
        :integer)
      (inv (car (erl-val-cons->lst
                  (omap::lookup 'CPids
                    (erl-state->bind (proc->s (omap::lookup p net))))))
           net)
      (network-p (omap::update p (proc-receive (omap::lookup p net)) net)))
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
      (equal (leaf-p (proc-receive (omap::lookup p net)))
             (leaf-p (omap::lookup p net)))
      (equal (root-p (proc-receive (omap::lookup p net)))
             (root-p (omap::lookup p net)))
      (equal (proc->ps (proc-receive (omap::lookup p net))) :receive)
      (null (proc->inbox-tried (proc-receive (omap::lookup p net))))
      (equal (proc->inbox-new (proc-receive (omap::lookup p net)))
             (inbox-without
               (proc->inbox-new (omap::lookup p net))
               (car (erl-val-cons->lst
                      (omap::lookup 'CPids
                        (erl-state->bind (proc->s (omap::lookup p net))))))))
      (omap::assoc 'CPids
                   (erl-state->bind (proc->s (proc-receive (omap::lookup p net)))))
      (equal
        (erl-val-kind
          (omap::lookup 'CPids
            (erl-state->bind
              (proc->s (proc-receive (omap::lookup p net))))))
        :cons)
      (equal
        (erl-val-cons->lst
          (omap::lookup 'CPids
            (erl-state->bind
              (proc->s (proc-receive (omap::lookup p net))))))
              (cdr (erl-val-cons->lst
                      (omap::lookup 'CPids
                        (erl-state->bind (proc->s (omap::lookup p net)))))))))
  :disable (inv equal-of-kont-function-return)
  :use
    ((:instance proc-receive-match-props)
     (:instance proc-receive-match-node-type)
     (:instance proc-receive-match-inbox)
     (:instance proc-receive-match-cpids)))

; Value of idle -> receive
(defruled idle-to-receive-val
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net) (pid-p p)
      (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :idle)
      (erl-val-cons->lst
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))
    (and
      (equal
        (erl-val-kind
          (erl-state->in
            (apply-k
              (proc->s (omap::lookup p net))
              (proc->klst (omap::lookup p net)))))
        :receive)
      (erl-klst-p
        (erl-val-receive->klst
          (erl-state->in
            (apply-k
              (proc->s (omap::lookup p net))
              (proc->klst (omap::lookup p net))))))))
  :cases ((leaf-p (omap::lookup p net)))
  :disable (equal-of-kont-function-return wtree-bind)
  :use
    ((:instance inv-idle-node-props)
     (:instance apply-k-of-idle-with-children
      (s (proc->s (omap::lookup p net)))
      (klst (proc->klst (omap::lookup p net)))
      (self p)
      (parent (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
      (children (erl-val-cons->lst
                  (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))
      (index (erl-val-integer->val
              (omap::lookup 'Index (wtree-bind (omap::lookup p net))))))
     (:instance wtree-nodes-are-leaf-or-root (pid p))
     (:instance wtree-node-fields (p (omap::lookup p net)))))

; Chd does not occur again.
(defruled chd-not-in-rest-of-cpids
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :receive))
    (not
      (member-equal
        (car (erl-val-cons->lst
               (omap::lookup 'CPids
                 (erl-state->bind (proc->s (omap::lookup p net))))))
        (cdr (erl-val-cons->lst
                (omap::lookup 'CPids
                  (erl-state->bind (proc->s (omap::lookup p net)))))))))
  :disable (inv equal-of-kont-function-return)
  :use ((:instance inv-receive-node-props)
        (:instance wtree-nodes-are-leaf-or-root (pid p))
        (:instance check-children-of-wtree-node (pid p))
        (:instance no-duplicatesp-of-check-children
          (pid p) (children
                    (erl-val-cons->lst
                        (omap::lookup 'ChildPids
                                (wtree-bind (omap::lookup p net))))))
        (:instance no-duplicatesp-of-rev
          (l (erl-val-cons->lst
               (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))))
        (:instance no-duplicatesp-of-rev
          (l (erl-val-cons->lst
               (omap::lookup 'CPids
                 (erl-state->bind (proc->s (omap::lookup p net))))))))
  :prep-lemmas
    ((defrule no-duplicatesp-of-prefix
      (implies (and (prefixp x y) (no-duplicatesp-equal y))
                (no-duplicatesp-equal x))
      :enable prefixp
      :prep-lemmas
        ((defrule member-of-prefix
          (implies (and (prefixp x y) (member-equal e x)) (member-equal e y))
          :enable prefixp)))))


; Bindings of idle -> receive
(defruled idle-to-receive-bind
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (pid-p p) (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :idle)
      (erl-val-cons->lst
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))
    (and
      (equal
        (erl-state->self
          (proc->s
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
                          (proc->klst (omap::lookup p net))))))))
        p)
      (equal
        (omap::lookup 'Index
          (wtree-bind
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
                          (proc->klst (omap::lookup p net))))))))
        (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
      (equal
        (omap::lookup 'Parent
          (wtree-bind
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
                          (proc->klst (omap::lookup p net))))))))
        (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
      (equal
        (omap::lookup 'ChildPids
          (wtree-bind
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
                          (proc->klst (omap::lookup p net))))))))
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))
      (iff
        (omap::assoc 'Index
          (wtree-bind
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
                          (proc->klst (omap::lookup p net))))))))
          (omap::assoc 'Index (wtree-bind (omap::lookup p net))))
      (iff
        (omap::assoc 'Parent
          (wtree-bind
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
                          (proc->klst (omap::lookup p net))))))))
          (omap::assoc 'Parent (wtree-bind (omap::lookup p net))))
      (iff
        (omap::assoc 'ChildPids
          (wtree-bind
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
                          (proc->klst (omap::lookup p net))))))))
          (omap::assoc 'ChildPids (wtree-bind (omap::lookup p net))))
      (equal
        (proc->ps
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
                          (proc->klst (omap::lookup p net)))))))
        :receive)
      (equal
        (proc->inbox-new
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
                          (proc->klst (omap::lookup p net)))))))
        (proc->inbox-new (omap::lookup p net)))
      (equal
        (proc->inbox-tried
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
                          (proc->klst (omap::lookup p net)))))))
        (proc->inbox-tried (omap::lookup p net)))
      (omap::assoc 'CPids
        (erl-state->bind
          (proc->s
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
                          (proc->klst (omap::lookup p net)))))))))
      (equal
        (erl-val-kind
          (omap::lookup 'CPids
            (erl-state->bind
              (proc->s
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
                              (proc->klst (omap::lookup p net))))))))))
                :cons)
      (equal
        (erl-val-cons->lst
          (omap::lookup 'CPids
            (erl-state->bind
              (proc->s
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
                              (proc->klst (omap::lookup p net))))))))))
        (erl-val-cons->lst
          (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))))
  :disable
    (equal-of-kont-function-return wtree-bind  parent-of-root
     wtree-bind-when-no-function-return index-of-root parent-of-leaf
     wtree-bind0-when-no-function-return index-of-leaf)
  :use
    ((:instance inv-idle-node-props)
     (:instance apply-k-of-idle-with-children
       (s (proc->s (omap::lookup p net)))
       (klst (proc->klst (omap::lookup p net)))
       (self p)
       (parent (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
       (children (erl-val-cons->lst
                   (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))
       (index (erl-val-integer->val
                (omap::lookup 'Index (wtree-bind (omap::lookup p net))))))
     (:instance wtree-nodes-are-leaf-or-root (pid p))
     (:instance wtree-node-fields (p (omap::lookup p net)))))

; Leaf or Root of idle -> receive
(defruled idle-to-receive-leaf-or-root
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (pid-p p) (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :idle)
      (erl-val-cons->lst
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))
    (and
      (equal
        (leaf-p
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
                          (proc->klst (omap::lookup p net)))))))
        (leaf-p (omap::lookup p net)))
      (equal
        (root-p
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
                          (proc->klst (omap::lookup p net)))))))
        (root-p (omap::lookup p net)))))
  :use
    ((:instance idle-to-receive-bind)
     (:instance leaf-root-p-when-wtree-bindings-equal
      (p1 (change-proc  (omap::lookup p net)
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
                        (proc->klst (omap::lookup p net)))))))
      (p2 (omap::lookup p net)))))

; idle -> terminated
(defruled idle-to-terminated-props
  (implies
    (and
      (network-p net) (wtree-p net) (inv p net)
      (pid-p p) (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :idle)
      (not (erl-val-cons->lst
            (omap::lookup 'ChildPids
              (wtree-bind (omap::lookup p net))))))
    (and
      (not (equal
              (erl-val-kind
                (erl-state->in
                  (apply-k (proc->s (omap::lookup p net))
                            (proc->klst (omap::lookup p net)))))
              :receive))
      (equal
        (erl-state->self
          (proc->s
            (change-proc (omap::lookup p net)
              :s (apply-k
                  (proc->s (omap::lookup p net))
                  (proc->klst (omap::lookup p net)))
              :ps :terminated
              :klst nil)))
        p)
      (equal
        (omap::lookup 'Index
           (wtree-bind
             (change-proc (omap::lookup p net)
               :s (apply-k
                    (proc->s (omap::lookup p net))
                    (proc->klst (omap::lookup p net)))
               :ps :terminated
               :klst nil)))
        (omap::lookup 'Index (wtree-bind (omap::lookup p net))))
      (equal
        (omap::lookup 'Parent
           (wtree-bind
             (change-proc (omap::lookup p net)
               :s (apply-k
                    (proc->s (omap::lookup p net))
                    (proc->klst (omap::lookup p net)))
               :ps :terminated
               :klst nil)))
        (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
      (equal
        (omap::lookup 'ChildPids
           (wtree-bind
             (change-proc (omap::lookup p net)
               :s (apply-k
                    (proc->s (omap::lookup p net))
                    (proc->klst (omap::lookup p net)))
               :ps :terminated
               :klst nil)))
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))
      (iff
        (omap::assoc 'Index
          (wtree-bind 
            (change-proc (omap::lookup p net)
              :s (apply-k
                  (proc->s (omap::lookup p net))
                  (proc->klst (omap::lookup p net)))
              :ps :terminated
              :klst nil)))
        (omap::assoc 'Index (wtree-bind (omap::lookup p net))))
      (iff
        (omap::assoc 'Parent
          (wtree-bind 
            (change-proc (omap::lookup p net)
              :s (apply-k
                  (proc->s (omap::lookup p net))
                  (proc->klst (omap::lookup p net)))
              :ps :terminated
              :klst nil)))
        (omap::assoc 'Parent (wtree-bind (omap::lookup p net))))
      (iff
        (omap::assoc 'ChildPids
          (wtree-bind 
            (change-proc (omap::lookup p net)
              :s (apply-k
                  (proc->s (omap::lookup p net))
                  (proc->klst (omap::lookup p net)))
              :ps :terminated
              :klst nil)))
        (omap::assoc 'ChildPids (wtree-bind (omap::lookup p net))))
      (equal
        (leaf-p
          (change-proc (omap::lookup p net)
            :s (apply-k
                  (proc->s (omap::lookup p net))
                  (proc->klst (omap::lookup p net)))
            :ps :terminated
            :klst nil))
        (leaf-p (omap::lookup p net)))
      (equal
        (root-p
          (change-proc (omap::lookup p net)
            :s (apply-k
                  (proc->s (omap::lookup p net))
                  (proc->klst (omap::lookup p net)))
            :ps :terminated
            :klst nil))
        (root-p (omap::lookup p net)))
      (equal
        (proc->ps
          (change-proc (omap::lookup p net)
            :s (apply-k
                  (proc->s (omap::lookup p net))
                  (proc->klst (omap::lookup p net)))
            :ps :terminated
            :klst nil))
        :terminated)))
  :disable equal-of-kont-function-return
  :use
    ((:instance inv-idle-node-props)
     (:instance apply-k-of-idle-no-children
        (s (proc->s (omap::lookup p net)))
        (klst (proc->klst (omap::lookup p net)))
        (self p)
        (parent (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
        (index (erl-val-integer->val
                (omap::lookup 'Index (wtree-bind (omap::lookup p net))))))
     (:instance wtree-nodes-are-leaf-or-root (pid p))
     (:instance leaf-root-p-when-wtree-bindings-equal
       (p1 (change-proc (omap::lookup p net)
              :s (apply-k
                    (proc->s (omap::lookup p net))
                    (proc->klst (omap::lookup p net)))
              :ps :terminated
              :klst nil))
       (p2 (omap::lookup p net)))))