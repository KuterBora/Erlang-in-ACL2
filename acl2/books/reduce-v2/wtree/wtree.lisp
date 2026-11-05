; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "wtree-helpers")

(set-induction-depth-limit 1)

; Predicate for Lin & Snyder style reduce worker trees, specifically for the reduce
; defined in reduce-v2/reduce-proc.lisp

; The Predicate ----------------------------------------------------------------

; If a process is a node of a worker tree:
; - it is the root or a leaf,
; - its children, parent, and indices are consistent with the rest of net,
; - if it is the root, the index of its rightmost child is one less than the
;   size of the network. This ties the root's subtree to the whole network.
;   This could probably be replaced with a better property.
(define wtree-node-p ((pid pid-p) (net network-p))
  :returns (r booleanp)
  :guard-hints
    (("Goal" :use ((:instance node-p-of-rightmost-child (net net) (pid pid)))))
  (b* ((pid (pid-fix pid))
       (net (network-fix net))
       ((unless (omap::assoc pid net)) nil)
       (proc (omap::lookup pid net))
       ((unless (or (root-p proc) (leaf-p proc))) nil)
       (bind (wtree-bind proc))
       (index (erl-val-integer->val (omap::lookup 'Index bind)))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids bind)))
       (parent (omap::lookup 'Parent bind)))
    (and (check-children pid children net)
         (check-parent pid parent net)
         (check-indices index children net)
         (or (leaf-p proc)
             (b* ((rpid (rightmost-child pid net)))
               (and rpid
                    (equal (erl-val-integer->val
                             (omap::lookup 'Index
                               (wtree-bind (omap::lookup rpid net))))
                           (- (omap::size net) 1)))))))
  ///
    (defcong pid-equiv equal (wtree-node-p pid net) 1)
    (defcong network-equiv equal (wtree-node-p pid net) 2))

; Every node of net is well formed in net0 (the original network).
(define wtree0-p ((net network-p) (net0 network-p))
  :returns (r booleanp)
  :measure (acl2-count (network-fix net))
  (b* ((net (network-fix net))
       (net0 (network-fix net0))
       ((if (omap::emptyp net)) t))
    (and (wtree-node-p (omap::head-key net) net0)
         (wtree0-p (omap::tail net) net0)))
  ///
    (defcong network-equiv equal (wtree0-p net net0) 1)
    (defcong network-equiv equal (wtree0-p net net0) 2)

    (defrule wtree-node-p-when-wtree0-p
      (implies (and (wtree0-p net net0) (network-p net) (omap::assoc pid net))
               (wtree-node-p pid net0)))

    (defrule wtree0-p-when-subset-of-keys
      (implies
        (and (network-p net1) (network-p net) (wtree0-p net1 net0)
             (set::subset (omap::keys net) (omap::keys net1)))
        (wtree0-p net net0))
      :induct (wtree0-p net net0)))

; Every node of net is well formed in net.
(define wtree-p ((net network-p))
  :returns (r booleanp)
  (wtree0-p net net)
  ///
    (defcong network-equiv equal (wtree-p net) 1)

    (defrule wtree-node-p-when-wtree-p
      (implies (and (wtree-p net) (network-p net) (omap::assoc pid net))
               (wtree-node-p pid net))))

; Properties of the Nodes of a Wtree -------------------------------------------

(defrule wtree-nodes-are-leaf-or-root
  (implies
    (and (wtree-p net) (network-p net) (omap::assoc pid net))
    (or (leaf-p (omap::lookup pid net))
        (root-p (omap::lookup pid net))))
  :use wtree-node-p-when-wtree-p
  :enable wtree-node-p)

(defrule check-children-of-wtree-node
  (implies
    (and (network-p net) (wtree-p net) (omap::assoc pid net))
    (check-children pid
      (erl-val-cons->lst
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net))))
      net))
  :use wtree-node-p-when-wtree-p
  :enable wtree-node-p)

(defrule check-parent-of-wtree-p
  (implies
    (and (network-p net) (wtree-p net) (omap::assoc pid net))
    (check-parent pid
      (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
      net))
  :use wtree-node-p-when-wtree-p
  :enable wtree-node-p)

(defrule check-indices-of-wtree-node
  (implies
    (and (network-p net) (wtree-p net) (omap::assoc pid net))
    (check-indices
      (erl-val-integer->val
        (omap::lookup 'Index (wtree-bind (omap::lookup pid net))))
      (erl-val-cons->lst
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net))))
      net))
  :use wtree-node-p-when-wtree-p
  :enable wtree-node-p)

(defrule rightmost-child-of-wtree-root
  (implies
    (and (network-p net) (wtree-p net) (omap::assoc pid net)
         (root-p (omap::lookup pid net)))
    (rightmost-child pid net))
  :use wtree-node-p-when-wtree-p
  :enable wtree-node-p)

; The root's subtree spans the indices 0 .. size-1 of the network.
; (defruled rightmost-index-of-wtree-root
;   (implies
;     (and (network-p net) (wtree-p net) (omap::assoc pid net)
;          (root-p (omap::lookup pid net)))
;     (equal
;       (erl-val-integer->val
;         (omap::lookup 'Index
;           (wtree-bind (omap::lookup (rightmost-child pid net) net))))
;       (+ -1 (omap::size net))))
;   :use wtree-node-p-when-wtree-p
;   :enable wtree-node-p)

(defrule parent-not-self-of-wtree
  (implies
    (and (network-p net) (wtree-p net) (omap::assoc pid net))
    (not (equal (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
                pid)))
  :enable check-parent
  :disable check-parent-of-wtree-p
  :use check-parent-of-wtree-p)

; (defruled node-is-childpid-of-parent
;   (implies
;     (and
;       (network-p net) (wtree-p net)
;       (pid-p pid) (pid-p p) (omap::assoc pid net)
;       (equal (omap::lookup 'Parent
;                (wtree-bind (omap::lookup pid net))) p))
;     (and
;       (omap::assoc p net)
;       (member-equal
;         pid
;         (erl-val-cons->lst
;           (omap::lookup
;             'ChildPids
;             (wtree-bind (omap::lookup p net)))))))
;   :enable check-parent
;   :use ((:instance check-parent-of-wtree-p (pid pid))))


; Rightmost Child of a Wtree Node ----------------------------------------------

; (defruled rightmost-child-of-parent-is-rightmost-of-last-child
;   (implies
;     (and
;       (network-p net) (omap::assoc pid net)
;       (or (leaf-p (omap::lookup pid net)) (root-p (omap::lookup pid net)))
;       (erl-val-cons->lst
;         (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net))))
;       (pid-p
;         (car (last (erl-val-cons->lst
;                      (omap::lookup 'ChildPids
;                        (wtree-bind (omap::lookup pid net)))))))
;       (omap::assoc
;         (car (last (erl-val-cons->lst
;                      (omap::lookup 'ChildPids
;                        (wtree-bind (omap::lookup pid net)))))) net)
;       (leaf-p (omap::lookup
;                 (car (last (erl-val-cons->lst
;                              (omap::lookup 'ChildPids
;                                (wtree-bind (omap::lookup pid net)))))) net))
;       (rightmost-child pid net))
;     (equal
;       (rightmost-child
;         (car (last (erl-val-cons->lst
;                       (omap::lookup 'ChildPids
;                         (wtree-bind (omap::lookup pid net)))))) net)
;       (rightmost-child pid net)))
;   :enable rightmost-child
;   :expand ((rightmost-child0 pid net (omap::size net)))
;   :use ((:instance increase-fuel-of-rightmost-child0
;           (pid (car (last (erl-val-cons->lst
;                             (omap::lookup 'ChildPids
;                               (wtree-bind (omap::lookup pid net)))))))
;           (f1 (- (omap::size net) 1)) (f2 (omap::size net)))))

; (defruled rightmost-child-when-check-indices
;   (implies
;     (and
;       (network-p net) (pid-lst-p cps)
;       (member-equal cpid cps)
;       (erl-val-cons->lst
;         (omap::lookup 'ChildPids (wtree-bind (omap::lookup cpid net))))
;       (check-indices i cps net))
;     (rightmost-child cpid net))
;   :enable check-indices
;   :induct (check-indices i cps net))

; (defruled first-child-of-check-indices
;   (implies
;     (and
;       (network-p net) (pid-p pid) (natp index)
;       (pid-lst-p children) children
;       (check-children pid children net)
;       (check-indices index children net))
;     (and
;       (omap::assoc (car children) net)
;       (leaf-p (omap::lookup (car children) net))
;       (equal
;         (omap::lookup 'Parent (wtree-bind (omap::lookup (car children) net)))
;         pid)
;       (equal
;         (erl-val-integer->val
;           (omap::lookup 'Index (wtree-bind (omap::lookup (car children) net))))
;         (+ 1 index))))
;   :enable (check-children check-indices))

; (defruled rightmost-child-of-wtree-node
;   (implies
;     (and
;       (network-p net) (wtree-p net)
;       (omap::assoc pid net)
;       (erl-val-cons->lst
;         (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net)))))
;     (rightmost-child pid net))
;   :enable check-parent
;   :disable
;     (wtree-nodes-are-leaf-or-root check-parent-of-wtree-p
;      check-indices-of-wtree-node)
;   :use ((:instance wtree-nodes-are-leaf-or-root)
;         (:instance check-parent-of-wtree-p)
;         (:instance check-indices-of-wtree-node
;           (pid (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))))
;         (:instance rightmost-child-when-member-of-check-indices
;           (cpid pid)
;           (cps (erl-val-cons->lst
;                  (omap::lookup 'ChildPids
;                    (wtree-bind
;                      (omap::lookup
;                        (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
;                        net)))))
;           (i (erl-val-integer->val
;                (omap::lookup 'Index
;                  (wtree-bind
;                    (omap::lookup
;                      (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
;                      net))))))))


; Updating a Wtree -------------------------------------------------------------

(defrule wtree-node-p-of-update-equal-fields
  (implies
    (and (network-p net) (network-p (omap::update pid proc net))
         (omap::assoc pid net) (pid-p p)
         (equal (wtree-fields proc) (wtree-fields (omap::lookup pid net))))
    (equal (wtree-node-p p (omap::update pid proc net))
           (wtree-node-p p net)))
  :enable wtree-node-p)

(defrule wtree0-p-of-update-equal-fields
  (implies
    (and (network-p net0) (network-p (omap::update pid proc net0))
         (network-p net) (omap::assoc pid net0)
         (equal (wtree-fields proc) (wtree-fields (omap::lookup pid net0))))
    (equal (wtree0-p net (omap::update pid proc net0))
           (wtree0-p net net0)))
  :enable wtree0-p)

(defrule wtree-p-of-update-equal-fields
  (implies
    (and (network-p net) (network-p (omap::update pid proc net))
         (omap::assoc pid net)
         (equal (wtree-fields proc) (wtree-fields (omap::lookup pid net))))
    (equal (wtree-p (omap::update pid proc net))
           (wtree-p net)))
  :enable (wtree-p omap::in-of-keys-to-assoc)
  :use ((:instance wtree0-p-when-subset-of-keys
          (net1 net) (net (omap::update pid proc net))
          (net0 (omap::update pid proc net)))
        (:instance wtree0-p-when-subset-of-keys
          (net1 (omap::update pid proc net)) (net net) (net0 net))))
