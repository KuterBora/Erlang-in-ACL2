(in-package "ACL2")
(include-book "wtree-helpers")

(set-induction-depth-limit 1)

; A worker tree for the parallel reduce algorithm.


; Wtree Predicate --------------------------------------------------------------

; Helper to traverse the network.
(define wtree0-p ((net network-p) (net0 network-p) (n natp))
  :returns (r booleanp)
  :measure (acl2-count (network-fix net))
  :guard-hints
    (("Goal"
      :in-theory (disable node-p-of-rightmost-child index-of-leaf)
      :use
        ((:instance index-of-leaf (p (mv-nth 1 (omap::head net))))
         (:instance node-p-of-rightmost-child
           (net net0) (pid (mv-nth 0 (omap::head net))))
         (:instance node-p-of-rightmost-child
           (net net0) (pid (mv-nth 0 (omap::head net)))))))
  :ignore-ok t
  (b* ((net (network-fix net))
       (net0 (network-fix net0))
       (n (nfix n))
       ((if (zp n)) (omap::emptyp net0))
       ((unless (equal n (omap::size net0))) nil)
       ((if (omap::emptyp net)) t)
       (pid (omap::head-key net))
       (proc (omap::head-val net))
       ((unless (or (root-p proc) (leaf-p proc))) nil)
       (bind (wtree-bind proc))
       (index (erl-val-integer->val (omap::lookup 'Index bind)))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids bind)))
       (parent (omap::lookup 'Parent bind))
       ((unless (check-children pid children net0)) nil)
       ((unless (check-parent pid parent net0)) nil)
       ((unless (check-indices index children net0)) nil))
    (cond
      ((root-p proc)
       (b* (((unless (wtree0-p (omap::tail net) net0 n)) nil)
            (rpid (rightmost-child pid net0))
            ((unless rpid) nil)
            (rproc (omap::lookup rpid net0))
            (rbind (wtree-bind rproc))
            (rindex (erl-val-integer->val (omap::lookup 'Index rbind))))
          (equal rindex (- n 1))))   
      ((leaf-p proc) (wtree0-p (omap::tail net) net0 n))
      (t nil)))
  ///
    (defcong network-equiv equal (wtree0-p net net0 n) 1)
    (defcong network-equiv equal (wtree0-p net net0 n) 2)
    (defcong nat-equiv equal (wtree0-p net net0 n) 3)
    
    ; TODO: For my current implementation of wtree-p, I often have
    ; to state n > 0 in proofs. However, I would like to change that.
    (defrule wtree0-nodes-are-leaf-or-root
      (implies
        (and (wtree0-p net net0 n) (natp n) (> n 0)
            (network-p net) (network-p net0)
            (omap::assoc pid net)
            (not (leaf-p (omap::lookup pid net))))
        (root-p (omap::lookup pid net)))
      :use ((:instance omap::assoc-of-tail-when-not-head
              (key pid) (map net))
            (:instance omap::assoc-of-tail-when-assoc-of-tail
              (key pid) (map net))))

    (defrule wtree0-nodes-are-leaf-or-root-rev
      (implies
        (and (wtree0-p net net0 n) (natp n) (> n 0)
             (network-p net) (network-p net0)
             (omap::assoc pid net)
             (not (root-p (omap::lookup pid net))))
        (leaf-p (omap::lookup pid net)))
      :use ((:instance omap::assoc-of-tail-when-not-head
              (key pid) (map net))
            (:instance omap::assoc-of-tail-when-assoc-of-tail
              (key pid) (map net))))
    
    (defrule root-or-leaf-of-wtree-head
      (implies
        (and
          (network-p net) (network-p net0)
          (wtree0-p net net0 size)
          (not (omap::emptyp net0))
          (not (omap::emptyp net))
          (natp size)
          (not (root-p (mv-nth 1 (omap::head net)))))
        (leaf-p (mv-nth 1 (omap::head net))))
      :expand (wtree0-p net net0 size))
    
    (defrule wtree0-p-of-bad-tail
      (implies
        (and
          (network-p net) (network-p net0)
          (not (omap::emptyp net))
          (not (wtree0-p (omap::tail net) net0 size)))
        (not (wtree0-p net net0 size))))
    
    (defrule wtree0-of-zero
      (implies
        (and (network-p net0) (wtree0-p net net0 0))
        (omap::emptyp net0)))

    (defrule wtree0-of-size
      (implies
        (and (network-p net0) (natp size)
             (wtree0-p net net0 size))
        (equal (omap::size net0) size))))

; Check if network is a wtree of size n.
(define wtree-p ((net network-p))
  :returns (r booleanp)
  (b* ((net (network-fix net)))
      (wtree0-p net net (omap::size net)))
  ///
    (defcong network-equiv equal (wtree-p net) 1)
    
    (defrule wtree-nodes-are-leaf-or-root
      (implies
        (and (wtree-p net) (network-p net)
            (pid-p pid) (omap::assoc pid net))
        (or (leaf-p (omap::lookup pid net))
            (root-p (omap::lookup pid net))))
      :enable wtree-p
      :cases ((< 0 (omap::size net)))))


; Utility ----------------------------------------------------------------------

; Induction on wtree
(define wtree0-induct (p net net0 size)
  :enabled t
  :irrelevant-formals-ok t
  :ignore-ok t
  :verify-guards nil
  :measure (acl2-count (network-fix net))
   (b* ((net (network-fix net))
        ((unless (omap::assoc p net)) net)
        ((if (omap::emptyp net)) net)
        (pid (omap::head-key net))
        ((if (equal p pid)) net))
       (wtree0-induct p (omap::tail net) net0 size)))


; More Theorems ----------------------------------------------------------------

(defrule rightmost-child-of-wtree0-p
  (implies
    (and
      (wtree0-p net net0 size)
      (network-p net) (network-p net0)
      (not (omap::emptyp net)) (not (omap::emptyp net0))
      (omap::assoc pid net)
      (root-p (omap::lookup pid net)))
    (rightmost-child pid net0))
  :enable wtree0-p
  :induct (wtree0-induct pid net net0 size)
  :hints
    (("Subgoal *1/3"
      :use ((:instance omap::assoc-of-tail-when-not-head
              (key pid) (map net))))
     ("Subgoal *1/2" :expand (wtree0-p net net0 size))))

(defrule check-children-of-wtree0-p
  (implies
    (and
      (wtree0-p net net0 size)
      (network-p net) (network-p net0)
      (not (omap::emptyp net)) (not (omap::emptyp net0))
      (omap::assoc pid net))
    (check-children
      pid
      (erl-val-cons->lst
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net))))
      net0))
  :enable wtree0-p
  :induct (wtree0-induct pid net net0 size)
  :hints
    (("Subgoal *1/3"
      :use ((:instance omap::assoc-of-tail-when-not-head
             (key pid) (map net))))
     ("Subgoal *1/2" :expand (wtree0-p net net0 size))))

(defrule check-children-of-wtree-node
  (implies
    (and (network-p net) (wtree-p net) (omap::assoc pid net))
    (check-children pid
      (erl-val-cons->lst
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net))))
      net))
  :enable wtree-p
  :cases ((omap::emptyp net)))

(defrule check-parent-of-wtree0-p
  (implies
    (and
      (wtree0-p net net0 size)
      (network-p net) (network-p net0)
      (not (omap::emptyp net)) (not (omap::emptyp net0))
      (omap::assoc pid net))
    (check-parent
      pid
      (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
      net0))
  :enable wtree0-p
  :induct (wtree0-induct pid net net0 size)
  :hints
    (("Subgoal *1/3"
      :use ((:instance omap::assoc-of-tail-when-not-head
              (key pid) (map net))))
     ("Subgoal *1/2" :expand (wtree0-p net net0 size))))

(defrule check-parent-of-wtree-p
  (implies
    (and
      (network-p net) (wtree-p net) (omap::assoc pid net))
    (check-parent pid
      (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
      net))
  :enable wtree-p
  :cases ((omap::emptyp net)))

(defrule parent-not-self-of-wtree
  (implies
    (and (network-p net) (wtree-p net) (omap::assoc pid net))
    (not (equal (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
                pid)))
  :enable check-parent
  :disable check-parent-of-wtree-p
  :use check-parent-of-wtree-p)

(defrule root-of-wtree0-p
  (implies
    (and
      (wtree0-p net net0 size) (network-p net) (network-p net0)
      (not (omap::emptyp net)) (not (omap::emptyp net0))
      (omap::assoc pid net)
      (root-p (omap::lookup pid net)))
    (equal
      (erl-val-integer->val
        (omap::lookup 'Index (wtree-bind (omap::lookup (rightmost-child pid net0) net0))))
      (+ -1 size)))
  :enable wtree0-p
  :induct (wtree0-induct pid net net0 size)
  :hints
    (("Subgoal *1/3"
      :use ((:instance omap::assoc-of-tail-when-not-head
             (key pid) (map net))))
     ("Subgoal *1/2" :expand (wtree0-p net net0 size))))

(defrule check-indices-of-wtree0-p
  (implies
    (and
      (wtree0-p net net0 size)
      (network-p net) (network-p net0)
      (not (omap::emptyp net)) (not (omap::emptyp net0))
      (omap::assoc pid net))
    (check-indices
      (erl-val-integer->val
        (omap::lookup 'Index (wtree-bind (omap::lookup pid net))))
      (erl-val-cons->lst
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net))))
      net0))
  :enable wtree0-p
  :induct (wtree0-induct pid net net0 size)
  :hints
    (("Subgoal *1/3"
        :use ((:instance omap::assoc-of-tail-when-not-head
                (key pid) (map net))))
     ("Subgoal *1/2" :expand (wtree0-p net net0 size))))

(defrule check-indices-of-wtree-node
  (implies
    (and (network-p net) (wtree-p net) (omap::assoc pid net))
    (check-indices
      (erl-val-integer->val
        (omap::lookup 'Index (wtree-bind (omap::lookup pid net))))
      (erl-val-cons->lst
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net))))
      net))
  :enable wtree-p
  :cases ((omap::emptyp net)))

(defrule wtree0-of-tail-of-wtree0-p
  (implies
    (and (wtree0-p net net0 size)
         (network-p net) (network-p net0)
         (not (omap::emptyp net))
         (not (omap::emptyp net0))
         (omap::assoc pid net))
    (wtree0-p (omap::tail net) net0 size))
  :enable wtree0-p
  :induct (wtree0-induct pid net net0 size)
  :hints
    (("Subgoal *1/3"
        :use ((:instance omap::assoc-of-tail-when-not-head
                (key pid) (map net))))
     ("Subgoal *1/2" :expand (wtree0-p net net0 size))))