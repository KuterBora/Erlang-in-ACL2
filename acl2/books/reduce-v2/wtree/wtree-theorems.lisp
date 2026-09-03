(in-package "ACL2")
(include-book "wtree")

; Even more theorems about wtree-p, and its helpers

; Updating a Wtree -------------------------------------------------------------

; TODO: This probably exists in a community book.
(defrule size-crock
  (implies (< 0 (omap::size m)) (not (omap::emptyp m)))
  :enable omap::size)

(defrule wtree0-p-of-update
  (implies
    (and
      (network-p net) (network-p net0)
      (wtree0-p net net0 size) (natp size)
      (omap::assoc pid net)
      (pid-p pid) (proc-p proc)
      (network-p (omap::update pid proc net))
      (equal (proc->pid proc) pid)
      (or (leaf-p proc) (root-p proc))
      (equal
        (omap::lookup 'Index (wtree-bind proc))
        (omap::lookup 'Index (wtree-bind (omap::lookup pid net))))
      (equal
        (omap::lookup 'Parent (wtree-bind proc))
        (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))))
      (equal
        (omap::lookup 'ChildPids (wtree-bind proc))
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net)))))
    (wtree0-p (omap::update pid proc net) net0 size))
  :enable (network-fix)
  :disable
    (wtree0-of-tail-of-wtree0-p
    check-children-of-wtree0-p)
  :induct (wtree0-induct pid net net0 size)
  :hints
    (("Subgoal *1/3"
      :use ((:instance wtree0-of-tail-of-wtree0-p)
            (:instance check-children-of-wtree0-p (pid (mv-nth 0 (omap::head net))))
            (:instance check-parent-of-wtree0-p (pid (mv-nth 0 (omap::head net))))
            (:instance check-indices-of-wtree0-p (pid (mv-nth 0 (omap::head net))))
            (:instance check-children-of-wtree0-p (net (omap::tail net)))
            (:instance check-parent-of-wtree0-p (net (omap::tail net)))
            (:instance check-indices-of-wtree0-p (net (omap::tail net)))
            (:instance omap::assoc-of-tail-when-not-head (key pid) (map net)))
      :expand
        ((wtree0-p (omap::update (proc->pid proc) proc net) net0 size)))
     ("Subgoal *1/2"
      :expand
        ((wtree0-p net net0 size)
         (wtree0-p (omap::update (proc->pid proc) proc net) net0 0)
         (wtree0-p (omap::update (proc->pid proc) proc net) net0 size)))))

(defrule wtree0-p-of-update-net0
  (implies
    (and
      (network-p net) (network-p net0)
      (network-p (omap::update pid proc net0))
      (pid-p pid) (proc-p proc) (omap::assoc pid net0)
      (or (leaf-p proc) (root-p proc))
      (or (leaf-p (omap::lookup pid net0)) (root-p (omap::lookup pid net0)))
      (equal (omap::lookup 'Index (wtree-bind proc))
             (omap::lookup 'Index (wtree-bind (omap::lookup pid net0))))
      (equal (omap::lookup 'Parent (wtree-bind proc))
             (omap::lookup 'Parent (wtree-bind (omap::lookup pid net0))))
      (equal (omap::lookup 'ChildPids (wtree-bind proc))
             (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net0))))
      (wtree0-p net net0 size))
    (wtree0-p net (omap::update pid proc net0) size))
  :enable (wtree0-p omap::lookup-of-update)
  :induct (wtree0-p net net0 size)
  :expand (wtree0-p net (omap::update pid proc net0) size))

(defrule wtree-p-of-update
  (implies
    (and
      (network-p net) (wtree-p net)
      (omap::assoc pid net) (proc-p proc) (pid-p pid)
      (network-p (omap::update pid proc net))
      (equal (proc->pid proc) pid)
      (or (leaf-p proc) (root-p proc))
      (equal (omap::lookup 'Index (wtree-bind proc))
             (omap::lookup 'Index (wtree-bind (omap::lookup pid net))))
      (equal (omap::lookup 'Parent (wtree-bind proc))
             (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))))
      (equal (omap::lookup 'ChildPids (wtree-bind proc))
             (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net)))))
    (wtree-p (omap::update pid proc net)))
  :enable wtree-p
  :do-not-induct t
  :disable (wtree0-p-of-update wtree0-p-of-update-net0)
  :use ((:instance wtree-nodes-are-leaf-or-root)
        (:instance wtree0-p-of-update (net0 net) (size (omap::size net)))
        (:instance wtree0-p-of-update-net0
          (net (omap::update pid proc net)) (net0 net)
          (size (omap::size net)))))
