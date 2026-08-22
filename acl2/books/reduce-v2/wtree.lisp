(in-package "ACL2")
(include-book "spawn")

(set-induction-depth-limit 1)

(local (include-book "std/lists/len" :dir :system))
(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "std/lists/nth" :dir :system))



; Wtree properties

(define root-p ((p proc-p))
  :returns (r booleanp)
  (b* ((p (proc-fix p))
       (bind (erl-state->bind (proc->s p)))
       ((unless (omap::assoc 'Parent bind)) nil)
       ((unless (omap::assoc 'ChildPids bind)) nil)
       ((unless (omap::assoc 'Index bind)) nil)
       (index (omap::lookup 'Index bind))
       (parent (omap::lookup 'Parent bind))
       (children (omap::lookup 'ChildPids bind)))
      (and (equal index '(:integer 0))
           (equal parent '(:atom none))
           (equal (erl-val-kind children) :cons)))
  ///
    (defcong proc-equiv equal (root-p p) 1)
    (defrule assoc-of-root-p
      (implies
        (root-p p)
        (and (omap::assoc 'Index (erl-state->bind (proc->s p)))
             (omap::assoc 'Parent (erl-state->bind (proc->s p)))
             (omap::assoc 'ChildPids (erl-state->bind (proc->s p)))
             (equal (erl-val-kind
                      (omap::lookup 'ChildPids (erl-state->bind (proc->s p))))
                    :cons))))
    (defrule index-of-root-p
      (implies
        (root-p p)
        (and
          (natp (erl-val-integer->val
                  (omap::lookup 'Index (erl-state->bind (proc->s p)))))
          (equal (omap::lookup 'Index (erl-state->bind (proc->s p))) '(:integer 0)))))
    (defrule parent-of-root-p
      (implies
        (root-p p)
        (equal (omap::lookup 'Parent (erl-state->bind (proc->s p))) '(:atom none)))))

(define leaf-p ((p proc-p))
  :returns (r booleanp)
  (b* ((p (proc-fix p))
       (bind (erl-state->bind (proc->s p)))
       ((unless (omap::assoc 'Parent bind)) nil)
       ((unless (omap::assoc 'ChildPids bind)) nil)
       ((unless (omap::assoc 'Index bind)) nil)
       (index (omap::lookup 'Index bind))
       (parent (omap::lookup 'Parent bind))
       (children (omap::lookup 'ChildPids bind)))
      (and (equal (erl-val-kind index) :integer)
           (natp (erl-val-integer->val index))
           (not (equal (erl-val-integer->val index) 0))
           (pid-p parent)
           (equal (erl-val-kind children) :cons)))
  ///
    (defcong proc-equiv equal (leaf-p p) 1)
    (defrule assoc-of-leaf-p
      (implies
        (leaf-p p)
        (and (omap::assoc 'Index (erl-state->bind (proc->s p)))
             (omap::assoc 'Parent (erl-state->bind (proc->s p)))
             (omap::assoc 'ChildPids (erl-state->bind (proc->s p)))
             (equal (erl-val-kind
                      (omap::lookup 'Index (erl-state->bind (proc->s p))))
                    :integer)
             (equal (erl-val-kind
                      (omap::lookup 'ChildPids (erl-state->bind (proc->s p))))
                    :cons))))
    (defrule index-of-leaf-p
      (implies
        (leaf-p p)
        (and
          (natp (erl-val-integer->val
                  (omap::lookup 'Index (erl-state->bind (proc->s p)))))
          (not (equal
                  (erl-val-integer->val
                    (omap::lookup 'Index (erl-state->bind (proc->s p))))
                  0)))))
    (defrule parent-of-leaf-p
      (implies
        (leaf-p p)
        (pid-p (omap::lookup 'Parent (erl-state->bind (proc->s p)))))))

(define non-root-segment-p ((net network-p))
  :returns (r booleanp)
  :measure (acl2-count (network-fix net))
  (b* ((net (network-fix net))
       ((if (omap::emptyp net)) t))
      (and (leaf-p (omap::head-val net))
           (non-root-segment-p (omap::tail net))))
  ///
    (defcong network-equiv equal (non-root-segment-p net) 1)
    (defrule assoc-of-non-root-segment
      (implies
        (and (network-p net) (pid-p pid)
            (non-root-segment-p net)
            (omap::assoc pid net))
        (leaf-p (omap::lookup pid net)))
      :enable (omap::lookup)))

(define check-children ((pid pid-p) (children erl-vlst-p) (net network-p))
  :returns (r booleanp)
  :measure (len (erl-vlst-fix children))
  (b* ((pid (pid-fix pid))
       (children (erl-vlst-fix children))
       (net (network-fix net))
       ((if (null children)) t)
       (cpid (car children))
       ((unless (omap::assoc cpid net)) nil)
       (cproc (omap::lookup cpid net))
       ((unless (leaf-p cproc)) nil)
       (bind (erl-state->bind (proc->s cproc)))
       ((unless (equal (omap::lookup 'Parent bind) pid)) nil))
      (check-children pid (cdr children) net))
  ///
    (defcong pid-equiv equal (check-children pid children net) 1)
    (defcong erl-vlst-equiv equal (check-children pid children net) 2)
    (defcong network-equiv equal (check-children pid children net) 3))

; check if parent is indeed a parent of pid
(define check-parent ((pid pid-p) (parent erl-val-p) (net network-p))
  :returns (r booleanp)
  (b* ((pid (pid-fix pid))
       (parent (erl-val-fix parent))
       (net (network-fix net))
       ((unless (omap::assoc pid net)) nil)
       ((unless (pid-p parent)) (root-p (omap::lookup pid net)))
       ((unless (omap::assoc parent net)) nil)
       (pproc (omap::lookup parent net))
       ((unless (or (leaf-p pproc) (root-p pproc))) nil)
       (bind (erl-state->bind (proc->s pproc)))
       (cpids (erl-val-cons->lst (omap::lookup 'ChildPids bind))))
      (not (null (member-equal pid cpids))))
  ///
    (defcong pid-equiv equal (check-parent pid parent net) 1)
    (defcong erl-val-equiv equal (check-parent pid parent net) 2)
    (defcong network-equiv equal (check-parent pid parent net) 3))

; return the leftmost descendent of the given pid, else nil.
; Also, make sure there is no cycle by removing visted nodes from the net.
; (define leftmost-child ((pid pid-p) (net network-p))
;   :returns lpid
;   :measure (omap::size (network-fix net))
;   :guard-hints (("Goal" :in-theory (enable erl-val-crock)))
;   :prepwork ((local (defruled erl-val-crock (implies (erl-val-p v) (consp v)))))

;   (b* ((pid (pid-fix pid))
;        (net (network-fix net))
;        ((unless (omap::assoc pid net)) nil)
;        (proc (omap::lookup pid net))
;        ((unless (or (leaf-p proc) (root-p proc))) nil)
;        (bind (erl-state->bind (proc->s proc)))
;        (children (erl-val-cons->lst (omap::lookup 'ChildPids bind)))
;        ((if (null children)) pid)
;        (cpid (car children))
;        ((unless (pid-p cpid)) nil)
;        ((unless (omap::assoc cpid net)) nil)
;        ((unless (leaf-p (omap::lookup cpid net))) nil))
;       (leftmost-child cpid (omap::delete pid net)))
;   ///
;     (defcong pid-equiv equal (leftmost-child pid net) 1)
;     (defcong network-equiv equal (leftmost-child pid net) 2)
    
;     (more-returns
;       (lpid :name erl-pid-or-nil-of-leftmost-child
;         (or (null lpid) (pid-p lpid)))
;       (lpid :name assoc-of-leftmost-child
;         (implies (and lpid (network-p net)) (omap::assoc lpid net)))
;       (lpid :name node-p-of-leftmost-child
;         (implies
;           (and lpid (network-p net))
;           (or (leaf-p (omap::lookup lpid net))
;               (root-p (omap::lookup lpid net)))))
;       ; TODO: prove this by showing omap::delete will not be assoc
;       ; (lpid :name no-children-of-leftmost-child
;       ;   (implies
;       ;     (and (pid-p lpid) (pid-p pid) (network-p net))
;       ;     (null (erl-val-cons->lst
;       ;             (omap::lookup
;       ;               'ChildPids
;       ;               (erl-state->bind (proc->s (omap::lookup lpid net))))))))
;       ))


(define rightmost-child-aux ((pid pid-p) (net network-p) (fuel natp))
  :returns rpid
  :measure (nfix fuel)
  :guard-hints (("Goal" :in-theory (enable erl-val-crock)))
  :prepwork
    ((local (include-book "std/lists/last" :dir :system))
     (local (defruled erl-val-crock (implies (erl-val-p v) (consp v)))))

  (b* ((pid (pid-fix pid))
       (net (network-fix net))
       (fuel (nfix fuel))
       ((if (zp fuel)) nil)
       ((unless (omap::assoc pid net)) nil)
       (proc (omap::lookup pid net))
       ((unless (or (leaf-p proc) (root-p proc))) nil)
       (bind (erl-state->bind (proc->s proc)))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids bind)))
       ((if (null children)) pid)
       (cpid (car (last children)))
       ((unless (pid-p cpid)) nil)
       ((unless (omap::assoc cpid net)) nil)
       ((unless (leaf-p (omap::lookup cpid net))) nil))
      (rightmost-child-aux cpid net (- fuel 1)))
  ///
    (defcong pid-equiv equal (rightmost-child-aux pid net fuel) 1)
    (defcong network-equiv equal (rightmost-child-aux pid net fuel) 2)
    (defcong nat-equiv equal (rightmost-child-aux pid net fuel) 3)

    (more-returns
      (rpid :name erl-pid-or-nil-of-rightmost-child-aux
        (or (null rpid) (pid-p rpid)))
      (rpid :name assoc-of-rightmost-child-aux
        (implies (and rpid (network-p net)) (omap::assoc rpid net)))
      (rpid :name node-p-of-rightmost-child-aux
        (implies
          (and rpid (network-p net))
          (or (leaf-p (omap::lookup rpid net))
              (root-p (omap::lookup rpid net)))))))

(define rightmost-child ((pid pid-p) (net network-p))
  :returns rpid
  (rightmost-child-aux pid net (omap::size (network-fix net)))
  ///
    (defcong pid-equiv equal (rightmost-child pid net) 1)
    (defcong network-equiv equal (rightmost-child pid net) 2)

    (more-returns
      (rpid :name erl-pid-or-nil-of-rightmost-child
        (or (null rpid) (pid-p rpid))
        :hints (("Goal"
                  :use ((:instance erl-pid-or-nil-of-rightmost-child-aux
                          (fuel (omap::size (network-fix net))))))))
      (rpid :name assoc-of-rightmost-child
        (implies (and rpid (network-p net)) (omap::assoc rpid net))
        :hints (("Goal"
                  :use ((:instance assoc-of-rightmost-child-aux
                          (fuel (omap::size (network-fix net))))))))
      (rpid :name node-p-of-rightmost-child
        (implies
          (and rpid (network-p net))
          (or (leaf-p (omap::lookup rpid net))
              (root-p (omap::lookup rpid net))))
        :hints (("Goal"
                  :use ((:instance node-p-of-rightmost-child-aux
                          (fuel (omap::size (network-fix net))))))))))


(define check-indices ((index natp) (children erl-vlst-p) (net network-p))
  :returns (r booleanp)
  :measure (len (erl-vlst-fix children))
  :guard-hints
    (("Goal" :use ((:instance node-p-of-rightmost-child (net net) (pid (car children))))))
  (b* ((index (nfix index))
       (children (erl-vlst-fix children))
       (net (network-fix net))
       ((if (null children)) t)
       (cpid (car children))
       ((unless (pid-p cpid)) nil)
       ((unless (omap::assoc cpid net)) nil)
       (cproc (omap::lookup cpid net))
       ((unless (leaf-p cproc)) nil)
       (cbind (erl-state->bind (proc->s cproc)))
       (cchildren (erl-val-cons->lst (omap::lookup 'ChildPids cbind)))
       (cindex (erl-val-integer->val (omap::lookup 'Index cbind)))
       ((unless (equal (+ 1 index) cindex)) nil)
       ((if (null cchildren)) (check-indices cindex (cdr children) net))
       (rpid (rightmost-child cpid net))
       ((unless rpid) nil)
        (rproc (omap::lookup rpid net))
        (rbind (erl-state->bind (proc->s rproc)))
        (rindex (erl-val-integer->val (omap::lookup 'Index rbind))))
      (check-indices rindex (cdr children) net)))

; check if network is a wtree of size n.
(define wtree0-p ((net network-p) (net0 network-p) (n natp))
  :returns (r booleanp)
  :measure (acl2-count (network-fix net))
  :guard-hints
    (("Goal"
      :in-theory (disable node-p-of-rightmost-child index-of-leaf-p)
      :use
        ((:instance index-of-leaf-p (p (mv-nth 1 (omap::head net))))
         (:instance node-p-of-rightmost-child (net net0) (pid (mv-nth 0 (omap::head net))))
         (:instance node-p-of-rightmost-child (net net0) (pid (mv-nth 0 (omap::head net)))))))
  :ignore-ok t
  (b* ((net (network-fix net))
       (net0 (network-fix net0))
       (n (nfix n))

       ; do I need these?
       ((if (zp n)) (omap::emptyp net0))
       ((unless (equal n (omap::size net0))) nil)

       ((if (omap::emptyp net)) t)

       (pid (omap::head-key net))
       (proc (omap::head-val net))
       ((unless (or (root-p proc) (leaf-p proc))) nil)

       (bind (erl-state->bind (proc->s proc)))
       ; must have entries for parent, children, and index
       (index (erl-val-integer->val (omap::lookup 'Index bind)))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids bind)))
       (parent (omap::lookup 'Parent bind))
       ((unless (check-children pid children net0)) nil)
       ((unless (check-parent pid parent net0)) nil)
       ((unless (check-indices index children net0)) nil))
    (cond
      ((root-p proc)
       (b* (((unless (non-root-segment-p (omap::tail net))) nil)
            ((unless (wtree0-p (omap::tail net) net0 n)) nil)
            (rpid (rightmost-child pid net0)))
           (if rpid
               (b* ((rproc (omap::lookup rpid net0))
                    (rbind (erl-state->bind (proc->s rproc)))
                    (rindex (erl-val-integer->val (omap::lookup 'Index rbind))))
                  (equal rindex (- n 1))) ; if 0 indexed
               (and (null children) (equal n 1)))))
      ((leaf-p proc) (wtree0-p (omap::tail net) net0 n))
      (t nil))))


(define wtree-p ((net network-p))
  :returns (r booleanp)
  (b* ((net (network-fix net)))
      (wtree0-p net net (omap::size net))))
