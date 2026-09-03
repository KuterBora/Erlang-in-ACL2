(in-package "ACL2")
(include-book "spawn")

(set-induction-depth-limit 1)

; TODO: doc and defsec

; Wtree properties

; Root of a reduce worker tree
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
           (equal (erl-val-kind children) :cons)
           (pid-lst-p (erl-val-cons->lst children))))
  ///
    (defcong proc-equiv equal (root-p p) 1)

    (defrule bidnings-of-root
      (implies
        (root-p p)
        (and (omap::assoc 'Index (erl-state->bind (proc->s p)))
             (omap::assoc 'Parent (erl-state->bind (proc->s p)))
             (omap::assoc 'ChildPids (erl-state->bind (proc->s p))))))
    
    (defrule erl-val-kind-of-root
      (implies
        (root-p p)
        (and
          (equal (erl-val-kind (omap::lookup 'Index (erl-state->bind (proc->s p)))) :integer)
          (equal (erl-val-kind (omap::lookup 'Parent (erl-state->bind (proc->s p)))) :atom)
          (equal (erl-val-kind (omap::lookup 'ChildPids (erl-state->bind (proc->s p)))) :cons))))

    (defrule index-of-root
      (implies
        (root-p p)
        (equal (omap::lookup 'Index (erl-state->bind (proc->s p))) '(:integer 0))))

    (defrule parent-of-root
      (implies
        (root-p p)
        (equal (omap::lookup 'Parent (erl-state->bind (proc->s p))) '(:atom none))))
    
    (defrule children-of-root
      (implies
        (root-p p)
        (pid-lst-p
          (erl-val-cons->lst
            (omap::lookup 'ChildPids (erl-state->bind (proc->s p)))))))

    (defrule root-p-of-make-reduce-proc
      (root-p (make-reduce-proc self '(:atom none) children 0))
      :enable (root-p make-reduce-proc omap::from-lists omap::lookup-of-update))
    
    (defrule root-when-assoc-of-tail-is-root
      (implies (root-p (omap::lookup key (omap::tail map)))
               (root-p (omap::lookup key map)))
      :enable omap::lookup
      :disable root-p
      :use (:instance omap::assoc-of-tail-when-assoc-of-tail
              (map map) (key key))))


; Any node, but the root, in the reduce worker tree.
; TODO: rename to branch
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
           (equal (erl-val-kind children) :cons)
           (pid-lst-p (erl-val-cons->lst children))))
  ///
    (defcong proc-equiv equal (leaf-p p) 1)
    
    (defrule bindings-of-leaf
      (implies
        (leaf-p p)
        (and (omap::assoc 'Index (erl-state->bind (proc->s p)))
             (omap::assoc 'Parent (erl-state->bind (proc->s p)))
             (omap::assoc 'ChildPids (erl-state->bind (proc->s p))))))
    
    (defrule erl-val-kind-of-leaf
      (implies
        (leaf-p p)
        (and
          (equal (erl-val-kind (omap::lookup 'Index (erl-state->bind (proc->s p)))) :integer)
          (equal (erl-val-kind (omap::lookup 'Parent (erl-state->bind (proc->s p)))) :pid)
          (equal (erl-val-kind (omap::lookup 'ChildPids (erl-state->bind (proc->s p)))) :cons)))
      :enable  pid-p)

    (defrule index-of-leaf
      (implies
        (leaf-p p)
        (not
          (equal (erl-val-integer->val (omap::lookup 'Index (erl-state->bind (proc->s p)))) 0))))

    (defrule parent-of-leaf
      (implies
        (leaf-p p)
        (pid-p (omap::lookup 'Parent (erl-state->bind (proc->s p))))))
    
    (defrule children-of-leaf
      (implies
        (leaf-p p)
        (pid-lst-p
          (erl-val-cons->lst
            (omap::lookup 'ChildPids (erl-state->bind (proc->s p)))))))

    (defrule leaf-p-of-make-reduce-proc
      (implies (and (posp index) (pid-p parent))
              (leaf-p (make-reduce-proc self parent children index)))
      :enable (leaf-p make-reduce-proc omap::from-lists omap::lookup-of-update))
    
    (defrule leaf-when-assoc-of-tail-is-leaf
      (implies (leaf-p (omap::lookup key (omap::tail map)))
               (leaf-p (omap::lookup key map)))
      :enable omap::lookup
      :disable leaf-p
      :use (:instance omap::assoc-of-tail-when-assoc-of-tail
              (map map) (key key))))

(defrule index-of-wtree-node
  (implies
    (or (root-p p) (leaf-p p))
    (natp (erl-val-integer->val (omap::lookup 'Index (erl-state->bind (proc->s p))))))
  :enable (root-p leaf-p))

(defrule index-of-wtree-node-greater-than-zero
  (implies
    (or (root-p p) (leaf-p p))
    (<= 0 (erl-val-integer->val
            (omap::lookup 'Index
              (erl-state->bind (proc->s p))))))
  :enable (root-p leaf-p))

(defrule index-of-wtree-leaf-greater-than-one
  (implies
    (leaf-p p)
    (<= 0 (+ -1 (erl-val-integer->val
                  (omap::lookup 'Index
                    (erl-state->bind (proc->s p)))))))
  :enable leaf-p)

(defrule root-and-leaf-disjoint
  (implies (root-p proc) (not (leaf-p proc)))
  :enable (root-p leaf-p))

(defrule root-equiv-when-bindings-equiv
  (implies
    (and
      (root-p p1) (or (root-p p2) (leaf-p p2))
      (equal
        (omap::lookup 'Index (erl-state->bind (proc->s p1)))
        (omap::lookup 'Index (erl-state->bind (proc->s p2))))
      (equal
        (omap::lookup 'Parent (erl-state->bind (proc->s p1)))
        (omap::lookup 'Parent (erl-state->bind (proc->s p2))))
      (equal
        (omap::lookup 'ChildPids (erl-state->bind (proc->s p1)))
        (omap::lookup 'ChildPids (erl-state->bind (proc->s p2)))))
    (root-p p2))
  :enable root-p)

(defrule leaf-equiv-when-bindings-equiv
  (implies
    (and
      (leaf-p p1) (or (root-p p2) (leaf-p p2))
      (equal
        (omap::lookup 'Index (erl-state->bind (proc->s p1)))
        (omap::lookup 'Index (erl-state->bind (proc->s p2))))
      (equal
        (omap::lookup 'Parent (erl-state->bind (proc->s p1)))
        (omap::lookup 'Parent (erl-state->bind (proc->s p2))))
      (equal
        (omap::lookup 'ChildPids (erl-state->bind (proc->s p1)))
        (omap::lookup 'ChildPids (erl-state->bind (proc->s p2)))))
    (leaf-p p2))
  :enable leaf-p)

; Segment of the wtree that does not contain the root.
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


; Ensure that every child of the given pid is in the network and has pid as their parent.
(define check-children ((pid pid-p) (children pid-lst-p) (net network-p))
  :returns (r booleanp)
  :measure (len (erl-vlst-fix children))
  (b* ((pid (pid-fix pid))
       (children (pid-lst-fix children))
       (net (network-fix net))
       ((if (null children)) t)
       (cpid (car children))
       ((unless (omap::assoc cpid net)) nil)
       (cproc (omap::lookup cpid net))
       ((unless (leaf-p cproc)) nil)
       (bind (erl-state->bind (proc->s cproc)))
       ((unless (equal (omap::lookup 'Parent bind) pid)) nil)
       ; No child is listed twice.  The reduce loop drops ChildHd from CPids
       ; once it has folded in that child's message, and a child that occurred
       ; again would still be listed as outstanding afterwards -- so its
       ; sent-message-wf, which by then rests on having been dropped, would
       ; fail.  Its own message cannot arrive twice either: it terminates after
       ; sending one.
       ((when (member-equal cpid (cdr children))) nil))
      (check-children pid (cdr children) net))
  ///
    (defcong pid-equiv equal (check-children pid children net) 1)
    (defcong pid-lst-equiv equal (check-children pid children net) 2)
    (defcong network-equiv equal (check-children pid children net) 3)
    
    (defrule check-children-of-update
      (implies
        (and (network-p net) (network-p (omap::update pid proc net))
             (not (omap::assoc pid net)) (check-children i chl net))
        (check-children i chl (omap::update pid proc net)))
      :enable omap::lookup-of-update)
    
    (defrule check-children-of-update-assoc
      (implies
        (and
          (network-p net) (network-p (omap::update pid proc net))
          (pid-p pid) (proc-p proc) (omap::assoc pid net)
          (or (leaf-p proc) (root-p proc))
          (equal (omap::lookup 'Parent (erl-state->bind (proc->s proc)))
                (omap::lookup 'Parent
                  (erl-state->bind (proc->s (omap::lookup pid net)))))
          (equal (omap::lookup 'ChildPids (erl-state->bind (proc->s proc)))
                (omap::lookup 'ChildPids
                  (erl-state->bind (proc->s (omap::lookup pid net)))))
          (check-children i chl net))
        (check-children i chl (omap::update pid proc net)))
      :enable omap::lookup-of-update)

    (defrule check-children-of-nil (check-children pid nil net))

    (defrule check-children-of-cons
      (implies
        (and
          (network-p net) (pid-p cpid)
          (pid-lst-p chl) (omap::assoc cpid net)
          (leaf-p (omap::lookup cpid net))
          (equal
            (omap::lookup 'Parent
              (erl-state->bind (proc->s (omap::lookup cpid net))))
            pid)
          (not (member-equal cpid chl))
          (check-children pid chl net))
        (check-children pid (cons cpid chl) net))))


; Ensure that the parent of the given pid is in the network and has pid as its child.
(define check-parent ((pid pid-p) (parent erl-val-p) (net network-p))
  :returns (r booleanp)
  (b* ((pid (pid-fix pid))
       (parent (erl-val-fix parent))
       (net (network-fix net))
       ((unless (omap::assoc pid net)) nil)
       ((unless (pid-p parent)) (root-p (omap::lookup pid net)))
       ; A node is not its own parent.  This is a structural fact about the
       ; tree, but the invariant proofs need it: a :run step updates one pid,
       ; and without this they cannot rule out that the pid being updated is
       ; also its own parent -- in which case a node that terminates would
       ; observe its own parent as terminated.
       ((when (equal parent pid)) nil)
       ((unless (omap::assoc parent net)) nil)
       (pproc (omap::lookup parent net))
       ((unless (or (leaf-p pproc) (root-p pproc))) nil)
       (bind (erl-state->bind (proc->s pproc)))
       (cpids (erl-val-cons->lst (omap::lookup 'ChildPids bind))))
      (not (null (member-equal pid cpids))))
  ///
    (defcong pid-equiv equal (check-parent pid parent net) 1)
    (defcong erl-val-equiv equal (check-parent pid parent net) 2)
    (defcong network-equiv equal (check-parent pid parent net) 3)
    
    (defrule check-parent-of-update
      (implies
        (and
          (network-p net) (network-p (omap::update pid proc net))
          (not (omap::assoc pid net)) (check-parent i p net))
        (check-parent i p (omap::update pid proc net)))
      :enable omap::lookup-of-update)
        
    (defrule check-parent-of-update-assoc
      (implies
        (and
          (network-p net) (network-p (omap::update pid proc net))
          (pid-p pid) (proc-p proc) (omap::assoc pid net)
          (or (leaf-p proc) (root-p proc))
          (or (leaf-p (omap::lookup pid net)) (root-p (omap::lookup pid net)))
          (equal (omap::lookup 'Index (erl-state->bind (proc->s proc)))
                 (omap::lookup 'Index
                   (erl-state->bind (proc->s (omap::lookup pid net)))))
          (equal (omap::lookup 'Parent (erl-state->bind (proc->s proc)))
                 (omap::lookup 'Parent
                   (erl-state->bind (proc->s (omap::lookup pid net)))))
          (equal (omap::lookup 'ChildPids (erl-state->bind (proc->s proc)))
                 (omap::lookup 'ChildPids
                   (erl-state->bind (proc->s (omap::lookup pid net)))))
          (check-parent i p net))
        (check-parent i p (omap::update pid proc net)))
      :enable (check-parent omap::lookup-of-update))

    (defrule check-parent-of-root
      (implies
        (and (network-p net) (pid-p pid)
             (omap::assoc pid net)
             (root-p (omap::lookup pid net)))
        (check-parent pid '(:atom none) net))))


; If it exists, return the rightmost child of the given pid in the network,
; otherwise (for example, if there is a cycle) return nil.
(define rightmost-child0 ((pid pid-p) (net network-p) (fuel natp))
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
      (rightmost-child0 cpid net (- fuel 1)))
  ///
    (defcong pid-equiv equal (rightmost-child0 pid net fuel) 1)
    (defcong network-equiv equal (rightmost-child0 pid net fuel) 2)
    (defcong nat-equiv equal (rightmost-child0 pid net fuel) 3)

    (more-returns
      (rpid :name erl-pid-or-nil-of-rightmost-child0
        (or (null rpid) (pid-p rpid)))
      (rpid :name assoc-of-rightmost-child0
        (implies (and rpid (network-p net)) (omap::assoc rpid net)))
      (rpid :name node-p-of-rightmost-child0
        (implies
          (and rpid (network-p net))
          (or (leaf-p (omap::lookup rpid net))
              (root-p (omap::lookup rpid net)))))
      (rpid :name no-children-of-rightmost-child0
        (implies
          (and (pid-p rpid) (network-p net))
          (null
            (erl-val-cons->lst
              (omap::lookup
                'ChildPids
                (erl-state->bind (proc->s (omap::lookup rpid net)))))))))
    
    (defruled increase-fuel-of-rightmost-child0
      (implies
        (and (rightmost-child0 pid net f1)
             (<= (nfix f1) (nfix f2)))
        (equal (rightmost-child0 pid net f2)
               (rightmost-child0 pid net f1))))
    
    (defrule rightmost-child0-of-update
      (implies
        (and
          (network-p net) (network-p (omap::update pid proc net))
          (not (omap::assoc pid net))
          (rightmost-child0 i net fuel))
        (equal (rightmost-child0 i (omap::update pid proc net) fuel)
               (rightmost-child0 i net fuel)))
      :enable omap::lookup-of-update
      :induct (rightmost-child0 i net fuel)
      :expand (rightmost-child0 i (omap::update pid proc net) fuel))

    (defrule rightmost-child0-of-update-assoc
      (implies
        (and
          (network-p net) (network-p (omap::update pid proc net))
          (pid-p pid) (proc-p proc) (omap::assoc pid net)
          (or (leaf-p proc) (root-p proc))
          (or (leaf-p (omap::lookup pid net)) (root-p (omap::lookup pid net)))
          (equal (omap::lookup 'Index (erl-state->bind (proc->s proc)))
                 (omap::lookup 'Index
                   (erl-state->bind (proc->s (omap::lookup pid net)))))
          (equal (omap::lookup 'Parent (erl-state->bind (proc->s proc)))
                 (omap::lookup 'Parent
                   (erl-state->bind (proc->s (omap::lookup pid net)))))
          (equal (omap::lookup 'ChildPids (erl-state->bind (proc->s proc)))
                 (omap::lookup 'ChildPids
                   (erl-state->bind (proc->s (omap::lookup pid net))))))
        (equal (rightmost-child0 i (omap::update pid proc net) fuel)
               (rightmost-child0 i net fuel)))
      :enable (omap::lookup-of-update)
      :disable (zp-open nfix assoc-of-runnable? runnable-of-tail
                lookup-of-tail-when-assoc-tail-of-network
                omap::assoc-when-assoc-tail last network-p-of-tail)
      :induct (rightmost-child0 i net fuel)
      :expand (rightmost-child0 i (omap::update pid proc net) fuel))

    (defrule rightmost-child0-of-end
      (implies
        (and
          (network-p net) (pid-p self) (natp index)
          (or (and (pid-p parent) (> index 0))
              (and (equal parent '(:atom none)) (equal index 0)))
          (natp fuel) (> fuel 0))
        (equal
          (rightmost-child0 self
            (omap::update self (make-reduce-proc self parent nil index) net) fuel)
          self)))
    
    (defrule rightmost-child0-when-no-children
      (implies
        (and
          (network-p net) (not (omap::emptyp net))
          (omap::assoc pid net)
          (or (leaf-p (omap::lookup pid net))
              (root-p (omap::lookup pid net)))
          (not
            (erl-val-cons->lst
              (omap::lookup 'ChildPids
                (erl-state->bind
                  (proc->s
                    (omap::lookup pid net)))))))
        (equal (rightmost-child0 pid net (omap::size net)) pid))))

; If it exists, return the rightmost child of the given pid in the network,
; otherwise (for example, if there is a cycle) return nil.
; - call rightmost-child0 with the size of the network as fuel. This will
;   make it terminate, and return nil, in case of a cycle.
(define rightmost-child ((pid pid-p) (net network-p))
  :returns rpid
  (b* ((pid (pid-fix pid))
       (net (network-fix net)))
  (rightmost-child0 pid net (omap::size net)))
  ///
    (defcong pid-equiv equal (rightmost-child pid net) 1)
    (defcong network-equiv equal (rightmost-child pid net) 2)

    (more-returns
      (rpid :name erl-pid-or-nil-of-rightmost-child
        (or (null rpid) (pid-p rpid))
        :hints (("Goal" :use (:instance erl-pid-or-nil-of-rightmost-child0
                               (fuel (omap::size (network-fix net)))))))
      (rpid :name assoc-of-rightmost-child
        (implies (and rpid (network-p net)) (omap::assoc rpid net))
        :hints (("Goal" :use (:instance assoc-of-rightmost-child0
                               (fuel (omap::size (network-fix net)))))))
      (rpid :name node-p-of-rightmost-child
        (implies
          (and rpid (network-p net))
          (or (leaf-p (omap::lookup rpid net))
              (root-p (omap::lookup rpid net))))
        :hints (("Goal" :use (:instance node-p-of-rightmost-child0
                               (fuel (omap::size (network-fix net)))))))
      (rpid :name no-children-of-rightmost-child
        (implies
          (and (pid-p rpid) (network-p net))
          (null
            (erl-val-cons->lst
              (omap::lookup
                'ChildPids
                (erl-state->bind (proc->s (omap::lookup rpid net)))))))
        :hints (("Goal" :use (:instance no-children-of-rightmost-child0
                               (fuel (omap::size (network-fix net))))))))
    
    (defrule rightmost-child-of-update
      (implies
        (and (network-p net) (network-p (omap::update key v net))
             (not (omap::assoc key net))
             (rightmost-child i net))
        (equal (rightmost-child i (omap::update key v net))
               (rightmost-child i net)))
      :enable rightmost-child
      :use ((:instance increase-fuel-of-rightmost-child0
              (pid i) (f1 (omap::size net))
              (f2 (omap::size (omap::update key v net))))))

(defrule rightmost-child-of-update-assoc
  (implies
    (and
      (network-p net) (network-p (omap::update pid proc net))
      (pid-p pid) (proc-p proc) (omap::assoc pid net)
      (or (leaf-p proc) (root-p proc))
      (or (leaf-p (omap::lookup pid net)) (root-p (omap::lookup pid net)))
      (equal (omap::lookup 'Index (erl-state->bind (proc->s proc)))
             (omap::lookup 'Index
               (erl-state->bind (proc->s (omap::lookup pid net)))))
      (equal (omap::lookup 'Parent (erl-state->bind (proc->s proc)))
             (omap::lookup 'Parent
               (erl-state->bind (proc->s (omap::lookup pid net)))))
      (equal (omap::lookup 'ChildPids (erl-state->bind (proc->s proc)))
             (omap::lookup 'ChildPids
               (erl-state->bind (proc->s (omap::lookup pid net))))))
    (equal (rightmost-child i (omap::update pid proc net))
           (rightmost-child i net))))

    (defrule rightmost-child-of-end
      (implies
        (and (network-p net) (pid-p cpid) (omap::assoc cpid net)
             (leaf-p (omap::lookup cpid net))
             (not (erl-val-cons->lst
                    (omap::lookup 'ChildPids
                      (erl-state->bind (proc->s (omap::lookup cpid net)))))))
        (equal (rightmost-child cpid net) cpid))
      :expand (rightmost-child0 cpid net (omap::size net))))


; Check if the indices of the nodes in the reduce work tree are well formed.
;   W0 
;   |  \ 
;   |    \ W2
;   | \    | \
;   |  |   |  |
;   W0 W1  W2 W3
; For each node with index i,
; - the first (leftmost) child must have index = i + 1
; - the rightmost child of the first child must have 1 less than
;   the index of the second child.
; BOZO: I hope that description makes sense!
(define check-indices ((index natp) (children pid-lst-p) (net network-p))
  :returns (r booleanp)
  :measure (len (pid-lst-fix children))
  :guard-hints
    (("Goal" :use ((:instance node-p-of-rightmost-child (net net) (pid (car children))))))
  (b* ((index (nfix index))
       (children (pid-lst-fix children))
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
      (check-indices rindex (cdr children) net))
  ///
    (defcong nat-equiv equal (check-indices i c n) 1
      :hints
        (("Goal" :in-theory (disable nfix)
                 :expand ((check-indices i c n) (check-indices i-equiv c n)))))
    (defcong pid-lst-equiv equal (check-indices i c n) 2
      :hints
        (("Goal" :expand ((check-indices i c n) (check-indices i c-equiv n)))))
    (defcong network-equiv equal (check-indices i c n) 3
      :hints
        (("Goal" :expand ((check-indices i c n) (check-indices i c n-equiv)))))
    
    (defrule check-indices-of-nil (check-indices i nil net))
    
    (defrule check-indices-of-update
      (implies
        (and (network-p net) (network-p (omap::update pid proc net))
             (not (omap::assoc pid net))
             (check-indices i chl net))
        (check-indices i chl (omap::update pid proc net)))
      :enable (omap::lookup-of-update)
      :induct (check-indices i chl net)
      :expand (check-indices i chl (omap::update pid proc net)))
    
    (defrule check-indices-of-update-assoc
      (implies
        (and
          (network-p net) (network-p (omap::update pid proc net))
          (pid-p pid) (proc-p proc) (omap::assoc pid net)
          (or (leaf-p proc) (root-p proc))
          (or (leaf-p (omap::lookup pid net)) (root-p (omap::lookup pid net)))
          (equal (omap::lookup 'Index (erl-state->bind (proc->s proc)))
                (omap::lookup 'Index
                  (erl-state->bind (proc->s (omap::lookup pid net)))))
          (equal (omap::lookup 'Parent (erl-state->bind (proc->s proc)))
                (omap::lookup 'Parent
                  (erl-state->bind (proc->s (omap::lookup pid net)))))
          (equal (omap::lookup 'ChildPids (erl-state->bind (proc->s proc)))
                (omap::lookup 'ChildPids
                  (erl-state->bind (proc->s (omap::lookup pid net)))))
          (check-indices i chl net))
        (check-indices i chl (omap::update pid proc net)))
      :enable (omap::lookup-of-update)
      :disable nfix
      :induct (check-indices i chl net)
      :expand (check-indices i chl (omap::update pid proc net)))

    (defrule check-indices-of-cons
       (implies
         (and
           (network-p net) (omap::assoc cpid net)
           (leaf-p (omap::lookup cpid net))
           (rightmost-child cpid net) (natp i)
           (equal (erl-val-integer->val
                    (omap::lookup 'Index
                      (erl-state->bind (proc->s (omap::lookup cpid net)))))
                  (+ 1 i))  
           (check-indices
             (erl-val-integer->val
               (omap::lookup 'Index
                 (erl-state->bind
                   (proc->s
                     (omap::lookup
                       (rightmost-child cpid net) net)))))
             chl net))
         (check-indices i (cons cpid chl) net))
       :expand (check-indices i (cons cpid chl) net)
       :disable check-indices))


; The body of wtree-p
(define wtree0-p ((net network-p) (net0 network-p) (n natp))
  :returns (r booleanp)
  :measure (acl2-count (network-fix net))
  :guard-hints
    (("Goal"
      :in-theory (disable node-p-of-rightmost-child index-of-leaf)
      :use
        ((:instance index-of-leaf (p (mv-nth 1 (omap::head net))))
         (:instance node-p-of-rightmost-child (net net0) (pid (mv-nth 0 (omap::head net))))
         (:instance node-p-of-rightmost-child (net net0) (pid (mv-nth 0 (omap::head net)))))))
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
       (bind (erl-state->bind (proc->s proc)))
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
            (rbind (erl-state->bind (proc->s rproc)))
            (rindex (erl-val-integer->val (omap::lookup 'Index rbind))))
          (equal rindex (- n 1))))   
      ((leaf-p proc) (wtree0-p (omap::tail net) net0 n))
      (t nil)))
  ///
    (defcong network-equiv equal (wtree0-p net net0 n) 1)
    (defcong network-equiv equal (wtree0-p net net0 n) 2)
    (defcong nat-equiv equal (wtree0-p net net0 n) 3)
    
    ; TODO: For my current implementation of wtree-p, I have
    ; to state n > 0. However, I would like to change that.
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