(in-package "ACL2")
(include-book "spawn")

(set-induction-depth-limit 1)

(local (include-book "std/lists/len" :dir :system))
(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "std/lists/nth" :dir :system))

; Create wtree
(encapsulate nil
  (local (defrule compatiblep-of-tail
    (implies (omap::compatiblep a b)
             (omap::compatiblep a (omap::tail b)))))

  (local (defrule wf-network-p-of-update*
    (implies
      (and
        (wf-network-p n1)
        (wf-network-p n2)
        (network-gen-p n1)
        (network-gen-p n2)
        (omap::compatiblep n1 n2))
      (wf-network-p (omap::update* n1 n2)))
    :enable (wf-network-p omap::update*)))

  (local (defrule network-p-of-update*
    (implies (and (network-p n1) (network-p n2) (omap::compatiblep n1 n2))
             (network-p (omap::update* n1 n2)))
    :enable (network-p)))
  
  (local (defrule network-p-of-update-2
    (implies
      (and (network-p net) (pid-p pid))
      (network-p (omap::update pid (make-reduce-proc pid par chl val) net)))
    :enable (proc->pid make-reduce-proc)
    :use (:instance network-p-of-update
          (net net)
          (pid pid)
          (p (make-reduce-proc pid par chl val)))
    :rule-classes ((:rewrite :match-free :all))))
  
  (local (defrule network-p-of-update-3
    (implies
      (and (network-p net) (pid-p pid))
      (network-p (omap::update pid (proc ps (erl-state a b c d pid e) f g h) net)))
    :enable (proc->pid network-gen-p network-p)
    :rule-classes ((:rewrite :match-free :all))))
  
  (local (defrule integerp-of-nth-of-nat-listp
    (implies (and (nat-listp lst) (nth x lst))
             (natp (nth x lst)))))

  (local (defrule domain-of-network-p
    (implies (network-p n) (pid-set-p (omap::keys n)))
    :enable (network-p pid-set-p omap::keys)))

  (define create-wtree0
    ((n natp) (self pid-p) (index natp)
     (parent erl-val-p) (children erl-vlst-p)
     (pids pid-set-p) (net network-p))
    :verify-guards nil
    :returns rnet
    :measure (nfix n)
    (b* ((n (nfix n))
         (self (pid-fix self))
         (index (nfix index))
         (parent (erl-val-fix parent))
         (children (erl-vlst-fix children))
         (pids (pid-set-fix pids))
         (net (network-fix net))
         ((if (zp n)) net)
         ((if (not (set::in self pids))) nil)
         ((if (omap::assoc self net)) nil)
         ((if (equal n 1))
          (omap::update self (make-reduce-proc self parent children index) net))
         (cpid (spawn pids))
         (child-net
           (create-wtree0
              (ceiling n 2) cpid (+ index (floor n 2)) self nil
              (set::insert cpid pids) net)))
        (create-wtree0
          (floor n 2) self index parent (cons cpid children)
          (set::union pids (omap::keys child-net)) child-net))

      ///
        (more-returns
          (rnet network-p :rule-classes :type-prescription
            :hints (("Goal" :in-theory (disable nfix)))))
          
        (verify-guards create-wtree0
          :hints (("Goal" :in-theory (enable network-p))))
        
        (defcong nat-equiv equal (create-wtree0 a b c d e f g) 1)
        (defcong pid-equiv equal (create-wtree0 a b c d e f g) 2
          :hints
            (("Goal" :expand ((create-wtree0 a b c d e f g)
                              (create-wtree0 a b-equiv c d e f g)))))
        (defcong nat-equiv equal (create-wtree0 a b c d e f g) 3
          :hints
            (("Goal" :in-theory (disable nfix)
                     :expand ((create-wtree0 a b c d e f g)
                              (create-wtree0 a b c-equiv d e f g)))))
        (defcong erl-val-equiv equal (create-wtree0 a b c d e f g) 4)
        (defcong erl-vlst-equiv equal (create-wtree0 a b c d e f g) 5)
        (defcong pid-set-equiv equal (create-wtree0 a b c d e f g) 6
          :hints
            (("Goal" :expand ((create-wtree0 a b c d e f g)
                              (create-wtree0 a b c d e f-equiv g)))))
        (defcong network-equiv equal (create-wtree0 a b c d e f g) 7
          :hints
            (("Goal" :expand ((create-wtree0 a b c d e f g)
                              (create-wtree0 a b c d e f g-equiv))))))
  
  (define create-wtree ((n natp))
    :returns (rnet network-p)
    :guard-hints (("Goal" :in-theory (enable pid-set-p)))
    (b* ((n (nfix n))
         (self (spawn nil)))
        (create-wtree0 n self 0 '(:atom none) nil (list self) nil))
    ///
      (defcong nat-equiv equal (create-wtree n) 1
        :hints
          (("Goal"
             :in-theory (disable nfix)
             :expand ((create-wtree n) (create-wtree n-equiv))
             :use (:instance nat-equiv-implies-equal-create-wtree0-1
                    (a n) (b self) (c 0) (d '(:atom none))
                    (e nil) (f (list self)) (g nil)))))))


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


; return the rightmost descendent of the given pid, else nil.
; Also, make sure there is no cycle by removing visted nodes from the net.
(define rightmost-child ((pid pid-p) (net network-p))
  :returns rpid
  :measure (omap::size (network-fix net))
  :guard-hints (("Goal" :in-theory (enable erl-val-crock)))
  :prepwork
    ((local (include-book "std/lists/last" :dir :system))  
     (local (defruled erl-val-crock (implies (erl-val-p v) (consp v)))))

  (b* ((pid (pid-fix pid))
       (net (network-fix net))
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
      (rightmost-child cpid (omap::delete pid net)))
  ///
    (defcong pid-equiv equal (rightmost-child pid net) 1)
    (defcong network-equiv equal (rightmost-child pid net) 2)
    
    (more-returns
      (rpid :name erl-pid-or-nil-of-rightmost-child
        (or (null rpid) (pid-p rpid)))
      (rpid :name assoc-of-rightmost-child
        (implies (and rpid (network-p net)) (omap::assoc rpid net)))
      (rpid :name node-p-of-rightmost-child
        (implies
          (and rpid (network-p net))
          (or (leaf-p (omap::lookup rpid net))
              (root-p (omap::lookup rpid net)))))))


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
