(in-package "ACL2")
(include-book "../reduce-proc")

(set-induction-depth-limit 1)

; This file contains helpers for the function wtree-p.

; Bindings of Wtree ------------------------------------------------------------

; Wtree-bind are auxillary variables of a Wtree's node which keep track
; of the parent, children, and index the process was spawned with.
;
; BOZO: This was a last minute fix, as I had somehow forgotten that
; a function call loses the scope before the call.In fact, this will
; not work if there is more code, after the call to reduce, which
; there would definitely be. A better solution might be to seperate the
; auxillary variables from the Erlang process, and have a different data
; structure that keeps track of them.
(define wtree-bind0 ((bind bind-p) (klst erl-klst-p))
  :returns (b bind-p)
  (b* ((klst (erl-klst-fix klst))
       ((unless (consp klst)) (bind-fix bind))
       (kont (erl-k->kont (car (last klst))))
       ((unless (equal (kont-kind kont) :function-return)) (bind-fix bind)))
      (kont-function-return->bind kont))
  ///
    (defcong bind-equiv equal (wtree-bind0 bind klst) 1)
    (defcong erl-klst-equiv equal (wtree-bind0 bind klst) 2)

    (defrule wtree-bind0-of-nil
      (equal (wtree-bind0 bind nil) (bind-fix bind)))
    (defrule wtree-bind0-when-no-function-return
      (implies
        (or (not (consp (erl-klst-fix klst)))
            (not (equal (kont-kind (erl-k->kont (car (last (erl-klst-fix klst)))))
                        :function-return)))
        (equal (wtree-bind0 bind klst) (bind-fix bind)))))

(define wtree-bind ((p proc-p))
  :returns (b bind-p)
  (wtree-bind0 (erl-state->bind (proc->s p)) (proc->klst p))
  ///
    (defcong proc-equiv equal (wtree-bind p) 1)
    (defrule wtree-bind-of-proc
      (equal (wtree-bind (proc ps s inew itried klst))
             (wtree-bind0 (erl-state->bind (erl-state-fix s))
                          (erl-klst-fix klst))))

    (defrule wtree-bind0-to-wtree-bind
      (equal (wtree-bind0 (erl-state->bind (proc->s p))
                          (proc->klst p))
             (wtree-bind p)))

    (defrule wtree-bind-when-no-function-return
      (implies
        (or (not (consp (proc->klst p)))
            (not
              (equal
                (kont-kind
                  (erl-k->kont (car (last (proc->klst p)))))
                :function-return)))
        (equal (wtree-bind p) (erl-state->bind (proc->s p))))
      :enable wtree-bind0
      :disable wtree-bind0-to-wtree-bind)

    (defrule wtree-bind-of-make-reduce-proc
      (equal (wtree-bind
              (make-reduce-proc self parent children index))
             (erl-state->bind
              (proc->s
                (make-reduce-proc self parent children index))))
      :enable (make-reduce-proc wtree-bind0)
      :disable wtree-bind0-to-wtree-bind)
    
    (defrule wtree-bind-of-lookup-of-update-when-wtree-bind-equal
      (implies
        (and (network-p net) (omap::assoc q net)
             (equal (wtree-bind qproc) (wtree-bind (omap::lookup q net))))
        (equal (wtree-bind (omap::lookup x (omap::update q qproc net)))
               (wtree-bind (omap::lookup x net))))
      :enable omap::lookup-of-update
      :disable wtree-bind)
    
    (defrule wtree-bind0-of-new-klst
      (implies
        (equal
          klst
          (proc->klst
            (make-reduce-proc self parent children index)))
        (equal (wtree-bind0 bind klst) (bind-fix bind)))
      :enable make-reduce-proc)
    
    (defrule wtree-bind-of-new-proc
      (implies
        (and
          (equal
            (proc->s p)
            (proc->s (make-reduce-proc self parent children index)))
          (equal (proc->klst p)
                 (proc->klst
                   (make-reduce-proc self parent children index))))
        (equal (wtree-bind p) (erl-state->bind (proc->s p))))
      :enable (wtree-bind0 make-reduce-proc)
      :disable wtree-bind0-to-wtree-bind)
    
    (defruled wtree-bind-when-fields-equal
      (implies
        (and (equal (proc->s p1) (proc->s p2))
             (equal (proc->klst p1) (proc->klst p2)))
        (equal (wtree-bind p1) (wtree-bind p2)))
      :disable wtree-bind0-to-wtree-bind)

    (defrule wtree-bind-of-proc-receive
      (implies
        (and (equal (proc->s (proc-receive p)) (proc->s p))
             (equal (proc->klst (proc-receive p)) (proc->klst p)))
        (equal (wtree-bind (proc-receive p)) (wtree-bind p)))
      :use ((:instance wtree-bind-when-fields-equal
              (p1 (proc-receive p)) (p2 p)))
      :disable (wtree-bind proc-receive))

    (defrule wtree-bindings-of-make-reduce-proc
      (implies
        (and
          (equal
            (proc->s p)
            (proc->s (make-reduce-proc self parent children index)))
          (equal
            (proc->klst p)
            (proc->klst (make-reduce-proc self parent children index))))
        (equal
          (omap::from-lists
            '(ChildPids Parent Index)
            (list (omap::lookup 'ChildPids (wtree-bind p))
                  (omap::lookup 'Parent (wtree-bind p))
                  (omap::lookup 'Index (wtree-bind p))))
          (erl-state->bind (proc->s p))))
    :use ((:instance wtree-bind-of-new-proc)
          (:instance bindings-of-make-reduce-proc (s (proc->s p))))
    :disable
      (wtree-bind-of-new-proc wtree-bind
       bindings-of-make-reduce-proc)))

; Nodes of Wtree ---------------------------------------------------------------

; Root is the master process which would have initiated the reduce.
(define root-p ((p proc-p))
  :returns (r booleanp)
  (b* ((p (proc-fix p))
       (bind (wtree-bind p))
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

    (defrule bindings-of-root
      (implies
        (root-p p)
        (and (omap::assoc 'Index (wtree-bind p))
             (omap::assoc 'Parent (wtree-bind p))
             (omap::assoc 'ChildPids (wtree-bind p)))))
    
    (defrule erl-val-kind-of-root
      (implies
        (root-p p)
        (and
          (equal (erl-val-kind (omap::lookup 'Index (wtree-bind p))) :integer)
          (equal (erl-val-kind (omap::lookup 'Parent (wtree-bind p))) :atom)
          (equal (erl-val-kind (omap::lookup 'ChildPids (wtree-bind p))) :cons))))

    (defrule index-of-root
      (implies
        (root-p p)
        (equal (omap::lookup 'Index (wtree-bind p)) '(:integer 0))))

    (defrule parent-of-root
      (implies
        (root-p p)
        (equal (omap::lookup 'Parent (wtree-bind p)) '(:atom none))))
    
    (defrule children-of-root
      (implies
        (root-p p)
        (pid-lst-p
          (erl-val-cons->lst
            (omap::lookup 'ChildPids (wtree-bind p))))))

    (defrule root-p-of-make-reduce-proc
      (root-p (make-reduce-proc self '(:atom none) children 0))
      :enable (root-p make-reduce-proc omap::from-lists omap::lookup-of-update))
    
    (defrule root-when-assoc-of-tail-is-root
      (implies (root-p (omap::lookup key (omap::tail map)))
               (root-p (omap::lookup key map)))
      :enable omap::lookup
      :disable root-p
      :use (:instance omap::assoc-of-tail-when-assoc-of-tail
              (map map) (key key)))
    
    (defrule root-p-of-change-proc-of-outbox
      (equal
        (root-p (change-proc p
                  :s (update-erl-state->outbox (proc->s p) ob)))
        (root-p p)))
    
    (defrule root-p-of-change-proc-of-inbox
      (equal
        (root-p (change-proc p :inbox-new inew :ps ps))
        (root-p p))))



; Any node, but the root, in the reduce worker tree.
; TODO: a better name could have been branch-p, as this
; predicate includes nodes in the middle of the tree.
(define leaf-p ((p proc-p))
  :returns (r booleanp)
  (b* ((p (proc-fix p))
       (bind (wtree-bind p))
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
        (and (omap::assoc 'Index (wtree-bind p))
             (omap::assoc 'Parent (wtree-bind p))
             (omap::assoc 'ChildPids (wtree-bind p)))))
    
    (defrule erl-val-kind-of-leaf
      (implies
        (leaf-p p)
        (and
          (equal (erl-val-kind (omap::lookup 'Index (wtree-bind p))) :integer)
          (equal (erl-val-kind (omap::lookup 'Parent (wtree-bind p))) :pid)
          (equal (erl-val-kind (omap::lookup 'ChildPids (wtree-bind p))) :cons)))
      :enable  pid-p)

    (defrule index-of-leaf
      (implies
        (leaf-p p)
        (not
          (equal (erl-val-integer->val (omap::lookup 'Index (wtree-bind p))) 0))))

    (defrule parent-of-leaf
      (implies
        (leaf-p p)
        (pid-p (omap::lookup 'Parent (wtree-bind p)))))
    
    (defrule children-of-leaf
      (implies
        (leaf-p p)
        (pid-lst-p
          (erl-val-cons->lst
            (omap::lookup 'ChildPids (wtree-bind p))))))

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
              (map map) (key key)))
    
    (defrule leaf-p-of-change-proc-of-outbox
      (equal
        (leaf-p (change-proc p
                  :s (update-erl-state->outbox (proc->s p) o)))
        (leaf-p p)))
    
    (defrule leaf-p-of-change-proc-of-inbox
      (equal
        (leaf-p (change-proc p :inbox-new inew :ps ps))
        (leaf-p p))))


(defrule index-of-wtree-node
  (implies
    (or (root-p p) (leaf-p p))
    (natp (erl-val-integer->val (omap::lookup 'Index (wtree-bind p)))))
  :enable (root-p leaf-p))

(defrule index-of-wtree-node-greater-than-zero
  (implies
    (or (root-p p) (leaf-p p))
    (<= 0 (erl-val-integer->val
            (omap::lookup 'Index (wtree-bind p)))))
  :enable (root-p leaf-p))

(defrule index-of-wtree-leaf-greater-than-one
  (implies
    (leaf-p p)
    (<= 0 (+ -1 (erl-val-integer->val
                  (omap::lookup 'Index (wtree-bind p))))))
  :enable leaf-p)

(defrule root-and-leaf-disjoint
  (implies (root-p proc) (not (leaf-p proc)))
  :enable (root-p leaf-p))

(defrule root-equiv-when-bindings-equiv
  (implies
    (and
      (root-p p1) (or (root-p p2) (leaf-p p2))
      (equal
        (omap::lookup 'Index (wtree-bind p1))
        (omap::lookup 'Index (wtree-bind p2)))
      (equal
        (omap::lookup 'Parent (wtree-bind p1))
        (omap::lookup 'Parent (wtree-bind p2)))
      (equal
        (omap::lookup 'ChildPids (wtree-bind p1))
        (omap::lookup 'ChildPids (wtree-bind p2))))
    (root-p p2))
  :enable root-p)

(defrule leaf-equiv-when-bindings-equiv
  (implies
    (and
      (leaf-p p1) (or (root-p p2) (leaf-p p2))
      (equal
        (omap::lookup 'Index (wtree-bind p1))
        (omap::lookup 'Index (wtree-bind p2)))
      (equal
        (omap::lookup 'Parent (wtree-bind p1))
        (omap::lookup 'Parent (wtree-bind p2)))
      (equal
        (omap::lookup 'ChildPids (wtree-bind p1))
        (omap::lookup 'ChildPids (wtree-bind p2))))
    (leaf-p p2))
  :enable leaf-p)

(defruled leaf-root-p-when-bind-equal
  (implies
    (equal (wtree-bind p1) (wtree-bind p2))
    (and (equal (leaf-p p1) (leaf-p p2))
         (equal (root-p p1) (root-p p2))))
  :enable (leaf-p root-p)
  :disable
    (bindings-of-leaf omap::assoc-when-assoc-tail
     bindings-of-root omap::assoc-when-emptyp))

(defrule leaf-root-p-of-bind-equal-of-update
  (implies
    (and
      (network-p net) (omap::assoc q net)
      (equal
        (wtree-bind qproc)
        (wtree-bind (omap::lookup q net))))
    (and (equal (leaf-p (omap::lookup x (omap::update q qproc net)))
                (leaf-p (omap::lookup x net)))
         (equal (root-p (omap::lookup x (omap::update q qproc net)))
                (root-p (omap::lookup x net)))))
  :use ((:instance leaf-root-p-when-bind-equal
          (p1 (omap::lookup x (omap::update q qproc net)))
          (p2 (omap::lookup x net)))))

; TODO: I seem to need a lot of lemmas about leaf and root eqivalenece.
; There is a cleaner way of doing this, by defining fixtypes for leaf
; and root. I will implement it at some point.
; - This lemma is also disabled. I have to call to call it manually,
;   which is tedious.
(defruled leaf-root-p-when-wtree-bindings-equal
  (implies
    (and (iff (omap::assoc 'Index (wtree-bind p1))
              (omap::assoc 'Index (wtree-bind p2)))
         (iff (omap::assoc 'Parent (wtree-bind p1))
              (omap::assoc 'Parent (wtree-bind p2)))
         (iff (omap::assoc 'ChildPids (wtree-bind p1))
              (omap::assoc 'ChildPids (wtree-bind p2)))
         (equal (omap::lookup 'Index (wtree-bind p1))
                (omap::lookup 'Index (wtree-bind p2)))
         (equal (omap::lookup 'Parent (wtree-bind p1))
                (omap::lookup 'Parent (wtree-bind p2)))
         (equal (omap::lookup 'ChildPids (wtree-bind p1))
                (omap::lookup 'ChildPids (wtree-bind p2))))
    (and (equal (leaf-p p1) (leaf-p p2))
         (equal (root-p p1) (root-p p2))))
  :enable (leaf-p root-p)
  :disable
    (bindings-of-leaf omap::assoc-when-assoc-tail
     bindings-of-root omap::assoc-when-emptyp))

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


; Check-Children ---------------------------------------------------------------

; Check if the children of a wtree node are well-formed.
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
       (bind (wtree-bind cproc))
       ((unless (equal (omap::lookup 'Parent bind) pid)) nil)
       ((if (member-equal cpid (cdr children))) nil))
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
          (equal (omap::lookup 'Parent (wtree-bind proc))
                (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))))
          (equal (omap::lookup 'ChildPids (wtree-bind proc))
                (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net))))
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
            (omap::lookup 'Parent (wtree-bind (omap::lookup cpid net)))
            pid)
          (not (member-equal cpid chl))
          (check-children pid chl net))
        (check-children pid (cons cpid chl) net)))

    (defruled no-duplicatesp-of-check-children
      (implies (check-children pid children net)
               (no-duplicatesp-equal (pid-lst-fix children)))))


; Check-Parent ---------------------------------------------------------------

; Check if the parent of a wtree node is well-formed.
(define check-parent ((pid pid-p) (parent erl-val-p) (net network-p))
  :returns (r booleanp)
  (b* ((pid (pid-fix pid))
       (parent (erl-val-fix parent))
       (net (network-fix net))
       ((unless (omap::assoc pid net)) nil)
       ((unless (pid-p parent)) (root-p (omap::lookup pid net)))
       ((if (equal parent pid)) nil)
       ((unless (omap::assoc parent net)) nil)
       (pproc (omap::lookup parent net))
       ((unless (or (leaf-p pproc) (root-p pproc))) nil)
       (bind (wtree-bind pproc))
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
          (equal (omap::lookup 'Index (wtree-bind proc))
                 (omap::lookup 'Index (wtree-bind (omap::lookup pid net))))
          (equal (omap::lookup 'Parent (wtree-bind proc))
                 (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))))
          (equal (omap::lookup 'ChildPids (wtree-bind proc))
                 (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net))))
          (check-parent i p net))
        (check-parent i p (omap::update pid proc net)))
      :enable (check-parent omap::lookup-of-update))

    (defrule check-parent-of-root
      (implies
        (and (network-p net) (pid-p pid)
             (omap::assoc pid net)
             (root-p (omap::lookup pid net)))
        (check-parent pid '(:atom none) net))))


; Rightmost-Child ------------------------------------------------------------

; If it exists, return the rightmost child of the given pid in the network,
; otherwise (for example, if there is a cycle) return nil.
(define rightmost-child0 ((pid pid-p) (net network-p) (fuel natp))
  :returns rpid
  :measure (nfix fuel)
  :guard-hints
    (("Goal" :in-theory (enable erl-val-crock)))
  :hints (("Goal" :in-theory
    (disable last-when-atom-of-cdr last
             consp-of-cdr-of-erl-vlst erl-vlst-p-of-pid-lst
             pid-lst-p-of-cdr-when-pid-lst-p)))
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
       (bind (wtree-bind proc))
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

    (local (in-theory
      (disable
        consp-of-cdr-of-erl-vlst
        wtree-bind-when-no-function-return erl-vlst-p-of-pid-lst
        lookup-of-tail-when-assoc-tail-of-network
        pid-lst-p-of-cdr-when-pid-lst-p assoc-of-runnable?
        omap::assoc-when-assoc-tail)))
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
              (omap::lookup 'ChildPids (wtree-bind (omap::lookup rpid net))))))))

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
          (equal (omap::lookup 'Index (wtree-bind proc))
                 (omap::lookup 'Index (wtree-bind (omap::lookup pid net))))
          (equal (omap::lookup 'Parent (wtree-bind proc))
                 (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))))
          (equal (omap::lookup 'ChildPids (wtree-bind proc))
                 (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net)))))
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
            (omap::update self
              (make-reduce-proc self parent nil index) net) fuel)
          self))
      :disable erl-state->bind-of-make-reduce-proc)

    (defrule rightmost-child0-when-no-children
      (implies
        (and
          (network-p net) (not (omap::emptyp net))
          (omap::assoc pid net)
          (or (leaf-p (omap::lookup pid net))
              (root-p (omap::lookup pid net)))
          (not
            (erl-val-cons->lst
              (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net))))))
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
              (omap::lookup 'ChildPids (wtree-bind (omap::lookup rpid net))))))
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
      (equal (omap::lookup 'Index (wtree-bind proc))
             (omap::lookup 'Index (wtree-bind (omap::lookup pid net))))
      (equal (omap::lookup 'Parent (wtree-bind proc))
             (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))))
      (equal (omap::lookup 'ChildPids (wtree-bind proc))
             (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net)))))
    (equal (rightmost-child i (omap::update pid proc net))
           (rightmost-child i net))))

    (defrule rightmost-child-of-end
      (implies
        (and (network-p net) (pid-p cpid) (omap::assoc cpid net)
             (leaf-p (omap::lookup cpid net))
             (not (erl-val-cons->lst
                    (omap::lookup 'ChildPids (wtree-bind (omap::lookup cpid net))))))
        (equal (rightmost-child cpid net) cpid))
      :expand (rightmost-child0 cpid net (omap::size net))))


; Check-Indices --------------------------------------------------------------

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
       (cbind (wtree-bind cproc))
       (cchildren (erl-val-cons->lst (omap::lookup 'ChildPids cbind)))
       (cindex (erl-val-integer->val (omap::lookup 'Index cbind)))
       ((unless (equal (+ 1 index) cindex)) nil)
       ((if (null cchildren)) (check-indices cindex (cdr children) net))
       (rpid (rightmost-child cpid net))
       ((unless rpid) nil)
        (rproc (omap::lookup rpid net))
        (rbind (wtree-bind rproc))
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
          (equal (omap::lookup 'Index (wtree-bind proc))
                (omap::lookup 'Index (wtree-bind (omap::lookup pid net))))
          (equal (omap::lookup 'Parent (wtree-bind proc))
                (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))))
          (equal (omap::lookup 'ChildPids (wtree-bind proc))
                (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net))))
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
                    (omap::lookup 'Index (wtree-bind (omap::lookup cpid net))))
                  (+ 1 i))  
           (check-indices
             (erl-val-integer->val
               (omap::lookup 'Index (wtree-bind (omap::lookup
                       (rightmost-child cpid net) net))))
             chl net))
         (check-indices i (cons cpid chl) net))
       :expand (check-indices i (cons cpid chl) net)
       :disable check-indices))

; This is very important for the reduce prove
(defrule check-indices-of-suffix
  (implies
    (and (network-p net) (pid-lst-p children) (pid-lst-p cps) cps
         (prefixp (rev cps) (rev children))
         (check-indices i children net))
    (check-indices
      (1- (erl-val-integer->val
            (omap::lookup 'Index (wtree-bind (omap::lookup (car cps) net)))))
      cps net))
  :enable check-indices
  :induct (check-indices i children net)
  :hints (("Subgoal *1/3" :cases ((equal cps children)))
          ("Subgoal *1/2" :cases ((equal cps children)))
          ("Subgoal *1/1" :cases ((equal cps children))))
  ; TODO: I tried using the community book, but it did not work.
  :prep-lemmas
    ((defrule len-when-prefixp
      (implies (prefixp x y) (<= (len x) (len y)))
      :rule-classes :linear :enable prefixp)
    (defrule prefixp-of-append-when-shorter
      (implies (and (prefixp x (append y z)) (<= (len x) (len y)))
               (prefixp x y)) :enable prefixp)
    (defrule equal-when-prefixp-and-same-len
      (implies
        (and (prefixp x y) (equal (len x) (len y))
             (true-listp x) (true-listp y))
        (equal x y))
      :enable prefixp :rule-classes :forward-chaining)
    (defrule suffix-cases
      (implies
        (and (true-listp cps) (true-listp children)
             cps (prefixp (rev cps) (rev children)))
        (or (equal cps children)
            (prefixp (rev cps) (rev (cdr children)))))
      :expand ((rev children))
      :use
        ((:instance equal-when-prefixp-and-same-len
          (x (rev cps)) (y (rev children)))
        (:instance len-when-prefixp
          (x (rev cps))
          (y (append (rev (cdr children)) (list (car children)))))))
    (defrule prefix-of-nil
      (implies (consp cps) (not (prefixp cps nil)))
      :enable prefixp)
    (defrule prefixp-of-rev-cdr-when-not-whole
      (implies
        (and (true-listp cps) (true-listp children)
            cps (prefixp (rev cps) (rev children))
            (not (equal cps children)))
        (prefixp (rev cps) (rev (cdr children))))
      :use suffix-cases)))
