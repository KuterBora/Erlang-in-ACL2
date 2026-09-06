(in-package "ACL2")

(include-book "../wtree/wtree-theorems")
(set-induction-depth-limit 1)


; Sum and Sum-range  ----------------------------------------------------------

; helpers to compute the work completed by a wtree so far.

; compute sum of numbers up to n.
(define sum ((n natp))
  (b* ((n (nfix n))
       ((if (= n 0)) 0))
      (+ n (sum (1- n)))))

; (sum-range 0 2) -> 3
; (sum-range 1 2) -> 3
; (sum-range 1 3) -> 6
; (sum-range 5 6) -> 11
(define sum-range ((i natp) (j natp))
  :returns (n natp)
  :measure (acl2-count (- (nfix j) (nfix i)))
  (b* ((i (nfix i))
       (j (nfix j))
       ((if (< j i)) 0)
       ((if (equal i j)) i))
      (+ i (sum-range (+ 1 i) j)))
  ///
    (defcong nat-equiv equal (sum-range i j) 1)
    (defcong nat-equiv equal (sum-range i j) 2)
    
    (defrule sum-range-of-add
      (implies
        (and (natp i) (natp j) (natp n) (<= i j) (< j n))
        (equal (+ (sum-range i j) (sum-range (+ j 1) n))
               (sum-range i n))))
    (defrule sum-range-of-sum
      (implies
        (and (natp i) (natp j) (<= i j))
        (equal (sum-range i j) (- (sum j) (sum (1- i)))))
      :enable sum)
    (defrule sum-range-of-one
      (implies (natp j) (equal (sum-range 1 j) (sum j)))
      :enable sum)
    (defrule sum-range-of-zero
      (implies (natp j) (equal (sum-range 0 j) (sum j)))
      :enable sum)
    (defrule sum-range-of-same
      (implies (natp i) (equal (sum-range i i) i))
      :disable (sum-range-of-sum sum-range-of-one sum-range-of-zero))
    (defrule sum-range-of-fold-childless
      (implies (and (natp i) (natp c) (< i c))
               (equal (+ c (sum-range i (+ -1 c))) (sum-range i c)))
      :enable sum
      :disable (sum-range-of-one sum-range-of-zero sum-range))
    (defrule sum-range-fold
      (implies
        (and (natp i) (natp c) (natp r) (< i c) (<= c r))
        (equal (+ (sum-range i (+ -1 c)) (sum-range c r))
               (sum-range i r)))
      :use (:instance sum-range-of-add (i i) (j (+ -1 c)) (n r))
      :disable (sum-range sum-range-of-add)))


; General Utility -------------------------------------------------------------

; TODO: Some of these should move to other files, some of them are
; probably useless.

(defrule erl-vlst-p-of-remove-equal
  (implies (erl-vlst-p l) (erl-vlst-p (remove-equal x l)))
  :enable erl-vlst-p)

(defrule commutuativity-of-remove-equal
  (equal (remove-equal a (remove-equal b l))
         (remove-equal b (remove-equal a l))))

(defrule pid-lst-crock
  (implies
    (and (prefixp (rev l2) (rev l1))
         l2 (erl-vlst-p l2) (pid-lst-p l1))
    (pid-lst-p l2))
  :use (:instance prefix-of-pid-lst-p
        (l1 (rev l1)) (l2 (rev l2)))
  :prep-lemmas
    ((defrule prefix-of-pid-lst-p
       (implies
         (and (pid-lst-p l1) (erl-vlst-p l2) (prefixp l2 l1))
         (pid-lst-p l2))
       :enable prefixp)))

(defrule submap-of-update-new-key
  (implies (and (omap::mapp m) (not (omap::assoc k m)))
           (omap::submap m (omap::update k v m)))
  :enable (omap::submap-to-submap-sk omap::submap-sk
           omap::lookup-of-update))

(defrule assoc-of-head-of-submap-crock
  (implies
    (and (omap::submap a b) (not (omap::emptyp a)))
    (omap::assoc (mv-nth 0 (omap::head a)) b))
  :in-theory (enable* omap::submap))

(defrule member-of-cdr-when-not-car
  (implies (and (member-equal x l) (not (equal x (car l))))
           (member-equal x (cdr l))))

(defrule assoc-of-update-when-assoc
  (implies (omap::assoc q net)
           (iff (omap::assoc x (omap::update q qproc net))
                (omap::assoc x net))))

(defrule assoc-of-update-same
  (omap::assoc k (omap::update k v m))
  :enable omap::assoc-of-update)

(defrule lookup-of-update-of-new
  (implies (not (equal x q))
           (equal (omap::lookup x (omap::update q v m))
                  (omap::lookup x m)))
  :enable omap::lookup-of-update)

(defrule prefixp-of-same
  (prefixp x x)
  :enable prefixp)

; TODO: This should definitely move next to erl-value.lisp
(defrule proc->outbox-of-proc
  (equal (proc->outbox (proc ps s inbox-new inbox-tried klst))
         (erl-state->outbox s))
  :enable proc->outbox)

(defrule len-of-pid-lst-when-consp
  (implies (and (pid-lst-p x) x) (<= 1 (len x)))
  :rule-classes :linear)

(defrule prefixp-of-rev-of-cdr
  (implies (prefixp (rev l) x)
           (prefixp (rev (cdr l)) x))
  :use ((:instance prefixp-transitive-local
          (x (rev (cdr l))) (y (rev l)) (z x)))
  :prep-lemmas
  ((defrule prefixp-of-self-append
    (prefixp x (append x y)) :enable prefixp)
   (defrule prefixp-transitive-local
     (implies (and (prefixp x y) (prefixp y z)) (prefixp x z))
     :enable prefixp)
   (defrule prefixp-of-rev-cdr-rev
     (prefixp (rev (cdr l)) (rev l))
     :expand ((rev l)))))

(defruled no-duplicatesp-of-rev
  (equal (no-duplicatesp-equal (rev l)) (no-duplicatesp-equal l))
  :enable rev
  :prep-lemmas
    ((defrule member-of-rev
       (iff (member-equal e (rev l)) (member-equal e l))
       :enable rev)
     (defrule no-duplicatesp-of-append-singleton
       (equal (no-duplicatesp-equal (append x (list a)))
              (and (no-duplicatesp-equal x) (not (member-equal a x)))))))


; Inbox Utility ---------------------------------------------------------------

; Check if the inbox contains a message {pid, _}
(define inbox-contains ((inbox erl-vlst-p) (pid pid-p))
  :returns (r booleanp)
  :measure (acl2-count (erl-vlst-fix inbox))
  (b* ((inbox (erl-vlst-fix inbox))
       (pid (pid-fix pid))
       ((unless inbox) nil)
       (m (car inbox))
       ((if
         (and
          (equal (erl-val-kind m) :tuple)
          (equal (len (erl-val-tuple->lst m)) 2)
          (equal (car (erl-val-tuple->lst m)) pid)))
         t))
      (inbox-contains (cdr inbox) pid))
  ///
    (defcong erl-vlst-equiv equal (inbox-contains inbox pid) 1)
    (defcong pid-equiv equal (inbox-contains inbox pid) 2)
    
    (defrule inbox-contains-of-append-1
      (implies
        (and (erl-vlst-p a) (erl-vlst-p b)
             (inbox-contains a pid))
        (inbox-contains (append a b) pid)))
    (defrule inbox-contains-of-append-2
      (implies
        (and (erl-vlst-p a) (erl-vlst-p b)
             (inbox-contains b pid))
        (inbox-contains (append a b) pid)))
    
    (defrule not-inbox-contains-of-car
      (implies
        (and
          (not (inbox-contains inbox pid))
          (pid-p pid) (consp inbox)
          (equal (erl-val-kind (car inbox)) :tuple)
          (equal (len (erl-val-tuple->lst (car inbox))) 2))
        (not (equal (car (erl-val-tuple->lst (car inbox))) pid))))

    (defrule not-inbox-contains-of-cdr
      (implies
        (and (not (inbox-contains inbox pid)) (erl-vlst-p inbox))
        (not (inbox-contains (cdr inbox) pid)))
      :enable erl-vlst-p)

    (defrule inbox-contains-of-append-message
      (implies
        (and
          (erl-vlst-p l) (pid-p pid) (erl-val-p m)
          (equal (erl-val-kind m) :tuple)
          (equal (len (erl-val-tuple->lst m)) 2)
          (equal (car (erl-val-tuple->lst m)) pid))
        (inbox-contains (append l (list m)) pid))))

; The negation of inbox-contains
(define inbox-without ((inbox erl-vlst-p) (pid pid-p))
  :returns (r erl-vlst-p)
  :measure (acl2-count (erl-vlst-fix inbox))
  (b* ((inbox (erl-vlst-fix inbox))
       (pid (pid-fix pid))
       ((unless inbox) nil)
       (m (car inbox))
       ((if (and (equal (erl-val-kind m) :tuple)
                 (equal (len (erl-val-tuple->lst m)) 2)
                 (equal (car (erl-val-tuple->lst m)) pid)))
        (erl-vlst-fix (cdr inbox))))
      (cons m (inbox-without (cdr inbox) pid)))
  ///
    (defcong erl-vlst-equiv equal (inbox-without inbox pid) 1)
    (defcong pid-equiv equal (inbox-without inbox pid) 2))

(defrule inbox-contains-of-inbox-without
  (implies
    (and (erl-vlst-p inbox) (pid-p pid) (pid-p x)
         (not (equal pid x))
         (inbox-contains inbox pid))
    (inbox-contains (inbox-without inbox x) pid))
  :enable (inbox-contains inbox-without))

; Retrive the value of a message {pid, value},
; or return the null value.
(define inbox->value ((inbox erl-vlst-p) (pid pid-p))
  :returns (v erl-val-p)
  :measure (acl2-count (erl-vlst-fix inbox))
  (b* ((inbox (erl-vlst-fix inbox))
       (pid (pid-fix pid))
       ((unless inbox) (make-erl-val-none))
       (m (car inbox))
       ((if (and (equal (erl-val-kind m) :tuple)
                 (equal (len (erl-val-tuple->lst m)) 2)
                 (equal (car (erl-val-tuple->lst m)) pid)))
        (erl-val-fix (cadr (erl-val-tuple->lst m)))))
      (inbox->value (cdr inbox) pid))
  ///
    (defcong erl-vlst-equiv equal (inbox->value inbox pid) 1)
    (defcong pid-equiv equal (inbox->value inbox pid) 2))


; Wtree Utility ---------------------------------------------------------------

; Check if the parent of the pid has not yet received the worker's message.
(define parent-still-waiting-p
  ((self pid-p) (parent erl-val-p) (net network-p))
  :returns (r booleanp)
  (b* ((self (pid-fix self))
       (parent (erl-val-fix parent))
       (net (network-fix net))
       ; the root has no parent to wait for it
       ((unless (pid-p parent)) t)
       ((unless (omap::assoc parent net)) nil)
       (pproc (omap::lookup parent net))
       (pbind (erl-state->bind (proc->s pproc)))
       ; the parent cannot terminated until it receives all messages.
       ((if (equal (proc->ps pproc) :terminated)) nil))
      (or (not (omap::assoc 'CPids pbind))
          (not (equal (erl-val-kind (omap::lookup 'CPids pbind)) :cons))
          (consp (member-equal self
                   (erl-val-cons->lst (omap::lookup 'CPids pbind))))))
  ///
    (defcong pid-equiv equal (parent-still-waiting-p a b c) 1)
    (defcong erl-val-equiv equal (parent-still-waiting-p a b c) 2)
    (defcong network-equiv equal (parent-still-waiting-p a b c) 3)
    
    (defrule parent-still-waiting-p-when-not-pid
      (implies
        (not (pid-p (erl-val-fix parent)))
        (parent-still-waiting-p self parent net)))
    
    (defrule parent-still-waiting-p-of-update
      (implies
        (and
          (network-p net) (network-p (omap::update p proc net))
          (omap::assoc p net)
          (equal (erl-state->bind (proc->s proc))
                 (erl-state->bind (proc->s (omap::lookup p net))))
          (or (equal (proc->ps proc) (proc->ps (omap::lookup p net)))
              (equal (proc->ps proc) :receive))
          (parent-still-waiting-p self parent net))
        (parent-still-waiting-p self parent (omap::update p proc net)))
      :enable omap::lookup-of-update))

(defrule parent-still-waiting-p-of-update-of-run
  (implies
    (and
      (network-p net) (network-p (omap::update p proc net))
      (omap::assoc pid net) (omap::assoc p net)
      (not (equal pid p)) (proc-p proc)  
      (erl-val-p
        (omap::lookup 'Parent
          (wtree-bind
            (omap::lookup pid net))))
      (not (equal (proc->ps proc) :terminated))
      (equal
        (omap::lookup 'CPids (erl-state->bind (proc->s proc)))
        (omap::lookup 'CPids
          (erl-state->bind
            (proc->s (omap::lookup p net)))))
      (iff (omap::assoc 'CPids (erl-state->bind (proc->s proc)))
           (omap::assoc 'CPids
             (erl-state->bind (proc->s (omap::lookup p net)))))
      (parent-still-waiting-p pid
        (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
        net))
    (parent-still-waiting-p pid
      (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
      (omap::update p proc net)))
  :enable (parent-still-waiting-p omap::lookup-of-update))

; slighly different to make the rule fire.
(defrule parent-still-waiting-p-of-update-of-run-with-self
  (implies
    (and
      (network-p net) (network-p (omap::update p proc net))
      (proc-p proc) (omap::assoc p net)
      (pid-p self) (erl-val-p parent)
      (or
        (not (equal parent p))
        (and
          (not (equal (proc->ps proc) :terminated))
          (or
            (not (and (omap::assoc 'CPids (erl-state->bind (proc->s proc)))
                      (equal (erl-val-kind
                                (omap::lookup 'CPids
                                  (erl-state->bind (proc->s proc))))
                                :cons)))
            (member-equal self
              (erl-val-cons->lst
                (omap::lookup 'CPids
                  (erl-state->bind (proc->s proc))))))))
      (parent-still-waiting-p self parent net))
    (parent-still-waiting-p self parent (omap::update p proc net)))
  :enable (parent-still-waiting-p omap::lookup-of-update))

(defruled parent-still-waiting-p-of-update-of-receive->receive
  (implies
    (and
      (network-p net) (network-p (omap::update p proc net))
      (proc-p proc) (not (equal pid p))
      (omap::assoc pid net) (omap::assoc p net)
      (erl-val-p (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))))
      (omap::assoc 'CPids (erl-state->bind (proc->s (omap::lookup p net))))
      (equal (erl-val-kind
               (omap::lookup 'CPids
                 (erl-state->bind (proc->s (omap::lookup p net)))))
             :cons)
      (not (equal (proc->ps proc) :terminated))
      (omap::assoc 'CPids (erl-state->bind (proc->s proc)))
      (equal (erl-val-kind
               (omap::lookup 'CPids (erl-state->bind (proc->s proc))))
             :cons)
      (equal (erl-val-cons->lst
               (omap::lookup 'CPids (erl-state->bind (proc->s proc))))
             (cdr (erl-val-cons->lst (omap::lookup 'CPids
                    (erl-state->bind (proc->s (omap::lookup p net)))))))
      (not (equal (proc->ps (omap::lookup pid net)) :terminated))
      (equal (proc->ps
               (omap::lookup
                 (car (erl-val-cons->lst (omap::lookup 'CPids
                        (erl-state->bind (proc->s (omap::lookup p net))))))
                 net))
             :terminated)
      (parent-still-waiting-p pid
        (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
        net))
    (parent-still-waiting-p pid
      (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
      (omap::update p proc net)))
  :enable parent-still-waiting-p
  :use ((:instance parent-still-waiting-p-of-update-of-run-with-self
          (self pid)
          (parent (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))))))

(defruled parent-still-waiting-p-of-update-of-receive->terminate
  (implies
    (and
      (network-p net) (network-p (omap::update p proc net))
      (proc-p proc) (not (equal pid p))
      (omap::assoc pid net) (omap::assoc p net)
      (erl-val-p (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))))
      (omap::assoc 'CPids (erl-state->bind (proc->s (omap::lookup p net))))
      (equal (erl-val-kind
               (omap::lookup 'CPids
                 (erl-state->bind (proc->s (omap::lookup p net)))))
             :cons)
      (null (cdr (erl-val-cons->lst (omap::lookup 'CPids
                   (erl-state->bind (proc->s (omap::lookup p net)))))))
      (not (equal (proc->ps (omap::lookup pid net)) :terminated))
      (equal (proc->ps
               (omap::lookup
                 (car (erl-val-cons->lst (omap::lookup 'CPids
                        (erl-state->bind (proc->s (omap::lookup p net))))))
                 net))
             :terminated)
      (parent-still-waiting-p pid
        (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
        net))
    (parent-still-waiting-p pid
      (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
      (omap::update p proc net)))
  :enable (parent-still-waiting-p omap::lookup-of-update))

(defrule wtree-bindings-of-lookup-of-update-when-bindings-equal
  (implies
    (and
      (network-p net)
      (omap::assoc q net)
      (equal (omap::lookup 'Index (wtree-bind qproc))
             (omap::lookup 'Index (wtree-bind (omap::lookup q net))))
      (equal (omap::lookup 'Parent (wtree-bind qproc))
             (omap::lookup 'Parent (wtree-bind (omap::lookup q net))))
      (equal (omap::lookup 'ChildPids (wtree-bind qproc))
             (omap::lookup 'ChildPids (wtree-bind (omap::lookup q net)))))
    (and
      (equal (omap::lookup 'Index
               (wtree-bind (omap::lookup x (omap::update q qproc net))))
             (omap::lookup 'Index (wtree-bind (omap::lookup x net))))
      (equal (omap::lookup 'Parent
               (wtree-bind (omap::lookup x (omap::update q qproc net))))
             (omap::lookup 'Parent (wtree-bind (omap::lookup x net))))
      (equal (omap::lookup 'ChildPids
               (wtree-bind (omap::lookup x (omap::update q qproc net))))
             (omap::lookup 'ChildPids (wtree-bind (omap::lookup x net))))))
  :enable omap::lookup-of-update)

(defrule leaf-root-p-of-lookup-of-update-when-wtree-bindings-equal
  (implies
    (and
      (network-p net)
      (omap::assoc q net)
      (iff (omap::assoc 'Index (wtree-bind qproc))
           (omap::assoc 'Index (wtree-bind (omap::lookup q net))))
      (iff (omap::assoc 'Parent (wtree-bind qproc))
           (omap::assoc 'Parent (wtree-bind (omap::lookup q net))))
      (iff (omap::assoc 'ChildPids (wtree-bind qproc))
           (omap::assoc 'ChildPids (wtree-bind (omap::lookup q net))))
      (equal (omap::lookup 'Index (wtree-bind qproc))
             (omap::lookup 'Index (wtree-bind (omap::lookup q net))))
      (equal (omap::lookup 'Parent (wtree-bind qproc))
             (omap::lookup 'Parent (wtree-bind (omap::lookup q net))))
      (equal (omap::lookup 'ChildPids (wtree-bind qproc))
             (omap::lookup 'ChildPids (wtree-bind (omap::lookup q net)))))
    (and
      (equal (leaf-p (omap::lookup x (omap::update q qproc net)))
             (leaf-p (omap::lookup x net)))
      (equal (root-p (omap::lookup x (omap::update q qproc net)))
             (root-p (omap::lookup x net)))))
  :enable omap::lookup-of-update
  :use ((:instance leaf-root-p-when-wtree-bindings-equal
          (p1 qproc) (p2 (omap::lookup q net)))))

(defruled check-indices-props
  (implies
    (and (network-p net) (pid-lst-p cps)
         (consp cps) (consp (cdr cps))
         (check-indices i cps net))
    (and (omap::assoc (car cps) net)
         (leaf-p (omap::lookup (car cps) net))
         (equal
          (erl-val-integer->val
            (omap::lookup 'Index
              (wtree-bind (omap::lookup (car cps) net))))
          (+ 1 (nfix i)))
         (omap::assoc (cadr cps) net)
         (leaf-p (omap::lookup (cadr cps) net))
         (or
           (erl-val-cons->lst
                  (omap::lookup 'ChildPids
                    (wtree-bind (omap::lookup (car cps) net))))
           (equal (erl-val-integer->val
                    (omap::lookup 'Index
                      (wtree-bind (omap::lookup (cadr cps) net))))
                  (+ 2 (nfix i))))
         (or
           (not
             (erl-val-cons->lst
              (omap::lookup 'ChildPids
                (wtree-bind (omap::lookup (car cps) net)))))
           (and (rightmost-child (car cps) net)
                (equal (erl-val-integer->val
                         (omap::lookup 'Index
                           (wtree-bind (omap::lookup (cadr cps) net))))
                       (+ 1 (nfix
                              (erl-val-integer->val
                                (omap::lookup 'Index
                                  (wtree-bind
                                    (omap::lookup
                                      (rightmost-child (car cps) net)
                                      net)))))))))))
  :enable check-indices)
