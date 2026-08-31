(in-package "ACL2")
(include-book "wtree")

(local (include-book "arithmetic-3/top" :dir :system))
(set-induction-depth-limit 1)

; TODO: defsection and doc

; Create a Reduce Worker Tree -------------------------------------------------

; Create a worker tree for reduce.
; 
; n: numbder of processes to spawn
; self: current worker node buing built
; index: index of self
; children: children of self, known so far
; pids: existing pids
; net: nodes of wtree built so far
(define create-wtree0
  ((n natp) (self pid-p) (index natp) (parent erl-val-p)
   (children pid-lst-p) (pids pid-set-p) (net network-p))
  :verify-guards nil
  :returns rnet
  :measure (nfix n)
  (b* ((n (nfix n))
       (self (pid-fix self))
       (index (nfix index))
       (parent (erl-val-fix parent))
       (children (pid-lst-fix children))
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
        
      (verify-guards create-wtree0 :hints (("Goal" :in-theory (enable network-p))))
      
      (defcong nat-equiv equal (create-wtree0 a b c d e f g) 1)
      (defcong pid-equiv equal (create-wtree0 a b c d e f g) 2
        :hints (("Goal" :expand ((create-wtree0 a b c d e f g)
                                 (create-wtree0 a b-equiv c d e f g)))))
      (defcong nat-equiv equal (create-wtree0 a b c d e f g) 3
        :hints (("Goal" :in-theory (disable nfix)
                        :expand ((create-wtree0 a b c d e f g)
                                 (create-wtree0 a b c-equiv d e f g)))))
      (defcong erl-val-equiv equal (create-wtree0 a b c d e f g) 4)
      (defcong pid-lst-equiv equal (create-wtree0 a b c d e f g) 5)
      (defcong pid-set-equiv equal (create-wtree0 a b c d e f g) 6
        :hints (("Goal" :expand ((create-wtree0 a b c d e f g)
                                 (create-wtree0 a b c d e f-equiv g)))))
      (defcong network-equiv equal (create-wtree0 a b c d e f g) 7
        :hints (("Goal" :expand ((create-wtree0 a b c d e f g)
                                 (create-wtree0 a b c d e f g-equiv))))))

(define create-wtree ((n natp))
  :returns (rnet network-p)
  :guard-hints (("Goal" :in-theory (enable pid-set-p)))
  (b* ((n (nfix n))
       (self (spawn nil)))
      (create-wtree0 n self 0 '(:atom none) nil (list self) nil))
  ///
    (defcong nat-equiv equal (create-wtree n) 1
      :hints (("Goal"
                :in-theory (disable nfix)
                :expand ((create-wtree n) (create-wtree n-equiv))
                :use (:instance nat-equiv-implies-equal-create-wtree0-1
                      (a n) (b self) (c 0) (d '(:atom none))
                      (e nil) (f (list self)) (g nil)))))
    (defrule create-wtree-of-zero
      (not (create-wtree 0))
      :enable create-wtree0))


; Theorems --------------------------------------------------------------------

(local (set-minimal-arithmetic-theory))

(local (defrule subset-crock
  (implies (set::subset x y) (set::subset x (set::insert a y)))
  :in-theory (enable* set::definitions)))

(local (defrule natp-of-floor-2
  (implies (natp n) (natp (floor n 2)))
  :rule-classes (:rewrite :type-prescription)))

(local (defrule pid-set-p-of-singleton
  (implies (pid-p a) (pid-set-p (list a)))
  :enable pid-set-p))

(local (defrule in-of-singleton
  (set::in a (list a))
  :expand (set::in a (list a))
  :in-theory
    (enable* set::definitions set::head set::tail
             set::setp set::emptyp)))

(defrule non-asssoc-of-create-wtree0-of-pid
  (implies
    (and
      (network-p net) (pid-set-p pids) (natp index)
      (set::in self pids) (not (omap::assoc self net))
      (set::subset (omap::keys net) pids)
      (set::in pid pids)
      (not (equal pid self))
      (not (omap::assoc pid net)))
    (not (omap::assoc pid (create-wtree0 n self index parent children pids net))))
  :enable create-wtree0
  :disable (floor ceiling))

(local (defrule assoc-of-create-wtree0-of-pid
  (implies
    (and
      (network-p net) (pid-set-p pids)
      (set::in self pids) (not (omap::assoc self net))
      (set::subset (omap::keys net) pids)
      (omap::assoc pid net))
    (and (omap::assoc pid (create-wtree0 n self index parent children pids net))
         (equal (omap::lookup pid (create-wtree0 n self index parent children pids net))
                (omap::lookup pid net))))
  :enable (create-wtree0 omap::lookup-of-update)
  :disable (floor ceiling nfix)))

(local (defrule assoc-of-create-wtree0-of-self
  (implies
    (and
      (network-p net) (pid-set-p pids) (natp index)
      (set::in self pids) (not (omap::assoc self net))
      (set::subset (omap::keys net) pids)
      (natp n) (> n 0) (pid-p self))
    (omap::assoc self (create-wtree0 n self index parent children pids net)))
  :enable create-wtree0
  :disable (floor ceiling)))

(local (defrule assoc-bind-of-create-wtree0-of-self
  (implies
    (and
      (network-p net) (pid-set-p pids) (natp index)
      (set::in self pids) (not (omap::assoc self net))
      (set::subset (omap::keys net) pids)
      (natp n) (> n 0) (pid-p self))
    (and
      (omap::assoc 'Index
        (erl-state->bind
          (proc->s
            (omap::lookup self
              (create-wtree0 n self index parent children pids net)))))
      (omap::assoc 'Parent
        (erl-state->bind
          (proc->s
            (omap::lookup self
              (create-wtree0 n self index parent children pids net)))))
      (omap::assoc 'ChildPids
        (erl-state->bind
          (proc->s
            (omap::lookup self
              (create-wtree0 n self index parent children pids net)))))))
  :enable create-wtree0
  :disable (floor ceiling)))

(local (defrule lookup-of-bind-of-create-wtree0-of-self
  (implies
    (and
      (network-p net) (pid-set-p pids) (natp index)
      (set::in self pids) (not (omap::assoc self net))
      (set::subset (omap::keys net) pids)
      (natp n) (> n 0) (pid-p self) (erl-val-p parent))
    (and
      (equal
        (omap::lookup 'Index
          (erl-state->bind
            (proc->s
              (omap::lookup self
                (create-wtree0 n self index parent children pids net)))))
        (make-erl-val-integer :val index))
      (equal
        (omap::lookup 'Parent
          (erl-state->bind
            (proc->s
              (omap::lookup self
                (create-wtree0 n self index parent children pids net)))))
        parent)
      (equal
        (erl-val-kind
          (omap::lookup 'ChildPids
            (erl-state->bind
              (proc->s
                (omap::lookup self
                  (create-wtree0 n self index parent children pids net))))))
        :cons)
      (pid-lst-p
        (erl-val-cons->lst
          (omap::lookup 'ChildPids
            (erl-state->bind
              (proc->s
                (omap::lookup self
                  (create-wtree0 n self index parent children pids net)))))))))
  :enable create-wtree0
  :disable (floor ceiling)))

(local (defrule last-child-of-create-wtree0-of-self
  (implies
    (and
      (network-p net) (pid-set-p pids)
      (set::in self pids) (not (omap::assoc self net))
      (set::subset (omap::keys net) pids)
      (pid-lst-p chl) (consp chl)
      (natp index) (natp n) (> n 0))
    (equal
      (last (erl-val-cons->lst
              (omap::lookup 'ChildPids
                (erl-state->bind
                  (proc->s
                    (omap::lookup self
                      (create-wtree0 n self index parent chl pids net)))))))
      (last chl)))
  :enable create-wtree0
  :disable (floor ceiling)))

(local (defrule member-equal-of-children-of-create-wtree0
  (implies
    (and
      (network-p net) (pid-set-p pids)
      (set::in self pids) (not (omap::assoc self net))
      (set::subset (omap::keys net) pids)
      (natp index) (pid-lst-p chl) (natp n) (> n 0)
      (member-equal pid chl))
    (member-equal pid
      (erl-val-cons->lst
        (omap::lookup 'ChildPids
          (erl-state->bind
            (proc->s
              (omap::lookup self
                (create-wtree0 n self index parent chl pids net))))))))
  :enable (create-wtree0 omap::lookup-of-update)
  :disable (floor ceiling)))


; Size of Create Wtree --------------------------------------------------------

(defrule size-of-create-wtree0
  (implies
    (and (network-p net) (pid-set-p pids) (natp index) (natp n)
        (set::subset (omap::keys net) pids) (set::in self pids)
        (not (omap::assoc self net)))
    (equal (omap::size (create-wtree0 n self index parent children pids net))
           (+ n (omap::size net))))
  :enable (create-wtree0 omap::size-to-cardinality-of-keys set::insert-cardinality)
  :disable (floor ceiling))

(defrule size-of-create-wtree
      (implies (natp n) (equal (omap::size (create-wtree n)) n))
      :in-theory (enable* create-wtree pid-set-p set::emptyp
                          set::head set::definitions))

; Nodes of Create Wtree are Root or Leaf --------------------------------------

(local (defrule root-p-of-create-wtree0
  (implies
    (and
      (network-p net) (pid-set-p pids)
      (set::in self pids) (not (omap::assoc self net))
      (set::subset (omap::keys net) pids)
      (natp n) (> n 0) (pid-p self))
    (root-p (omap::lookup self (create-wtree0 n self 0 '(:atom none) children pids net))))
  :enable (root-p omap::lookup-of-update)
  :disable (floor ceiling assoc-of-create-wtree0-of-self
            assoc-bind-of-create-wtree0-of-self)
  :use ((:instance assoc-of-create-wtree0-of-self (index 0) (parent '(:atom none)))
        (:instance assoc-bind-of-create-wtree0-of-self (index 0) (parent '(:atom none))))))

; TODO: this takes a lot of steps.
(local (defrule leaf-p-of-create-wtree0
  (implies
    (and
      (network-p net) (pid-set-p pids) (pid-p self)
      (set::in self pids) (not (omap::assoc self net))
      (set::subset (omap::keys net) pids)
      (natp n) (> n 0) (pid-p pid) (natp index)
      (or (and (> index 0) (pid-p parent))
          (and (equal index 0) (equal parent '(:atom none))
               (not (equal pid self))))
      (not (omap::assoc pid net))
      (omap::assoc pid (create-wtree0 n self index parent children pids net)))
    (leaf-p (omap::lookup pid (create-wtree0 n self index parent children pids net))))
  :enable create-wtree0
  :disable (floor ceiling not |(< x (if a b c))|
            ceiling-to-floor natp omap::assoc-of-update)
  :hints (("Subgoal *1/4" :in-theory (enable omap::assoc-of-update)))))

(defrule root-p-of-create-wtree
  (implies (and  (natp n) (> n 0))
           (and (omap::assoc (spawn nil) (create-wtree n))
                (root-p (omap::lookup (spawn nil) (create-wtree n)))))
  :enable create-wtree
  :disable natp)

(defrule leaf-p-of-create-wtree
  (implies
    (and
      (natp n) (> n 0) (pid-p pid)
      (not (equal pid (spawn nil)))
      (omap::assoc pid (create-wtree n)))
    (leaf-p (omap::lookup pid (create-wtree n))))
  :enable create-wtree)

(defrule root-or-leaf-of-create-wtree
  (implies
    (and (natp n) (pid-p pid) (omap::assoc pid (create-wtree n)))
    (or (root-p (omap::lookup pid (create-wtree n)))
        (leaf-p (omap::lookup pid (create-wtree n)))))
  :cases ((equal pid (spawn nil)))
  :use ((:instance leaf-p-of-create-wtree)
        (:instance root-p-of-create-wtree)))

(defrule leaf-p-of-create-wtree-when-not-root
  (implies
    (and (natp n) (pid-p pid) (omap::assoc pid (create-wtree n))
         (not (root-p (omap::lookup pid (create-wtree n)))))
    (leaf-p (omap::lookup pid (create-wtree n))))
  :use root-or-leaf-of-create-wtree
  :disable root-or-leaf-of-create-wtree)

(defrule head-key-of-root
  (implies
    (and (natp n) (> n 0) (network-p net) (not (omap::emptyp net))
         (omap::submap net (create-wtree n))
         (root-p (omap::lookup (omap::head-key net) (create-wtree n))))
    (equal (omap::head-key net) (spawn nil)))
  :use ((:instance leaf-p-of-create-wtree (pid (omap::head-key net)))
        (:instance root-and-leaf-disjoint
          (proc (omap::lookup (omap::head-key net) (create-wtree n)))))
  :disable (leaf-p-of-create-wtree root-and-leaf-disjoint))

; Check Children of Create Wtree ----------------------------------------------

(defrule check-children-of-create-wtree
  (implies
    (and
      (natp n) (> n 0) (omap::assoc pid (create-wtree n)))
    (check-children pid
      (erl-val-cons->lst
        (omap::lookup 'ChildPids
          (erl-state->bind (proc->s (omap::lookup pid (create-wtree n))))))
      (create-wtree n)))
  :enable create-wtree
  :prep-lemmas
    ((defrule check-children-of-create-wtree0-of-update
       (implies
         (and
           (network-p net) (pid-set-p pids)
           (set::in self pids) (not (omap::assoc self net))
           (set::subset (omap::keys net) pids)
           (check-children i chl net))
         (check-children i chl
           (create-wtree0 n self index parent children pids net)))
       :enable check-children)
     (defrule lookup-of-check-children-of-create-wtree0
       (implies
         (and
           (network-p net) (pid-set-p pids)
           (set::in self pids) (not (omap::assoc self net))
           (set::subset (omap::keys net) pids)
           (pid-lst-p children) (check-children self children net)
           (not (omap::assoc pid net)) (pid-p pid)
           (omap::assoc pid (create-wtree0 n self index parent children pids net)))
         (check-children pid
           (erl-val-cons->lst
             (omap::lookup 'ChildPids
               (erl-state->bind (proc->s (omap::lookup pid
                 (create-wtree0 n self index parent children pids net))))))
           (create-wtree0 n self index parent children pids net)))
       :enable create-wtree0
       :disable (floor ceiling floor-zero floor-positive erl-val-fix-when-erl-val-p nfix
                 omap::assoc-when-assoc-tail set::insert-identity set::in-tail
                 assoc-of-runnable? set::union-insert-x omap::tail-when-emptyp
                 lookup-of-tail-when-assoc-tail-of-network))))


; Check Parent of Create Wtree ------------------------------------------------

(defrule check-parent-of-create-wtree
  (implies
    (and
      (natp n) (> n 0)
      (omap::assoc pid (create-wtree n)))
    (check-parent pid
      (omap::lookup 'Parent
        (erl-state->bind (proc->s (omap::lookup pid (create-wtree n)))))
      (create-wtree n)))
  :enable create-wtree
  :disable check-parent-of-create-wtree0-of-lookup
  :use (:instance check-parent-of-create-wtree0-of-lookup
        (self (spawn nil)) (net nil) (parent '(:atom none))
        (index 0) (children nil) (pids (list (spawn nil))))
  :cases ((equal pid (spawn nil)))
  :prep-lemmas
    ((defrule check-parent-of-create-wtree0-extension
       (implies
         (and
           (network-p net) (pid-set-p pids)
           (set::in self pids) (not (omap::assoc self net))
           (set::subset (omap::keys net) pids)
           (check-parent pid par net))
         (check-parent pid par (create-wtree0 n self index parent chl pids net)))
       :enable check-parent)

     (defrule check-parent-of-create-wtree0
       (implies
         (and
           (network-p net) (pid-set-p pids)
           (set::in self pids) (not (omap::assoc self net))
           (set::subset (omap::keys net) pids)
           (pid-lst-p chl) (natp index)
           (or (and (> index 0) (pid-p parent))
               (and (equal index 0) (equal parent '(:atom none))))
           (natp n) (> n 0)
           (omap::assoc cpid net))
         (check-parent cpid self
           (create-wtree0 n self index parent (cons cpid chl) pids net)))
       :enable check-parent)

     ; TODO: This takes too many steps.
     (defrule check-parent-of-create-wtree0-of-lookup
       (implies
         (and
           (network-p net) (pid-set-p pids)
           (set::in self pids) (not (omap::assoc self net))
           (set::subset (omap::keys net) pids)
           (pid-lst-p children) (natp index)
           (or (and (> index 0) (pid-p parent) (not (equal pid self)))
               (and (equal index 0) (equal parent '(:atom none))))
           (natp n) (> n 0)
           (omap::assoc pid (create-wtree0 n self index parent children pids net))
           (not (omap::assoc pid net)))
         (check-parent pid
           (omap::lookup 'Parent
             (erl-state->bind
               (proc->s
                 (omap::lookup pid
                   (create-wtree0 n self index parent children pids net)))))
           (create-wtree0 n self index parent children pids net)))
       :enable (create-wtree0)
       :disable
         (floor ceiling floor-zero  omap::assoc-when-emptyp |(< x (if a b c))|
          omap::assoc-when-assoc-tail))))



; Rightmost Child of Wtree ----------------------------------------------------

(local (defrule rightmost-child0-of-create-wtree0-extension
  (implies
    (and
      (network-p net) (pid-set-p pids)
      (set::in self pids) (not (omap::assoc self net))
      (set::subset (omap::keys net) pids)
      (rightmost-child0 i net fuel))
    (equal
      (rightmost-child0 i
        (create-wtree0 n self index parent chl pids net) fuel)
      (rightmost-child0 i net fuel)))
  :enable rightmost-child0))

(local (defrule rightmost-child0-of-create-wtree0-step
  (implies
    (and
      (network-p net) (pid-set-p pids) (pid-p self)
      (set::in self pids) (not (omap::assoc self net))
      (set::subset (omap::keys net) pids)
      (natp n) (> n 0) (natp fuel) (> fuel 0)
      (natp index)
      (or (and (> index 0) (pid-p parent))
          (and (equal index 0) (equal parent '(:atom none))))
      (pid-lst-p chl) (consp chl)
      (pid-p (car (last chl)))
      (omap::assoc (car (last chl)) net) 
      (leaf-p (omap::lookup (car (last chl)) net)))
    (equal (rightmost-child0 self
             (create-wtree0 n self index parent chl pids net) fuel)
           (rightmost-child0 (car (last chl))
             (create-wtree0 n self index parent chl pids net) (- fuel 1))))
  :enable omap::lookup-of-update
  :disable (floor ceiling)
  :expand ((rightmost-child0 self
             (create-wtree0 n self index parent chl pids net) fuel)
           (rightmost-child0 self
             (create-wtree0 n self 0 '(:atom none) chl pids net) fuel))
  :prep-lemmas
    ((defrule childpids-of-create-wtree0-of-self-non-nil
       (implies
         (and
          (network-p net) (pid-set-p pids) (natp index)
          (pid-lst-p chl) (consp chl)
          (set::subset (omap::keys net) pids)
          (set::in self pids) (not (omap::assoc self net))
          (natp n) (> n 0))
         (erl-val-cons->lst
           (omap::lookup 'ChildPids
             (erl-state->bind (proc->s (omap::lookup self
               (create-wtree0 n self index parent chl pids net)))))))
       :use last-child-of-create-wtree0-of-self
       :disable last-child-of-create-wtree0-of-self
       :enable last))))

(local (defrule rightmost-child0-of-create-wtree0
  (implies
    (and (network-p net) (pid-set-p pids) (pid-p self)
         (natp index)
         (or (and (> index 0) (pid-p parent))
             (and (equal index 0) (equal parent '(:atom none))))
         (set::subset (omap::keys net) pids)
         (set::in self pids) (not (omap::assoc self net))
         (natp n) (> n 0) (natp fuel) (<= n fuel))
    (and (rightmost-child0 self
           (create-wtree0 n self index parent nil pids net) fuel)
         (equal (erl-val-integer->val
                  (omap::lookup 'Index
                    (erl-state->bind (proc->s
                      (omap::lookup
                        (rightmost-child0 self
                          (create-wtree0 n self index parent nil pids net) fuel)
                        (create-wtree0 n self index parent nil pids net))))))
                (+ index n -1))))
  :induct (rightmost-wtree-induct n self index parent pids net fuel)
  :enable (omap::lookup-of-update rightmost-child0)
  :disable (floor ceiling)
  :expand ((:free (x y z) (create-wtree0 x self y z nil pids net)))
  :prep-lemmas
    ((define rightmost-wtree-induct (m self index parent pids net fuel)
      :enabled t
      :irrelevant-formals-ok t
      :verify-guards nil
      :measure (nfix m)
      (b* (((if (zp m)) (list parent fuel))
           ((if (not (set::in self pids))) (list parent fuel))
           ((if (omap::assoc self net)) (list parent fuel))
           ((if (equal m 1)) (list parent fuel))
           (cpid (spawn pids)))
          (rightmost-wtree-induct (ceiling m 2) cpid (+ index (floor m 2)) self
                                  (set::insert cpid pids) net (- fuel 1)))
      :hints (("Goal" :in-theory (disable floor ceiling)))))))

(defrule rightmost-child-of-create-wtree
  (implies
    (and (natp n) (> n 0))
    (and (rightmost-child (spawn nil) (create-wtree n))
         (equal (erl-val-integer->val
                  (omap::lookup 'Index
                    (erl-state->bind (proc->s
                      (omap::lookup
                        (rightmost-child (spawn nil) (create-wtree n))
                        (create-wtree n))))))
                (- n 1))))
  :enable (create-wtree rightmost-child))

; I will have to prove the same theorems for the wrapper function.
(local (defrule rightmost-child-of-create-wtree0-extension
  (implies
    (and
      (network-p net) (pid-set-p pids)
      (set::subset (omap::keys net) pids)
      (set::in self pids) (not (omap::assoc self net))
      (natp index) (natp n) (rightmost-child i net))
    (equal (rightmost-child i (create-wtree0 n self index parent chl pids net))
           (rightmost-child i net)))
  :enable rightmost-child
  :use ((:instance increase-fuel-of-rightmost-child0
          (pid i) (f1 (omap::size net))
          (f2 (omap::size (create-wtree0 n self index parent chl pids net)))))))

(local (defrule rightmost-child-of-create-wtree0-step
  (implies
    (and (network-p net) (pid-set-p pids)
         (set::subset (omap::keys net) pids)
         (set::in self pids) (not (omap::assoc self net))
         (natp n) (> n 0) (natp index)
         (or (and (> index 0) (pid-p parent))
             (and (equal index 0) (equal parent '(:atom none)))))
    (and (rightmost-child self (create-wtree0 n self index parent nil pids net))
         (equal (erl-val-integer->val
                  (omap::lookup 'Index
                    (erl-state->bind
                      (proc->s
                        (omap::lookup
                          (rightmost-child self
                            (create-wtree0 n self index parent nil pids net))
                          (create-wtree0 n self index parent nil pids net))))))
                (+ index n -1))))
  :enable rightmost-child
  :use ((:instance rightmost-child0-of-create-wtree0
          (fuel (omap::size (create-wtree0 n self index parent nil pids net)))))))


; Check Indices of Create Wtree -----------------------------------------------

(local (defrule check-indices-of-create-wtree0-extension
  (implies
    (and (network-p net) (pid-set-p pids)
         (natp index) (natp n)
         (set::subset (omap::keys net) pids)
         (set::in self pids) (not (omap::assoc self net))
         (check-indices i chl net) (pid-lst-p chl))
    (check-indices i chl (create-wtree0 n self index parent cwchl pids net)))
  :enable check-indices))

; TODO: this takes a lot of steps.
(local (defrule check-indices-of-create-wtree0-of-lookup
  (implies
    (and (network-p net) (pid-set-p pids) (pid-p self) (pid-p pid)
         (natp index) (pid-lst-p children)
         (set::subset (omap::keys net) pids)
         (set::in self pids) (not (omap::assoc self net))
         (natp n) (> n 0)
         (check-indices (+ index n -1) children net)
         (omap::assoc pid (create-wtree0 n self index parent children pids net))
         (not (omap::assoc pid net)))
    (check-indices
      (erl-val-integer->val
        (omap::lookup 'Index
          (erl-state->bind
            (proc->s
              (omap::lookup pid
                (create-wtree0 n self index parent children pids net))))))
      (erl-val-cons->lst
        (omap::lookup 'ChildPids
          (erl-state->bind
            (proc->s
              (omap::lookup pid
                (create-wtree0 n self index parent children pids net))))))
      (create-wtree0 n self index parent children pids net)))
  :enable (create-wtree0 omap::lookup-of-update)
  :disable (floor ceiling not |(< (if a b c) x)| |(< x (if a b c))|)
  :prep-lemmas
    ((set-default-arithmetic-theory))))

(defrule check-indices-of-create-wtree
  (implies
    (and (natp n) (> n 0) (pid-p pid) (omap::assoc pid (create-wtree n)))
    (check-indices
      (erl-val-integer->val
        (omap::lookup 'Index
          (erl-state->bind (proc->s (omap::lookup pid (create-wtree n))))))
      (erl-val-cons->lst
        (omap::lookup 'ChildPids
          (erl-state->bind (proc->s (omap::lookup pid (create-wtree n))))))
      (create-wtree n)))
  :enable create-wtree)


; Create-Wtree is Wtree-p -----------------------------------------------------

(defrule wtree0-p-of-create-wtree
  (implies
    (and (natp n) (> n 0) (network-p net) (not (omap::emptyp net))
         (omap::submap net (create-wtree n)))
    (wtree0-p net (create-wtree n) n))
  :enable wtree0-p
  :disable (natp omap::head-key omap::head-val
            parent-of-root index-of-root erl-val-kind-of-root
            parent-of-leaf index-of-leaf erl-val-kind-of-leaf)
  :prep-lemmas
    ((defrule assoc-of-head-key-of-submap
       (implies (and (omap::submap a b) (not (omap::emptyp a)))
                (omap::assoc (omap::head-key a) b)))

     (defrule head-val-of-submap
       (implies (and (omap::submap a b) (not (omap::emptyp a)))
                (equal (omap::head-val a)
                       (omap::lookup (omap::head-key a) b)))
       :in-theory (enable omap::lookup omap::submap
                          omap::head-key omap::head-val))))

(defrule wtree-p-of-create-wtree
  (implies (natp n) (wtree-p (create-wtree n)))
  :enable wtree-p
  :disable natp
  :cases ((create-wtree n))
  :use ((:instance wtree0-p-of-create-wtree
          (net (create-wtree n)))))