(in-package "ACL2")
(include-book "../../scheduler/top")

(set-induction-depth-limit 1)

; TODO doc and defsection

; TODO: the world should not be limited to the following functions. It should
; instead just state that there is a module in the world that contains the
; functions. However, this simplifies the proofs slightly for now.

#| 
  reduce(none, [], GrandTotal) -> GrandTotal;
  reduce(ParentPid, [], MyTotal) ->
    ParentPid ! {self(), reduce_up, MyTotal};
  reduce(ParentPid, CPids, LeftTotal) ->
    ChildHd = hd(CPids);
    ChildTl = tl(Cpids);
    receive
      {ChildHd, reduce_up, RightTotal} ->
        reduce(Parent, ChildTl, LeftTotal + RightTotal)
    end.
|#
(define sum-reduce-w ()
  :returns (w world-p)
  '((local
      (attrs (module . local) (export) (import))
      (fn-defns
        (((name . sum_reduce) (arity . 3))
         ((cases (:atom none) (:nil) (:var GrandTotal))
          (guards)
          (body (:var GrandTotal)))
         ((cases (:var ParentPid) (:nil) (:var MyTotal))
          (guards)
          (body
            (:binop !
              (:var ParentPid)
              (:tuple (:cons (:call self (:nil))
                             (:cons (:var MyTotal)
                                    (:nil)))))))
         ((cases (:var ParentPid) (:var Children) (:var LeftTotal))
          (guards)
          (body
            (:match (:var ChildHd) (:call hd (:cons (:var Children) (:nil))))
            (:match (:var ChildTl) (:call tl (:cons (:var Children) (:nil))))
            (:receive
              (((cases
                  (:tuple (:cons (:var ChildHd)
                                 (:cons (:var RightTotal)
                                        (:nil)))))
                (guards)
                (body
                  (:call sum_reduce
                    (:cons (:var ParentPid)
                           (:cons (:var ChildTl)
                                  (:cons (:binop + (:var LeftTotal) (:var RightTotal))
                                         (:nil))))))))))))))))

; Create a process with given id, parent id, child ids, and index, that is calling reduce.
(define make-reduce-proc ((self pid-p) (parent erl-val-p) (children erl-vlst-p) (index natp))
  :returns (proc proc-p)
  :guard-hints (("Goal" :in-theory (enable omap::from-lists)))
  (b* ((self (pid-fix self))
       (parent (erl-val-fix parent))
       (index (nfix index))
       (children (erl-vlst-fix children)))
    (make-proc
      :s
        (make-erl-state
          :bind
            (omap::from-lists
              (list 'ChildPids 'Parent 'Index)
              (list (make-erl-val-cons :lst children) parent (make-erl-val-integer :val index)))
            :self self
            :world (sum-reduce-w))
      :klst (list (make-erl-k
                    :fuel 1000
                    :kont (make-kont-expr
                            :expr (make-node-call
                                    :fn 'sum_reduce
                                    :args (make-node-cons
                                            :hd (make-node-var :id 'Parent)
                                            :tl (make-node-cons
                                                  :hd (make-node-var :id 'ChildPids)
                                                  :tl (make-node-cons
                                                        :hd (make-node-var :id 'Index)
                                                        :tl (make-node-nil))))))))))
  ///
    (defcong pid-equiv equal (make-reduce-proc s p c i) 1)
    (defcong erl-val-equiv equal (make-reduce-proc s p c i) 2)
    (defcong erl-vlst-equiv equal (make-reduce-proc s p c i) 3)
    (defcong nat-equiv equal (make-reduce-proc s p c i) 4)

    (defrule network-p-of-update-with-make-reduce-proc
      (implies
        (and (network-p net) (pid-p pid))
        (network-p (omap::update pid (make-reduce-proc pid par chl val) net)))
      :e/d ((proc->pid) (network-p-of-update))
      :use (:instance network-p-of-update
              (net net) (pid pid) (p (make-reduce-proc pid par chl val))))

    (defrule assoc-of-make-reduce
      (and
        (omap::assoc 'Index
          (erl-state->bind (proc->s (make-reduce-proc self parent children index))))
        (omap::assoc 'Parent
          (erl-state->bind (proc->s (make-reduce-proc self parent children index))))
        (omap::assoc 'ChildPids
          (erl-state->bind (proc->s (make-reduce-proc self parent children index)))))
      :enable (omap::from-lists omap::lookup-of-update))

    (defrule index-of-make-reduce-proc
      (equal (omap::lookup 'Index
               (erl-state->bind (proc->s (make-reduce-proc self parent children index))))
             (make-erl-val-integer :val (nfix index)))
      :enable (omap::from-lists omap::lookup-of-update))

    (defrule parent-of-make-reduce-proc
      (equal (omap::lookup 'Parent
               (erl-state->bind (proc->s (make-reduce-proc self parent children index))))
             (erl-val-fix parent))
      :enable (omap::from-lists omap::lookup-of-update))

    (defrule childpids-of-make-reduce-proc
      (equal (omap::lookup 'ChildPids
               (erl-state->bind (proc->s (make-reduce-proc self parent children index))))
             (make-erl-val-cons :lst (erl-vlst-fix children)))
      :enable (omap::from-lists omap::lookup-of-update)))