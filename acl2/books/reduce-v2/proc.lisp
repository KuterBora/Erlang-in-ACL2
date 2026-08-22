(in-package "ACL2")
(include-book "../../top")

(set-induction-depth-limit 1)

; BOZO: the world should not be limited to the following functions. It should
; instead just state that there is a module in the world that contains the
; functions. However, this simplifies the proofs slightly for now.

#| 
  reduce(none, [], GrandTotal) -> GrandTotal;
  reduce(ParentPid, [], MyTotal) ->
    ParentPid ! {self(), reduce_up, MyTotal};
  reduce(Parent, [ChildHd | ChildTl], LeftTotal) ->
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
                                                        :tl (make-node-nil)))))))))))