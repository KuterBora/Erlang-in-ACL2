(in-package "ACL2")
(include-book "../top")

; Reduce Example --------------------------------------------------------------

; An example Lin & Snyder style reduce that computes the sum over a list of integers.


; Lin & Snyder style reduce:
; called by the leaves.
; returns the GrandTotal to each leaf.
; reduce({ParentPid, ChildPids}, Value) ->
;   reduce(ParentPid, ChildPids, Value).
;
; reduce(none, [], GrandTotal) -> GrandTotal;
; reduce(ParentPid, [], MyTotal) ->
;   ParentPid ! {self(), reduce_up, MyTotal},
;   receive
;     {ParentPid, reduce_down, GrandTotal} -> GrandTotal
;   end;
; reduce(Parent, [ChildHd | ChildTl], LeftTotal) ->
;   receive
;     {ChildHd, reduce_up, RightTotal} ->
;       GrandTotal =
;         reduce(Parent, ChildTl, LeftTotal + RightTotal),
;       ChildHd ! {self(), reduce_down, GrandTotal},
;       GrandTotal
;   end.
(define sum-reduce-w ()
  :returns (w world-p)
  '((local
      (attrs (module . local) (export) (import))
      (fn-defns
        (((name . init_sum_reduce) (arity . 2))
         ((cases
            (:tuple
              (:cons (:var ParentPid)
                     (:cons (:var ChildPids)
                            (:nil))))
            (:var Value))
          (guards)
          (body
            (:call
              sum_reduce
              (:cons (:var ParentPid)
                     (:cons (:var ChildPids)
                            (:cons (:var Value)
                                   (:nil))))))))
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
                             (:cons (:atom reduce_up)
                                    (:cons (:var MyTotal)
                                           (:nil))))))
            (:receive
              (((cases
                  (:tuple (:cons (:var ParentPid)
                                 (:cons (:atom reduce_down)
                                        (:cons (:var GrandTotal)
                                               (:nil))))))
                (guards)
                (body (:var GrandTotal)))))))

         ((cases (:var Parent) (:var ChildPids) (:var LeftTotal))
          (guards)
          (body
            (:match (:var ChildHd) (:call hd (:cons (:var ChildPids) (:nil))))
            (:match (:var ChildTl) (:call tl (:cons (:var ChildPids) (:nil))))
            (:receive
              (((cases
                  (:tuple (:cons (:var ChildHd)
                                 (:cons (:atom reduce_up)
                                        (:cons (:var RightTotal)
                                               (:nil))))))
                (guards)
                (body
                  (:match
                    (:var GrandTotal)
                    (:call sum_reduce
                      (:cons (:var Parent)
                             (:cons (:var ChildTl)
                                    (:cons (:binop + (:var LeftTotal) (:var RightTotal))
                                           (:nil))))))
                  (:binop !
                    (:var ChildHd)
                    (:tuple (:cons (:call self (:nil))
                                   (:cons (:atom reduce_down)
                                          (:cons (:var GrandTotal)
                                                 (:nil))))))
                  (:var GrandTotal))))))))))))

; Create a process with given id, parent id, child ids, and value.
(define make-reduce-proc ((self pid-p) (parent erl-val-p) (children erl-vlst-p) (value natp))
  :guard-hints (("Goal" :in-theory (enable omap::from-lists)))
  (b* ((self (pid-fix self))
       (parent (erl-val-fix parent))
       (value (nfix value))
       (children (erl-vlst-fix children)))
    (make-proc
      :s
        (make-erl-state
          :bind
            (omap::from-lists
              (list 'ChildPids 'Parent 'Value)
              (list (make-erl-val-cons :lst children) parent (make-erl-val-integer :val value)))
            :self self
            :world (sum-reduce-w))
      :klst
        (list
          (make-erl-k
            :fuel 1000
            :kont
              (make-kont-expr
                :expr
                  (make-node-call
                    :fn 'init_sum_reduce
                    :args
                      (make-node-cons
                        :hd
                          (make-node-tuple
                            :lst 
                              (make-node-cons
                                :hd (make-node-var :id 'Parent)
                                :tl (make-node-cons
                                      :hd (make-node-var :id 'ChildPids)
                                      :tl (make-node-nil))))
                        :tl (make-node-cons
                              :hd (make-node-var :id 'Value)
                              :tl (make-node-nil))))))))))

; example with 4 processes
(defconst *net1*
  (omap::from-lists
    '((:pid 1) (:pid 2) (:pid 3) (:pid 4))
     (list
      (make-reduce-proc '(:pid 1) '(:atom none) (list '(:pid 2) '(:pid 3)) 1)
      (make-reduce-proc '(:pid 2) '(:pid 1) nil 2)
      (make-reduce-proc '(:pid 3) '(:pid 1) (list '(:pid 4)) 3)
      (make-reduce-proc '(:pid 4) '(:pid 3) nil 4))))

; Execute the network and print the results.
#| 
  (b* ((result (erl-runner *net1* 22))
       (- (cw "The final leaf values are: ~%"))
      )
      (list
        (erl-state->in (proc->s (omap::lookup '(:pid 1) result)))
        (erl-state->in (proc->s (omap::lookup '(:pid 2) result)))
        (erl-state->in (proc->s (omap::lookup '(:pid 3) result)))
        (erl-state->in (proc->s (omap::lookup '(:pid 4) result)))))
|#


; Example for any number of processes.
; This still assumes the individual parts of the leafs has been computed,
; and that a worker tree has been created in Erlang, corresponding to the
; result of the following lisp function.

(include-book "arithmetic-3/top" :dir :system)

(define create-wtree ((n natp) (par erl-val-p) (children erl-vlst-p) (self natp) (vlst nat-listp))
  ;returns (net network-p)
  :verify-guards nil
  :measure (nfix n)
  (b* ((n (nfix n))
       (par (erl-val-fix par))
       (children (erl-vlst-fix children))
       (self (nfix self))
       (vlst (nat-list-fix vlst))
       ((unless (nth self vlst)) nil)
       ((if (zp n)) nil)
       ((if (equal n 1))
        (omap::update
          (make-erl-val-pid :id self)
          (make-reduce-proc (make-erl-val-pid :id self) par children (nth self vlst))
          nil))
       (child-net
        (create-wtree
          (ceiling n 2)
          (make-erl-val-pid :id self)
          nil
          (+ self (floor n 2))
          vlst))
       (parent-net
        (create-wtree
          (- n (ceiling n 2))
          par
          (cons (make-erl-val-pid :id (+ self (floor n 2))) children)
          self
          vlst))
       ((unless (omap::compatiblep parent-net child-net)) nil))
      (omap::update* parent-net child-net)))

; Test for 4 processes.
(create-wtree 4 '(:atom none) nil 0 (list 1 2 3 4))

; Reduce network with 10 processes.
(defconst *net2* (create-wtree 10 '(:atom none) nil 0 (list 7 16 2 19 11 6 16 8 3 12)))

; helper to print the leaf values
(local (define print-omap-values ((n network-p))
  :measure (acl2-count (network-fix n))
  (b* ((n (network-fix n))
       ((if (omap::emptyp n)) 'ok)
       (val (erl-state->in (proc->s (omap::head-val n))))
       (- (cw "~x0~%" val)))
    (print-omap-values (omap::tail n)))))

; Execute the network and print the results.
#| 
  (print-omap-values (erl-runner *net2* 64))
|#
