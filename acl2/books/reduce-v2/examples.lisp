; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "wtree/create-wtree/top")

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
                                    (:nil)))))
            (:var MyTotal)))
         ((cases (:var ParentPid) (:var CPids) (:var LeftTotal))
          (guards)
          (body
            (:match (:var ChildHd) (:call hd (:cons (:var CPids) (:nil))))
            (:match (:var ChildTl) (:call tl (:cons (:var CPids) (:nil))))
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

(define make-reduce-proc ((self pid-p) (parent erl-val-p) (children pid-lst-p) (index natp))
  :returns (proc proc-p)
  :guard-hints (("Goal" :in-theory (enable omap::from-lists)))
  (b* ((self (pid-fix self))
       (parent (erl-val-fix parent))
       (index (nfix index))
       (children (pid-lst-fix children)))
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
                    :fuel (+ 100 (* 100 (len children)))
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
    (defcong pid-equiv equal (make-reduce-proc s p c i) 1)
    (defcong erl-val-equiv equal (make-reduce-proc s p c i) 2)
    (defcong pid-lst-equiv equal (make-reduce-proc s p c i) 3)
    (defcong nat-equiv equal (make-reduce-proc s p c i) 4)

; helper to print the leaf values.
(local (define print-omap-values ((n network-p))
  :measure (acl2-count (network-fix n))
  (b* ((n (network-fix n))
       ((if (omap::emptyp n)) 'ok)
       (val (erl-state->in (proc->s (omap::head-val n))))
       (- (cw "~x0~%" val)))
    (print-omap-values (omap::tail n)))))


; Reduce network with 10 processes.
; Run the processes for 40 steps and print the results.
; Remark: index starts at 0, so this one is a sum until n-1
#| 
  (print-omap-values (erl-runner (create-wtree 10) 40))
|#


; Reduce network with 100 processes.
; Run the processes for 400 steps and print the results.
; Remark: index starts at 0, so this one is a sum until n-1
#| 
  (print-omap-values (erl-runner (create-wtree 100) 400))
|#

; Reduce network with 1000 processes.
; Run the processes for 4000 steps and print the results.
; Remarks:
; - index starts at 0, so this one is a sum until n-1
; - there are a lot of processes, so it is better to
;   just print the head.
#|
  (erl-state->in
    (proc->s
        (omap::head-val
            (erl-runner (create-wtree 1000) 4000))))
|#