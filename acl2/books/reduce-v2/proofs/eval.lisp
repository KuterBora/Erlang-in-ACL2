(in-package "ACL2")
(include-book "inv")
(include-book "../../../theorems/top")

; Apply-K Lemmas for INV ---------------------------------------------------------

(local (defrule erl-val-kind-of-car-of-pid-lst
  (implies
    (and (pid-lst-p x) (consp x))
    (and (erl-val-p (car x))
         (equal (erl-val-kind (car x)) :pid)))
  :enable pid-p))

(local (defrule len-of-pid-lst-when-consp
  (implies (and (pid-lst-p x) x) (<= 1 (len x)))
  :rule-classes :linear))

; idle -> receive
(defrule apply-k-of-idle-with-children
  (implies
    (and
      (equal s (proc->s (make-reduce-proc self parent children index)))
      (equal klst (proc->klst (make-reduce-proc self parent children index)))
      (natp index) (pid-lst-p children) children
      (or (pid-p parent) (equal parent (make-erl-val-atom :val 'none))))
    (b* ((ns (apply-k s klst))
         (bind (erl-state->bind ns)))
      (and
        ; it ran to a receive
        (equal (erl-val-kind (erl-state->in ns)) :receive)
        (erl-klst-p (erl-val-receive->klst (erl-state->in ns)))
        ; the reduce loop's bindings exist
        (omap::assoc 'ParentPid bind)
        (omap::assoc 'CPids bind)
        (omap::assoc 'ChildHd bind)
        (omap::assoc 'ChildTl bind)
        (omap::assoc 'LeftTotal bind)
        (not (omap::assoc 'RightTotal bind))
        (equal (omap::lookup 'ParentPid bind) parent)
        (equal (omap::lookup 'CPids bind) (make-erl-val-cons :lst children))
        (equal (omap::lookup 'ChildHd bind) (car children))
        (equal (omap::lookup 'ChildTl bind)
               (make-erl-val-cons :lst (cdr children)))
        (equal (omap::lookup 'LeftTotal bind)
               (make-erl-val-integer :val index))
        ; no messages sent 
        (equal (erl-state->outbox ns) nil)
        (equal (erl-state->self ns) (erl-state->self s))
        (equal (erl-state->world ns) (sum-reduce-w))
        (equal (erl-state->module ns) 'local)
        ; klst is correct
        (reduce-receive-klst-p
          (erl-val-receive->klst (erl-state->in ns))
          (erl-state->bind s))
        ; enough fuel is left
        (equal (erl-k->fuel (car (erl-val-receive->klst (erl-state->in ns))))
               (+ 95 (* 100 (len children)))))))
  :enable (reduce-receive-klst-p omap::from-lists match-args eval-match
           wf-state-p pid-p make-reduce-proc eval-clauses-when-consp
           apply-k-of-local-call-when-match eval-local-call eval-clauses
           apply-k-of-local-call-no-match eval-guard-seq eval-guard eval-bif
           eval-guard-seq eval-guard-seq-when-consp eval-guard-expr
           apply-k-of-cons apply-k-of-binop-expr1))

; idle -> terminated
(defrule apply-k-of-idle-no-children
  (implies
    (and
      (equal s (proc->s (make-reduce-proc self parent nil index)))
      (equal klst (proc->klst (make-reduce-proc self parent nil index)))
      (pid-p self) (natp index)
      (or (pid-p parent) (equal parent (make-erl-val-atom :val 'none))))
    (b* ((ns (apply-k s klst)))
      (and
        (not (equal (erl-val-kind (erl-state->in ns)) :receive))
        (equal (erl-state->in ns) (make-erl-val-integer :val index))
        (equal (erl-state->bind ns) (erl-state->bind s))
        (equal (erl-state->self ns) (erl-state->self s))
        (equal (erl-state->world ns) (sum-reduce-w))
        (equal (erl-state->module ns) 'local)
        (equal
          (erl-state->outbox ns)
          (if (pid-p parent)
              (omap::update parent
                (list (make-erl-val-tuple
                        :lst (list self (make-erl-val-integer :val index))))
                nil)
            nil)))))
  :enable (wf-state-p pid-p make-reduce-proc omap::from-lists
           apply-k-of-local-call-when-match apply-k-of-local-call-no-match
           apply-k-of-cons apply-k-of-binop-expr1 eval-guard-expr eval-bif
           eval-local-call eval-clauses eval-clauses-when-consp eval-guard
           match-args eval-match eval-guard-seq eval-guard-seq-when-consp
           omap::lookup-of-update))

; Expand eval receive

(local (defrule not-cddr-of-tuple-lst-of-len-2
  (implies (equal (len (erl-val-tuple->lst m)) 2)
          (not (cddr (erl-val-tuple->lst m))))
  :expand ((len (erl-val-tuple->lst m))
          (len (cdr (erl-val-tuple->lst m)))
          (len (cddr (erl-val-tuple->lst m))))
  :enable erl-vlst-p))

(defrule eval-receive-of-reduce-clauses-when-match
  (implies
    (and
      ; (erl-val-p m)
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (erl-val-kind (cadr (erl-val-tuple->lst m))) :integer)
      (omap::assoc 'ChildHd (erl-state->bind s))
      (equal (erl-val-kind (omap::lookup 'ChildHd (erl-state->bind s))) :pid)
      (not (omap::assoc 'RightTotal (erl-state->bind s)))
      (equal (car (erl-val-tuple->lst m))
             (omap::lookup 'ChildHd (erl-state->bind s))))
    (and
      (equal (mv-nth 1 (eval-receive (update-erl-state->in s m)
                                     *reduce-receive-clauses*))
             *reduce-receive-body*)
      (equal (mv-nth 0 (eval-receive (update-erl-state->in s m)
                                     *reduce-receive-clauses*))
             (update-erl-state->bind (update-erl-state->in s m)
               (omap::update 'RightTotal (cadr (erl-val-tuple->lst m))
                 (erl-state->bind s))))))
  :enable (eval-receive eval-clauses eval-clauses-when-consp
           match-args eval-match eval-guard-seq wf-state-p))

(defrule eval-receive-of-reduce-clauses-when-no-match
  (implies
    (and
      ; (erl-val-p m)
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (erl-val-kind (cadr (erl-val-tuple->lst m))) :integer)
      (omap::assoc 'ChildHd (erl-state->bind s))
      (not (omap::assoc 'RightTotal (erl-state->bind s)))
      (not (equal (car (erl-val-tuple->lst m))
                  (omap::lookup 'ChildHd (erl-state->bind s)))))
    (and
      (equal (mv-nth 1 (eval-receive (update-erl-state->in s m)
                                     *reduce-receive-clauses*))
             nil)
      (equal (mv-nth 0 (eval-receive (update-erl-state->in s m)
                                     *reduce-receive-clauses*))
             (update-erl-state->in (erl-state-fix s)
                                   (make-erl-val-blocked)))))
  :enable (eval-receive eval-clauses eval-clauses-when-consp
           match-args eval-match eval-guard-seq wf-state-p))

; receive -> blocked
(defrule apply-k-of-receive-klst-when-no-match
  (implies
    (and
      (reduce-receive-klst-p klst rbind)
      ; message facts
      (erl-val-p m)
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (erl-val-kind (cadr (erl-val-tuple->lst m))) :integer)
      ; bind facts, the message is not from ChildHd
      (omap::assoc 'ChildHd (erl-state->bind s))
      (not (omap::assoc 'RightTotal (erl-state->bind s)))
      (not (equal (car (erl-val-tuple->lst m))
                  (omap::lookup 'ChildHd (erl-state->bind s)))))
    (equal (apply-k (update-erl-state->in s m) klst)
           (update-erl-state->in (erl-state-fix s) (make-erl-val-blocked))))
  :do-not-induct t
  :use ((:instance apply-k-of-append
          (s (update-erl-state->in s m))
          (kl1 (list (car klst)))
          (kl2 (cdr klst))))
  :enable (reduce-receive-klst-p wf-state-p apply-k-of-receive-no-match)
  :disable (eval-receive eval-clauses eval-clauses-when-consp eval-match))


; Proc-Receive Lemmas for INV ----------------------------------------------------

