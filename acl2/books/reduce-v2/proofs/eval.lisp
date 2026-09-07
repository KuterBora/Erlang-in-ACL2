; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "inv")
(include-book "../../../theorems/top")

; BOZO: a lot of these can become way shorter and cheaper by proving some
; core properties. However, I am leaving that work for after we have
; implemented a meta-function/clause-processor.

; Apply-K Lemmas for INV ---------------------------------------------------------

(local (defrule erl-val-kind-of-car-of-pid-lst
  (implies
    (and (pid-lst-p x) (consp x))
    (and (erl-val-p (car x))
         (equal (erl-val-kind (car x)) :pid)))
  :enable pid-p))

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
  :enable
    (reduce-receive-klst-p omap::from-lists match-args eval-match
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
  :enable
    (wf-state-p pid-p make-reduce-proc omap::from-lists
     apply-k-of-local-call-when-match apply-k-of-local-call-no-match
     apply-k-of-cons apply-k-of-binop-expr1 eval-guard-expr eval-bif
     eval-local-call eval-clauses eval-clauses-when-consp eval-guard
     match-args eval-match eval-guard-seq eval-guard-seq-when-consp
     omap::lookup-of-update))


; Properties of eval receive
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

; receive -> receive
(local (defrule apply-k-of-reduce-receive-k-when-match
  (implies
    (and
      (equal (erl-k->kont k)
             (make-kont-receive :clauses *reduce-receive-clauses*))
      (> (erl-k->fuel k) 100)
      (equal (erl-state->world s) (sum-reduce-w))
      (equal (erl-state->module s) 'local)
      (omap::assoc 'ParentPid (erl-state->bind s))
      (omap::assoc 'ChildHd (erl-state->bind s))
      (omap::assoc 'ChildTl (erl-state->bind s))
      (omap::assoc 'LeftTotal (erl-state->bind s))
      (not (omap::assoc 'RightTotal (erl-state->bind s)))
      (equal
        (erl-val-kind
          (omap::lookup 'ChildHd (erl-state->bind s)))
        :pid)
      (equal
        (erl-val-kind (omap::lookup 'ChildTl (erl-state->bind s)))
        :cons)
      (pid-lst-p
        (erl-val-cons->lst
          (omap::lookup 'ChildTl (erl-state->bind s))))
      (erl-val-cons->lst
        (omap::lookup 'ChildTl (erl-state->bind s)))
      (equal
        (erl-val-kind (omap::lookup 'LeftTotal (erl-state->bind s)))
        :integer)
      (or
        (equal
          (erl-val-kind (omap::lookup 'ParentPid (erl-state->bind s)))
          :pid)
        (equal (omap::lookup 'ParentPid (erl-state->bind s))
               (make-erl-val-atom :val 'none)))
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (erl-val-kind (cadr (erl-val-tuple->lst m))) :integer)
      (equal (car (erl-val-tuple->lst m))
             (omap::lookup 'ChildHd (erl-state->bind s))))
    (equal
      (apply-k (update-erl-state->in s m) (list k))
      (update-erl-state->in
        (update-erl-state->bind (erl-state-fix s)
          (omap::from-lists
            (list 'CPids 'ChildHd 'ChildTl 'LeftTotal 'ParentPid)
            (list (omap::lookup 'ChildTl (erl-state->bind s))
                  (car (erl-val-cons->lst
                         (omap::lookup 'ChildTl (erl-state->bind s))))
                  (make-erl-val-cons
                    :lst (cdr (erl-val-cons->lst
                                (omap::lookup 'ChildTl (erl-state->bind s)))))
                  (make-erl-val-integer
                    :val (+ (erl-val-integer->val
                              (omap::lookup 'LeftTotal (erl-state->bind s)))
                            (erl-val-integer->val
                              (cadr (erl-val-tuple->lst m)))))
                  (omap::lookup 'ParentPid (erl-state->bind s)))))
        (make-erl-val-receive :klst
          (list (erl-k (- (erl-k->fuel k) 6) (erl-k->kont k))
                (erl-k (- (erl-k->fuel k) 6) (make-kont-exprs :exprs nil))
                (erl-k (- (erl-k->fuel k) 3)
                       (make-kont-function-return
                         :bind (omap::update 'RightTotal
                                 (cadr (erl-val-tuple->lst m))
                                 (erl-state->bind s))
                         :module 'local))
                (erl-k (- (erl-k->fuel k) 1)
                       (make-kont-exprs :exprs nil)))))))
  :enable
    (wf-state-p pid-p omap::from-lists omap::lookup-of-update
     apply-k-of-receive-when-match match-args eval-match
     apply-k-of-local-call-when-match apply-k-of-local-call-no-match
     apply-k-of-cons apply-k-of-binop-expr1
     eval-local-call eval-clauses eval-clauses-when-consp
     eval-guard-seq match-args eval-match eval-bif)))

; receive -> receive, but for klst
(defrule apply-k-of-reduce-receive-klst-when-match
  (implies
    (and
      (erl-klst-p klst) (reduce-receive-klst-p klst rbind)
      (equal (erl-state->world s) (sum-reduce-w))
      (equal (erl-state->module s) 'local)
      (omap::assoc 'ParentPid (erl-state->bind s))
      (omap::assoc 'ChildHd (erl-state->bind s))
      (omap::assoc 'ChildTl (erl-state->bind s))
      (omap::assoc 'LeftTotal (erl-state->bind s))
      (not (omap::assoc 'RightTotal (erl-state->bind s)))
      (equal
        (erl-val-kind
          (omap::lookup 'ChildHd (erl-state->bind s)))
        :pid)
      (equal
        (erl-val-kind (omap::lookup 'ChildTl (erl-state->bind s)))
        :cons)
      (pid-lst-p
        (erl-val-cons->lst
          (omap::lookup 'ChildTl (erl-state->bind s))))
      (erl-val-cons->lst
        (omap::lookup 'ChildTl (erl-state->bind s)))
      (equal
        (erl-val-kind (omap::lookup 'LeftTotal (erl-state->bind s)))
        :integer)
      (or
        (equal
          (erl-val-kind (omap::lookup 'ParentPid (erl-state->bind s)))
          :pid)
        (equal (omap::lookup 'ParentPid (erl-state->bind s))
               (make-erl-val-atom :val 'none)))
      (erl-val-p m)
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (erl-val-kind (cadr (erl-val-tuple->lst m))) :integer)
      (equal (car (erl-val-tuple->lst m))
             (omap::lookup 'ChildHd (erl-state->bind s))))
    (equal
      (apply-k (update-erl-state->in s m) klst)
      (update-erl-state->in
        (update-erl-state->bind (erl-state-fix s)
          (omap::from-lists
            (list 'CPids 'ChildHd 'ChildTl 'LeftTotal 'ParentPid)
            (list (omap::lookup 'ChildTl (erl-state->bind s))
                  (car (erl-val-cons->lst
                         (omap::lookup 'ChildTl (erl-state->bind s))))
                  (make-erl-val-cons
                    :lst (cdr (erl-val-cons->lst
                                (omap::lookup 'ChildTl (erl-state->bind s)))))
                  (make-erl-val-integer
                    :val (+ (erl-val-integer->val
                              (omap::lookup 'LeftTotal (erl-state->bind s)))
                            (erl-val-integer->val
                              (cadr (erl-val-tuple->lst m)))))
                  (omap::lookup 'ParentPid (erl-state->bind s)))))
        (make-erl-val-receive :klst
          (append
            (list (erl-k (- (erl-k->fuel (car klst)) 6)
                         (erl-k->kont (car klst)))
                  (erl-k (- (erl-k->fuel (car klst)) 6)
                         (make-kont-exprs :exprs nil))
                  (erl-k (- (erl-k->fuel (car klst)) 3)
                         (make-kont-function-return
                           :bind (omap::update 'RightTotal
                                   (cadr (erl-val-tuple->lst m))
                                   (erl-state->bind s))
                           :module 'local))
                  (erl-k (- (erl-k->fuel (car klst)) 1)
                         (make-kont-exprs :exprs nil)))
            (cdr klst))))))
  :use ((:instance apply-k-of-append
          (s (update-erl-state->in s m))
          (kl1 (list (car klst)))
          (kl2 (cdr klst))))
  :enable reduce-receive-klst-p)

; TODO: this should move the theorems folder
(defruled apply-k-of-exprs-nil-cons
  (implies
    (and
      (consp klst) (wf-state-p s)
      (> (erl-k->fuel (car klst)) 0)
      (equal (kont-kind (erl-k->kont (car klst))) :exprs)
      (endp (kont-exprs->exprs (erl-k->kont (car klst)))))
    (equal (apply-k s klst) (apply-k (erl-state-fix s) (cdr klst))))
  :use ((:instance apply-k-of-append (kl1 (list (car klst))) (kl2 (cdr klst))))
  :enable wf-state-p)

; TODO: this should also move the theorems folder
(defruled apply-k-of-function-return-cons
  (implies
    (and
      (consp klst) (wf-state-p s)
      (> (erl-k->fuel (car klst)) 0)
      (equal (kont-kind (erl-k->kont (car klst))) :function-return))
    (equal
      (apply-k s klst)
      (apply-k
        (update-erl-state->bind-mod
          (erl-state-fix s)
          (kont-function-return->bind (erl-k->kont (car klst)))
          (kont-function-return->module (erl-k->kont (car klst))))
        (cdr klst))))
  :use ((:instance apply-k-of-append
          (kl1 (list (car klst))) (kl2 (cdr klst)))))

(defruled apply-k-of-reduce-klst-lst-p
  (implies
    (and
      (erl-klst-p klst) (wf-state-p s)
      (reduce-klst-lst-p klst rbind))
    (equal
      (apply-k s klst)
      (update-erl-state->bind-mod
        (erl-state-fix s)
        (bind-fix rbind)
        'local)))
  :induct (tmp-induct s klst)
  :enable (reduce-klst-lst-p apply-k-of-exprs-nil-cons
           apply-k-of-function-return-cons wf-state-p
           update-erl-state->bind-mod)
  :prep-lemmas
    ((defun tmp-induct (s klst)
      (declare (xargs :measure (len (erl-klst-fix klst))))
      (b* ((klst (erl-klst-fix klst))
           ((unless (<= 3 (len klst))) s))
          (tmp-induct
            (update-erl-state->bind-mod s
              (kont-function-return->bind (erl-k->kont (caddr klst))) 'local)
            (cdddr klst))))))

; same as above, but for the last receive of a node.
(local (defrule apply-k-of-reduce-receive-k-when-match-last
  (implies
    (and 
      (equal
        (erl-k->kont k)
        (make-kont-receive :clauses *reduce-receive-clauses*))
      (> (erl-k->fuel k) 100)
      (equal (erl-state->world s) (sum-reduce-w))
      (equal (erl-state->module s) 'local)
      (not (erl-state->outbox s))
      (omap::assoc 'ParentPid (erl-state->bind s))
      (omap::assoc 'ChildHd (erl-state->bind s))
      (omap::assoc 'ChildTl (erl-state->bind s))
      (omap::assoc 'LeftTotal (erl-state->bind s))
      (not (omap::assoc 'RightTotal (erl-state->bind s)))
      (equal
        (erl-val-kind
          (omap::lookup 'ChildHd (erl-state->bind s)))
        :pid)
      (equal
        (erl-val-kind
          (omap::lookup 'ChildTl (erl-state->bind s)))
        :cons)
      (not
        (erl-val-cons->lst (omap::lookup 'ChildTl (erl-state->bind s))))
      (equal
        (erl-val-kind (omap::lookup 'LeftTotal (erl-state->bind s)))
        :integer)
      (or (pid-p (omap::lookup 'ParentPid (erl-state->bind s)))
          (equal (omap::lookup 'ParentPid (erl-state->bind s))
                 (make-erl-val-atom :val 'none)))
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (erl-val-kind (cadr (erl-val-tuple->lst m))) :integer)
      (equal (car (erl-val-tuple->lst m))
             (omap::lookup 'ChildHd (erl-state->bind s))))
    (equal
      (apply-k (update-erl-state->in s m) (list k))
      (update-erl-state->outbox
        (update-erl-state->bind
          (update-erl-state->in (erl-state-fix s)
            (make-erl-val-integer
              :val (+ (erl-val-integer->val
                        (omap::lookup 'LeftTotal (erl-state->bind s)))
                      (erl-val-integer->val
                        (cadr (erl-val-tuple->lst m))))))
          (omap::update 'RightTotal
            (cadr (erl-val-tuple->lst m)) (erl-state->bind s)))
        (if (pid-p (omap::lookup 'ParentPid (erl-state->bind s)))
            (omap::update (omap::lookup 'ParentPid (erl-state->bind s))
              (list
                (make-erl-val-tuple
                  :lst
                    (list
                      (erl-state->self s)
                      (make-erl-val-integer
                        :val (+ (erl-val-integer->val
                                  (omap::lookup 'LeftTotal (erl-state->bind s)))
                                (erl-val-integer->val (cadr (erl-val-tuple->lst m))))))))
              nil)
          nil))))
  :enable
    (wf-state-p pid-p erl-state-send match-args eval-match eval-bif
     update-erl-state->bind-mod omap::from-lists omap::lookup-of-update
     eval-clauses-when-consp apply-k-of-receive-when-match
     eval-local-call eval-guard-seq apply-k-of-local-call-when-match
     apply-k-of-binop-expr1 apply-k-of-local-call-no-match
     apply-k-of-cons eval-clauses)))

; same as above but for klst insteaf of a single k
(defrule apply-k-of-reduce-receive-klst-when-match-last
  (implies
    (and
      (erl-klst-p klst) (reduce-receive-klst-p klst rbind)
      (equal (erl-state->world s) (sum-reduce-w))
      (equal (erl-state->module s) 'local)
      (not (erl-state->outbox s))
      (omap::assoc 'ParentPid (erl-state->bind s))
      (omap::assoc 'ChildHd (erl-state->bind s))
      (omap::assoc 'ChildTl (erl-state->bind s))
      (omap::assoc 'LeftTotal (erl-state->bind s))
      (not (omap::assoc 'RightTotal (erl-state->bind s)))
      (equal
        (erl-val-kind
          (omap::lookup 'ChildHd (erl-state->bind s)))
        :pid)
      (equal
        (erl-val-kind
          (omap::lookup 'ChildTl (erl-state->bind s)))
        :cons)
      (not (erl-val-cons->lst
             (omap::lookup 'ChildTl (erl-state->bind s))))
      (equal (erl-val-kind
               (omap::lookup 'LeftTotal (erl-state->bind s))) :integer)
      (or (pid-p (omap::lookup 'ParentPid (erl-state->bind s)))
          (equal (omap::lookup 'ParentPid (erl-state->bind s))
                 (make-erl-val-atom :val 'none)))
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (erl-val-kind (cadr (erl-val-tuple->lst m))) :integer))
    (equal
      (apply-k (update-erl-state->in s m) klst)
      (if (equal (car (erl-val-tuple->lst m))
                 (omap::lookup 'ChildHd (erl-state->bind s)))
          (update-erl-state->bind-mod
            (update-erl-state->outbox
              (update-erl-state->bind
                (update-erl-state->in (erl-state-fix s)
                  (make-erl-val-integer
                    :val (+ (erl-val-integer->val
                              (omap::lookup 'LeftTotal
                                (erl-state->bind s)))
                            (erl-val-integer->val
                              (cadr (erl-val-tuple->lst m))))))
                (omap::update 'RightTotal
                  (cadr (erl-val-tuple->lst m)) (erl-state->bind s)))
              (if (pid-p (omap::lookup 'ParentPid (erl-state->bind s)))
                  (omap::update (omap::lookup 'ParentPid (erl-state->bind s))
                    (list
                      (make-erl-val-tuple
                        :lst
                          (list
                            (erl-state->self s)
                            (make-erl-val-integer
                              :val (+ (erl-val-integer->val
                                        (omap::lookup 'LeftTotal
                                          (erl-state->bind s)))
                                      (erl-val-integer->val
                                        (cadr (erl-val-tuple->lst m))))))))
                    nil)
                nil))
            (bind-fix rbind)
            'local)
          (update-erl-state->in
            (erl-state-fix s) (make-erl-val-blocked)))))
  :enable
    (reduce-receive-klst-p wf-state-p
     apply-k-of-exprs-nil-cons apply-k-of-function-return-cons
     apply-k-of-reduce-klst-lst-p
     update-erl-state->bind-mod)
  :use ((:instance apply-k-of-append
          (s (update-erl-state->in s m))
          (kl1 (list (car klst)))
          (kl2 (cdr klst)))))


; More Properties of apply-k -----------------------------------------------------

; wtree bindings do not change after idle -> receive/terminated
(defrule wtree-bind0-of-first-run-with-children
  (implies
    (and
      (equal s (proc->s (make-reduce-proc self parent children index)))
      (equal klst (proc->klst (make-reduce-proc self parent children index)))
      (pid-lst-p children) (natp index) children
      (or (pid-p parent)
          (equal parent (make-erl-val-atom :val 'none))))
    (equal
      (wtree-bind0 bind
        (erl-val-receive->klst (erl-state->in (apply-k s klst))))
      (bind-fix (erl-state->bind s))))
  :use ((:instance apply-k-of-idle-with-children))
  :disable apply-k-of-idle-with-children)

; reduce-receive-klst-p holds after idle -> receive
(defrule reduce-receive-klst-p-of-first-run-with-children
  (implies
    (and
      (equal
        (proc->s p)
        (proc->s (make-reduce-proc self parent children index)))
      (equal
        (proc->klst p)
        (proc->klst (make-reduce-proc self parent children index)))
      (pid-lst-p children) (natp index) children
      (or (pid-p parent)
          (equal parent (make-erl-val-atom :val 'none))))
    (reduce-receive-klst-p
      (erl-val-receive->klst
        (erl-state->in (apply-k (proc->s p) (proc->klst p))))
      (wtree-bind p)))
  :use ((:instance apply-k-of-idle-with-children
          (s (proc->s p)) (klst (proc->klst p))))
  :disable (apply-k-of-idle-with-children))


