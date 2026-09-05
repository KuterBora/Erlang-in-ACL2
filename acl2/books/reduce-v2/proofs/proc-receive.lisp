(in-package "ACL2")
(include-book "eval")
(include-book "../../../theorems/top")

; Proc-Receive Lemmas for INV ----------------------------------------------------

(defruled proc-receive-when-no-match
  (implies
    (and
      (proc-p p) (reduce-receive-klst-p (proc->klst p) rbind)
      (omap::assoc 'ChildHd (erl-state->bind (proc->s p)))
      (pid-p (omap::lookup 'ChildHd (erl-state->bind (proc->s p))))
      (not (omap::assoc 'RightTotal (erl-state->bind (proc->s p))))
      (wf-inbox-p (proc->inbox-new p))
      (not
        (inbox-contains
          (proc->inbox-new p)
          (omap::lookup 'ChildHd (erl-state->bind (proc->s p))))))
    (equal (proc-receive p)
           (change-proc p
             :ps :blocked
             :inbox-new nil
             :inbox-tried (append (proc->inbox-tried p) (proc->inbox-new p)))))
  :enable proc-receive)

; Another big lemma: the proc-receive counterpart to the *when-match apply-k lemmas.
(defruled proc-receive-when-match
  (implies
    (and
      (proc-p p) (reduce-receive-klst-p (proc->klst p) rbind)
      (equal (erl-state->world (proc->s p)) (sum-reduce-w))
      (equal (erl-state->module (proc->s p)) 'local)
      (omap::assoc 'ParentPid (erl-state->bind (proc->s p)))
      (omap::assoc 'ChildHd (erl-state->bind (proc->s p)))
      (omap::assoc 'ChildTl (erl-state->bind (proc->s p)))
      (omap::assoc 'LeftTotal (erl-state->bind (proc->s p)))
      (not (omap::assoc 'RightTotal (erl-state->bind (proc->s p))))
      (pid-p (omap::lookup 'ChildHd (erl-state->bind (proc->s p))))
      (equal
        (erl-val-kind
          (omap::lookup 'ChildTl (erl-state->bind (proc->s p))))
        :cons)
      (pid-lst-p
        (erl-val-cons->lst
          (omap::lookup 'ChildTl (erl-state->bind (proc->s p)))))
      (erl-val-cons->lst
        (omap::lookup 'ChildTl (erl-state->bind (proc->s p))))
      (equal
        (erl-val-kind
          (omap::lookup 'LeftTotal (erl-state->bind (proc->s p))))
        :integer)
      (or
        (equal
          (erl-val-kind
            (omap::lookup 'ParentPid (erl-state->bind (proc->s p))))
            :pid)
        (equal (omap::lookup 'ParentPid (erl-state->bind (proc->s p)))
               (make-erl-val-atom :val 'none)))
      (wf-inbox-p (proc->inbox-new p))
      (inbox-contains (proc->inbox-new p)
        (omap::lookup 'ChildHd (erl-state->bind (proc->s p)))))
    (equal
      (proc-receive p)
      (change-proc p
        :ps :receive
        :inbox-tried nil
        :inbox-new
          (append (proc->inbox-tried p)
                  (inbox-without (proc->inbox-new p)
                    (omap::lookup 'ChildHd (erl-state->bind (proc->s p)))))
        :klst
          (append
            (list (erl-k (- (erl-k->fuel (car (proc->klst p))) 6)
                        (erl-k->kont (car (proc->klst p))))
                  (erl-k (- (erl-k->fuel (car (proc->klst p))) 6)
                        (make-kont-exprs :exprs nil))
                  (erl-k (- (erl-k->fuel (car (proc->klst p))) 3)
                        (make-kont-function-return
                          :bind (omap::update 'RightTotal
                                  (inbox->value (proc->inbox-new p)
                                    (omap::lookup 'ChildHd
                                      (erl-state->bind (proc->s p))))
                                  (erl-state->bind (proc->s p)))
                          :module 'local))
                  (erl-k (- (erl-k->fuel (car (proc->klst p))) 1)
                        (make-kont-exprs :exprs nil)))
            (cdr (proc->klst p)))
        :s
          (update-erl-state->in
            (update-erl-state->in
              (update-erl-state->bind (proc->s p)
                (omap::from-lists
                  (list 'CPids 'ChildHd 'ChildTl 'LeftTotal 'ParentPid)
                  (list
                    (omap::lookup 'ChildTl (erl-state->bind (proc->s p)))
                    (car (erl-val-cons->lst
                          (omap::lookup 'ChildTl
                            (erl-state->bind (proc->s p)))))
                    (make-erl-val-cons
                      :lst (cdr (erl-val-cons->lst
                                  (omap::lookup 'ChildTl
                                    (erl-state->bind (proc->s p))))))
                    (make-erl-val-integer
                      :val (+ (erl-val-integer->val
                                (omap::lookup 'LeftTotal
                                  (erl-state->bind (proc->s p))))
                              (erl-val-integer->val
                                (inbox->value (proc->inbox-new p)
                                  (omap::lookup 'ChildHd
                                    (erl-state->bind (proc->s p)))))))
                    (omap::lookup 'ParentPid
                      (erl-state->bind (proc->s p))))))
              (make-erl-val-receive :klst
                (append
                  (list (erl-k (- (erl-k->fuel (car (proc->klst p))) 6)
                              (erl-k->kont (car (proc->klst p))))
                        (erl-k (- (erl-k->fuel (car (proc->klst p))) 6)
                              (make-kont-exprs :exprs nil))
                        (erl-k (- (erl-k->fuel (car (proc->klst p))) 3)
                              (make-kont-function-return
                                :bind (omap::update 'RightTotal
                                        (inbox->value (proc->inbox-new p)
                                          (omap::lookup 'ChildHd
                                            (erl-state->bind
                                              (proc->s p))))
                                        (erl-state->bind (proc->s p)))
                                :module 'local))
                        (erl-k (- (erl-k->fuel (car (proc->klst p))) 1)
                              (make-kont-exprs :exprs nil)))
                  (cdr (proc->klst p)))))
            (make-erl-val-none)))))
  :enable (proc-receive inbox-contains inbox-without inbox->value)
  :hints
    (("Goal"
      :expand ((:free (x) (inbox-contains nil x))
               (:free (x) (inbox-without nil x))
               (:free (x) (inbox->value nil x))
               (inbox->value (proc->inbox-new p)
                 (omap::lookup 'ChildHd (erl-state->bind (proc->s p))))
               (inbox-contains (proc->inbox-new p)
                 (omap::lookup 'ChildHd (erl-state->bind (proc->s p))))
               (inbox-without (proc->inbox-new p)
                 (omap::lookup 'ChildHd (erl-state->bind (proc->s p))))))
     ("Subgoal *1/1"
      :use ((:instance apply-k-of-reduce-receive-klst-when-match
              (s (proc->s p)) (m (car (proc->inbox-new p)))
              (klst (proc->klst p)))))
     ("Subgoal *1/2"
      :use ((:instance apply-k-of-reduce-receive-klst-when-match
              (s (proc->s p)) (m (car (proc->inbox-new p)))
              (klst (proc->klst p)))))
     ("Subgoal *1/3"
      :use ((:instance apply-k-of-reduce-receive-klst-when-match
              (s (proc->s p)) (m (car (proc->inbox-new p)))
              (klst (proc->klst p)))))
     ("Subgoal *1/4"
      :use ((:instance apply-k-of-reduce-receive-klst-when-match
              (s (proc->s p)) (m (car (proc->inbox-new p)))
              (klst (proc->klst p)))))
     ("Subgoal *1/5"
      :use ((:instance apply-k-of-reduce-receive-klst-when-match
              (s (proc->s p)) (m (car (proc->inbox-new p)))
              (klst (proc->klst p)))))))

; BOZO: Here is another very bug lemma, that performs terribly.
; If I had more time. I would definitely find a better solution.
; It was even worse earlier, until I tries quick-and-dirty-srs.
; The docs suggest not doing that, and I should probably listen,
; as I do not quite know how it works.
(local (defun qd-srs-off-2 (cl1 ac)
  (declare (ignore cl1 ac) (xargs :guard t)) nil))
(local (defattach (quick-and-dirty-srs qd-srs-off-2) :system-ok t))
(defruled proc-receive-of-match-with-more-children
  (implies
    (and
      (proc-p p) (equal (proc->ps p) :receive)
      (equal (erl-val-kind (erl-state->in (proc->s p))) :none)
      (null (proc->inbox-tried p)) (null (proc->outbox p))
      (equal (erl-state->world (proc->s p)) (sum-reduce-w))
      (equal (erl-state->module (proc->s p)) 'local)
      (equal
        (erl-val-kind
          (omap::lookup 'CPids (erl-state->bind (proc->s p))))
        :cons)
      (pid-lst-p
        (erl-val-cons->lst
          (omap::lookup 'CPids (erl-state->bind (proc->s p)))))
      (erl-val-cons->lst
        (omap::lookup 'CPids (erl-state->bind (proc->s p))))
      (equal
        (omap::lookup 'ChildHd
          (erl-state->bind (proc->s p)))
        (car (erl-val-cons->lst
               (omap::lookup 'CPids (erl-state->bind (proc->s p))))))
      (equal
        (erl-val-kind (omap::lookup 'ChildTl (erl-state->bind (proc->s p)))) :cons)
      (equal
        (erl-val-cons->lst
          (omap::lookup 'ChildTl (erl-state->bind (proc->s p))))
        (cdr (erl-val-cons->lst
               (omap::lookup 'CPids (erl-state->bind (proc->s p))))))
      (equal
        (erl-val-kind
          (omap::lookup 'LeftTotal (erl-state->bind (proc->s p))))
        :integer)
      (reduce-receive-klst-p (proc->klst p) rbind)
      (cdr (erl-val-cons->lst
            (omap::lookup 'CPids (erl-state->bind (proc->s p)))))
      (inbox-contains
        (proc->inbox-new p)
        (car (erl-val-cons->lst
               (omap::lookup 'CPids (erl-state->bind (proc->s p))))))
      (equal
        (erl-val-kind
          (inbox->value
            (proc->inbox-new p)
            (car (erl-val-cons->lst
                   (omap::lookup 'CPids
                      (erl-state->bind (proc->s p)))))))
        :integer)
      (omap::assoc 'ParentPid (erl-state->bind (proc->s p)))
      (omap::assoc 'ChildHd (erl-state->bind (proc->s p)))
      (omap::assoc 'ChildTl (erl-state->bind (proc->s p)))
      (omap::assoc 'LeftTotal (erl-state->bind (proc->s p)))
      (not (omap::assoc 'RightTotal (erl-state->bind (proc->s p))))
      (or
        (equal
          (erl-val-kind
            (omap::lookup 'ParentPid(erl-state->bind (proc->s p))))
          :pid)
        (equal
          (omap::lookup 'ParentPid (erl-state->bind (proc->s p)))
          (make-erl-val-atom :val 'none)))
      (wf-inbox-p (proc->inbox-new p))
      (> (erl-k->fuel (car (proc->klst p)))
         (+ 100 (* 6 (len (erl-val-cons->lst
                            (omap::lookup 'CPids
                              (erl-state->bind (proc->s p)))))))))
    (and
      (equal (proc->ps (proc-receive p)) :receive)
      (equal (erl-val-kind (erl-state->in (proc->s (proc-receive p))))
             :none)
      (equal (proc->outbox (proc-receive p)) nil) 
      (iff (omap::assoc 'Index (wtree-bind (proc-receive p)))
           (omap::assoc 'Index (wtree-bind p)))
      (iff (omap::assoc 'Parent (wtree-bind (proc-receive p)))
           (omap::assoc 'Parent (wtree-bind p)))
      (iff (omap::assoc 'ChildPids (wtree-bind (proc-receive p)))
           (omap::assoc 'ChildPids (wtree-bind p)))
      (equal (omap::lookup 'Index (wtree-bind (proc-receive p)))
             (omap::lookup 'Index (wtree-bind p)))
      (equal (omap::lookup 'Parent (wtree-bind (proc-receive p)))
             (omap::lookup 'Parent (wtree-bind p)))
      (equal (omap::lookup 'ChildPids (wtree-bind (proc-receive p)))
             (omap::lookup 'ChildPids (wtree-bind p)))
      (equal (erl-state->self (proc->s (proc-receive p)))
             (erl-state->self (proc->s p)))
      (equal (erl-state->world (proc->s (proc-receive p)))
             (sum-reduce-w))
      (equal (erl-state->module (proc->s (proc-receive p))) 'local) 
      (equal (proc->inbox-tried (proc-receive p)) nil)
      (equal
        (proc->inbox-new (proc-receive p))
        (inbox-without
          (proc->inbox-new p)
          (car (erl-val-cons->lst
                 (omap::lookup 'CPids (erl-state->bind (proc->s p)))))))
      (omap::assoc 'ParentPid (erl-state->bind (proc->s (proc-receive p))))
      (omap::assoc 'CPids (erl-state->bind (proc->s (proc-receive p))))
      (omap::assoc 'ChildHd (erl-state->bind (proc->s (proc-receive p))))
      (omap::assoc 'ChildTl (erl-state->bind (proc->s (proc-receive p))))
      (omap::assoc 'LeftTotal (erl-state->bind (proc->s (proc-receive p))))
      (not (omap::assoc 'RightTotal
             (erl-state->bind (proc->s (proc-receive p)))))
      (equal
        (omap::lookup 'ParentPid
          (erl-state->bind (proc->s (proc-receive p))))
        (omap::lookup 'ParentPid (erl-state->bind (proc->s p))))
      (equal
        (erl-val-kind
          (omap::lookup 'CPids (erl-state->bind (proc->s (proc-receive p)))))
        :cons)
      (equal
        (erl-val-cons->lst (omap::lookup 'CPids
                              (erl-state->bind (proc->s (proc-receive p)))))
        (cdr (erl-val-cons->lst (omap::lookup 'CPids
                                  (erl-state->bind (proc->s p))))))
      (equal
        (omap::lookup 'ChildHd
          (erl-state->bind (proc->s (proc-receive p))))
        (cadr (erl-val-cons->lst (omap::lookup 'CPids
                                    (erl-state->bind (proc->s p))))))
      (equal
          (erl-val-kind
            (omap::lookup 'ChildTl (erl-state->bind (proc->s (proc-receive p)))))
          :cons)
      (equal
        (erl-val-cons->lst (omap::lookup 'ChildTl
                              (erl-state->bind (proc->s (proc-receive p)))))
        (cddr (erl-val-cons->lst (omap::lookup 'CPids (erl-state->bind (proc->s p))))))
      (equal
        (erl-val-kind
          (omap::lookup 'LeftTotal (erl-state->bind (proc->s (proc-receive p)))))
        :integer)
      (equal
        (erl-val-integer->val
          (omap::lookup 'LeftTotal
            (erl-state->bind (proc->s (proc-receive p)))))
        (+ (erl-val-integer->val
             (omap::lookup 'LeftTotal (erl-state->bind (proc->s p))))
           (erl-val-integer->val
             (inbox->value
                (proc->inbox-new p)
                (car (erl-val-cons->lst
                       (omap::lookup 'CPids
                          (erl-state->bind (proc->s p)))))))))
      (erl-klst-p (proc->klst (proc-receive p)))
      (reduce-receive-klst-p (proc->klst (proc-receive p)) rbind)
      (> (erl-k->fuel (car (proc->klst (proc-receive p))))
        (+ 100 (* 6 (len (cdr (erl-val-cons->lst
                                (omap::lookup 'CPids
                                  (erl-state->bind (proc->s p)))))))))))
  :use ((:instance proc-receive-when-match)
        (:instance reduce-receive-klst-p-new-call-stack
          (klst (proc->klst p))
          (b (omap::update 'RightTotal
               (inbox->value (proc->inbox-new p) (omap::lookup 'ChildHd (erl-state->bind (proc->s p))))
               (erl-state->bind (proc->s p))))))
  :enable (wtree-bind proc->outbox omap::from-lists omap::lookup-of-update)
  :disable
    (wtree-bind0-to-wtree-bind proc-receive-when-match wtree0-of-zero
     reduce-receive-klst-p-new-call-stack erl-val-kind-of-pid-p
     omap::assoc-when-assoc-tail omap::lookup-when-emptyp default-car
     consp-of-cdr-of-erl-vlst (:type-prescription network-p) default-cdr
     lookup-when-outbox-emptyp erl-val-p-when-erl-fun-p-rewrite
     erl-val-when-erl-fun omap::assoc-when-assoc-of-tail-cheap
     (:type-prescription omap::tail-when-emptyp) erl-vlst-p-of-pid-lst
     received-messages-wf-fields (:type-prescription outbox-p) default-+-1
     assoc-of-runnable? subsetp-when-atom-left omap::tail-when-emptyp
     subsetp-member default-+-2 omap::assoc-when-emptyp network-p-of-tail
     member-of-cdr-when-not-car equal-of-erl-val-integer consp-of-expr-list-p
     omap::update-when-emptyp (:type-prescription erl-state->in$inline)
     wtree-bind0-when-no-function-return))
(local (defattach (quick-and-dirty-srs quick-and-dirty-srs-builtin)
         :system-ok t))