(in-package "ACL2")
(include-book "proc")

; Erlang Network --------------------------------------------------------------

; todo: doc and defsection

(fty::defomap network-gen
    :key-type pid-p
    :val-type proc-p)

(define wf-network-p ((n network-gen-p))
  :enabled t
  :returns (b booleanp)
  :measure (acl2-count (network-gen-fix n))
  (b* ((n (network-gen-fix n))
       ((if (omap::emptyp n)) t))
      (and (equal (omap::head-key n) (proc->pid (omap::head-val n)))
           (wf-network-p (omap::tail n))))
  ///
    (defcong network-gen-equiv equal (wf-network-p n) 1)
    
    (defrule wf-network-p-of-update
      (implies
        (and (network-gen-p net) (wf-network-p net))
        (wf-network-p (omap::update (proc->pid p) p net)))
      :expand (wf-network-p (omap::update (proc->pid p) p nil))
      :hints
        (("Subgoal *1/4''"
            :expand (wf-network-p (omap::update (proc->pid p) p net)))))
    
    (defrule wf-network-p-of-update-2
      (implies
        (and (network-gen-p net1) (network-gen-p net2)
             (wf-network-p net1) (wf-network-p net2)
             (not (omap::emptyp net1)))
        (wf-network-p
          (omap::update
            (mv-nth 0 (omap::head net1))
            (mv-nth 1 (omap::head net1))
            net2))))
    
    (defrule wf-network-p-of-update*
      (implies
        (and (wf-network-p n1) (wf-network-p n2)
            (network-gen-p n1) (network-gen-p n2)
            (omap::compatiblep n1 n2))
        (wf-network-p (omap::update* n1 n2)))
      :enable (wf-network-p omap::update*)
      :prep-lemmas
        ((defrule compatiblep-of-tail
          (implies (omap::compatiblep a b)
                   (omap::compatiblep a (omap::tail b))))))

    (defrule wf-network-p-of-delete
      (implies
        (and (network-gen-p net) (wf-network-p net))
        (wf-network-p (omap::delete p net)))
      :enable (omap::delete)
      :hints
        (("Subgoal *1/4''"
           :use (:instance wf-network-p-of-update
                  (net (omap::delete p (omap::tail net)))
                  (p (mv-nth 1 (omap::head net))))))))

; TODO: create a rule-set called network-map-rules
; that contains the theory about map operations on networks.
(fty::defsubtype network
  :supertype network-gen
  :restriction (lambda (x) (wf-network-p x))
  :fix-value nil)

(defrule domain-of-network-p
  (implies (network-p n) (pid-set-p (omap::keys n)))
  :enable (network-p pid-set-p omap::keys))

(defrule network-p-of-update
  (implies
    (and (network-p net) (pid-p pid)
         (proc-p p) (equal (proc->pid p) pid))
    (network-p (omap::update pid p net)))
  :enable (network-gen-p network-p))
  
(defrule network-p-of-update-with-constructor
  (implies
    (and (network-p net) (pid-p pid))
    (network-p (omap::update pid (proc ps (erl-state a b c d pid e) f g h) net)))
  :enable (proc->pid network-gen-p network-p))

(defrule network-p-of-update*
  (implies (and (network-p n1) (network-p n2) (omap::compatiblep n1 n2))
           (network-p (omap::update* n1 n2)))
  :enable network-p)

(defrule network-p-of-delete
  (implies
    (and (network-p net) (pid-p pid))
    (network-p (omap::delete pid net)))
  :enable (network-gen-p network-p wf-network-p))

(defrule network-p-of-tail
  (implies (network-p net) (network-p (omap::tail net)))
  :enable network-p)

(defrule lookup-of-tail-when-assoc-tail-of-network
  (implies
    (and (network-p net) (pid-p pid) (omap::assoc pid (omap::tail net)))
    (equal (omap::lookup pid net)
           (omap::lookup pid (omap::tail net))))
  :enable (network-p network-gen-p)
  :use (:instance omap::lookup-of-tail-when-assoc-tail (key pid) (map net)))


; Predicates for Networks -----------------------------------------------------

(define runnable? ((n network-p) (p pid-p))
  :returns (b booleanp)
  (b* ((n (network-fix n))
       (p (pid-fix p)))
      (and (omap::assoc p n)
           (proc-runnable? (omap::lookup p n))))
  ///
    (defcong network-equiv equal (runnable? n p) 1)
    (defcong pid-equiv equal (runnable? n p) 2)
    
    (defrule runnable-of-tail
      (implies
        (and (pid-p p) (network-p n) (runnable? (omap::tail n) p))
        (runnable? n p))
      :enable proc-runnable?)
    
    (defrule assoc-of-runnable?
      (implies
        (and (network-p net) (pid-p p) (runnable? net p))
        (omap::assoc p net))))

(define has-message-for-dst? ((net network-p) (src pid-p) (dst pid-p))
  (b* ((net (network-fix net))
       (src (pid-fix src))
       (dst (pid-fix dst)))
      (and (omap::assoc src net)
           (proc-has-message-for-dst? (omap::lookup src net) dst)))
  ///
    (defcong network-equiv equal (has-message-for-dst? net src dst) 1)
    (defcong pid-equiv equal (has-message-for-dst? net src dst) 2)
    (defcong pid-equiv equal (has-message-for-dst? net src dst) 3)
    
    (defrule has-message-for-dst-of-tail
      (implies
        (and (pid-p p1) (pid-p p2) (network-p n)
             (has-message-for-dst? (omap::tail n) p1 p2))
        (has-message-for-dst? n p1 p2))
      :enable proc-has-message-for-dst?)
    
    (defrule assoc-of-lookup-when-has-message-for-dst?
      (implies
        (and (pid-p p1) (pid-p p2) (has-message-for-dst? net p1 p2))
        (omap::assoc p2 (proc->outbox (omap::lookup p1 net))))
      :enable (proc-has-message-for-dst? network-fix))
    
    (defrule lookup-of-lookup-when-has-message-for-dst?
      (implies
        (and (pid-p p1) (pid-p p2) (has-message-for-dst? net p1 p2))
        (omap::lookup p2 (proc->outbox (omap::lookup p1 net))))
      :enable (proc-has-message-for-dst? network-fix))

    (defrule erl-vlst-p-when-has-message-for-dst?
      (implies
        (and (pid-p p1) (pid-p p2) (has-message-for-dst? net p1 p2))
        (erl-vlst-p (omap::lookup p2 (proc->outbox (omap::lookup p1 net))))))

    (defrule consp-when-has-message-for-dst?
      (implies
        (and (pid-p p1) (pid-p p2) (has-message-for-dst? net p1 p2))
        (consp (omap::lookup p2 (proc->outbox (omap::lookup p1 net)))))
      :disable (has-message-for-dst?
                lookup-of-lookup-when-has-message-for-dst?
                erl-vlst-p-when-has-message-for-dst?)
      :use ((:instance lookup-of-lookup-when-has-message-for-dst?)
            (:instance erl-vlst-p-when-has-message-for-dst?)))

    (defrule has-message-for-dst?-when-assoc-on-tail
      (implies
        (and (pid-p p1) (pid-p p2)
             (omap::assoc p1 (omap::tail net))
             (has-message-for-dst? net p1 p2))
        (has-message-for-dst? (omap::tail net) p1 p2))
      :enable (proc-has-message-for-dst? network-fix)))

(define terminated? ((net network-p))
  (b* ((net (network-fix net))
       ((if (omap::emptyp net)) t))
      (and (not (or (equal (proc->ps (omap::head-val net)) :idle)
                    (equal (proc->ps (omap::head-val net)) :receive)
                    (proc->outbox (omap::head-val net))))
           (terminated? (omap::tail net))))
  :hints (("Goal" :in-theory (enable network-p network-fix)))
  ///
    (defcong network-equiv equal (terminated? net) 1))