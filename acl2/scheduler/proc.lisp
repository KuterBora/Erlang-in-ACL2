(in-package "ACL2")
(include-book "../eval/top")

; Erlang Process --------------------------------------------------------------

(std::defenum proc-state-p
  (:idle :terminated :receive :blocked))

(fty::defprod proc
  (; state of the Erlang process
   (ps proc-state-p :default :idle)

   ; BOZO: state of the Erlang program run by the process
   (s erl-state-p :default (make-erl-state))

   ; BOZO: the messages received, but not yet tried on the next
   ; receive. (this is only used to prevent receive loops)
   (inbox-new erl-vlst-p :default nil)

   ; BOZO: messages that have been received and have already been
   ; tried by the next receive.
   (inbox-tried erl-vlst-p :default nil)
   
   ; the remaining computation
   (klst erl-klst-p :default nil)))

(define proc->pid ((p proc-p))
  :returns (pid pid-p)
  :enabled t
  (b* ((p (proc-fix p)))
      (erl-state->self (proc->s p)))
  ///
    (defcong proc-equiv equal (proc->pid p) 1))

(define proc->outbox ((p proc-p))
  :returns (o outbox-p)
  :enabled t
  (b* ((p (proc-fix p)))
      (erl-state->outbox (proc->s p)))
  ///
    (defcong proc-equiv equal (proc->outbox p) 1))

(define proc-runnable? ((p proc-p))
  :returns (b booleanp)
  (b* ((p (proc-fix p)))
      (or (equal (proc->ps p) :idle)
          (equal (proc->ps p) :receive)))
  ///
    (defcong proc-equiv equal (proc-runnable? p) 1))

(define proc-has-message-for-dst? ((p proc-p) (dst pid-p))
  (b* ((p (proc-fix p))
       (dst (pid-fix dst)))
      (and (erl-state->outbox (proc->s p))
           (omap::assoc dst (erl-state->outbox (proc->s p)))))
  ///
    (defcong proc-equiv equal (proc-has-message-for-dst? p dst) 1)
    (defcong pid-equiv equal (proc-has-message-for-dst? p dst) 2))

(fty::defomap network-gen
    :key-type pid-p
    :val-type proc-p)

(define wf-network-p ((n network-gen-p))
  :enabled t
  :returns (b booleanp)
  :measure (acl2-count (network-gen-fix n))
  (b* ((n (network-gen-fix n))
       ((if (omap::emptyp n)) t))
      (and (equal (omap::head-key n) (erl-state->self (proc->s (omap::head-val n))))
           (wf-network-p (omap::tail n))))
  ///
    (defcong network-gen-equiv equal (wf-network-p n) 1))

(fty::defsubtype network
  :supertype network-gen
  :restriction (lambda (x) (wf-network-p x))
  :fix-value nil)

(defrule network-p-of-tail
  (implies (network-p net) (network-p (omap::tail net)))
  :enable network-p)

(defrule lookup-of-tail-when-assoc-tail-of-network
  (implies (and (network-p net) (pid-p pid) (omap::assoc pid (omap::tail net)))
            (equal (omap::lookup pid net)
                  (omap::lookup pid (omap::tail net))))
  :enable (network-p network-gen-p)
  :use (:instance omap::lookup-of-tail-when-assoc-tail (key pid) (map net)))

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
      :enable proc-runnable?))

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
      :enable proc-has-message-for-dst?))

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