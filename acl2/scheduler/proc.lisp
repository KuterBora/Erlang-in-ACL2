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
   (klst true-listp :default nil)))

(define proc->pid ((p proc-p))
  :returns (pid pid-p)
  (b* ((p (proc-fix p)))
      (erl-state->self (proc->s p)))
  ///
    (more-returns
      (pid :name erl-val-kind-of-proc->pid
        (equal (erl-val-kind pid) :pid)
       :hints
        (("Goal"
            :in-theory (e/d (pid-p) (proc->pid pid-p-of-proc->pid))
            :use (:instance pid-p-of-proc->pid)))))
    (defcong proc-equiv equal (proc->pid p) 1))

(define proc->outbox ((p proc-p))
  :returns (o outbox-p)
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
      (and (proc->outbox p)
           (omap::assoc dst (proc->outbox p))
           (omap::lookup dst (proc->outbox p))))
  ///
    (defcong proc-equiv equal (proc-has-message-for-dst? p dst) 1)
    (defcong pid-equiv equal (proc-has-message-for-dst? p dst) 2))