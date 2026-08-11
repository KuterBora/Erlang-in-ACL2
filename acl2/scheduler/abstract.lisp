(in-package "ACL2")
(include-book "proc")
; (include-book "std/omaps/extensionality" :dir :system)

(set-induction-depth-limit 1)

; Possible Scheduling Steps ---------------------------------------------------

(fty::deftagsum scheduling
  (:run ((p pid-p)))
  (:deliver ((p1 pid-p) (p2 pid-p)))
  (:stutter ()))


; Weakly Fair Abstract Scheduler ----------------------------------------------

(encapsulate
  ; TODO: for fairness properties, we also need an abstarct state.
  ; that the scheduler uses to choose what action to take.
  ; I am guessing we will need this when we introduce fairness.
  (((schedule * ) => * :formals (net) :guard (network-p net)))

  ; Witness function

  (local (define schedule ((net network-p))
    :returns (s scheduling-p)
    :verify-guards nil
    :measure (acl2-count (network-fix net))
    (b* ((net (network-fix net))
         ((if (omap::emptyp net)) (make-scheduling-stutter))
         (pid (omap::head-key net))
         ((if (runnable? net pid)) (make-scheduling-run :p pid))
         (outbox (proc->outbox (omap::lookup pid net)))
         ((unless (omap::emptyp outbox)) (make-scheduling-deliver :p1 pid :p2 (omap::head-key outbox))))
        (schedule (omap::tail net)))
    :hints (("Goal" :in-theory (enable network-fix)))
    ///
      (defcong network-equiv equal (schedule net) 1)
      (verify-guards schedule
        :hints (("Goal" :in-theory (enable network-p))))))
  
  ; Theorems

  (local (defrule crock-1
    (implies (and (omap::assoc x m) (not (omap::assoc x (omap::tail m))))
             (equal (omap::head-key m) x))))

  ; The scheduler is weakly fair
  (defrule scheduler-weakly-fair-when-runnable
    (implies
      (and (pid-p pid)
           (network-p net)
           (omap::assoc pid net)
           (runnable? net pid))
      (not (equal (schedule net) (make-scheduling-stutter))))
    :enable (schedule runnable? proc-runnable?)
    :hints (("Subgoal *1/3" :use (:instance crock-1 (x pid) (m net)))))
  
  (defrule scheduler-weakly-fair-when-deliverable
    (implies
      (and (pid-p pid) (pid-p dst)
           (network-p net)
           (omap::assoc pid net)
           (has-message-for-dst? net pid dst))
      (not (equal (schedule net) (make-scheduling-stutter))))
    :enable (schedule has-message-for-dst? proc-has-message-for-dst? proc->outbox)
    :hints (("Subgoal *1/5" :use (:instance crock-1 (x pid) (m net)))
            ("Subgoal *1/6" :use ((:instance crock-1 (x pid) (m net))))))
  
  ; The scheduler is correct
  (defrule scheduler-correct-of-run
    (implies
      (and (network-p net) (equal (scheduling-kind (schedule net)) :run))
      (runnable? net (scheduling-run->p (schedule net))))
    :enable schedule)
  
  (defrule scheduler-correct-of-deliver
    (implies
      (and (network-p net) (equal (scheduling-kind (schedule net)) :deliver))
      (has-message-for-dst?
        net
        (scheduling-deliver->p1 (schedule net))
        (scheduling-deliver->p2 (schedule net))))
    :enable (schedule has-message-for-dst? proc-has-message-for-dst?)))

; Executable counterpart
(define in-order-schedule ((net network-p))
  :returns (s scheduling-p)
  :verify-guards nil
  :measure (acl2-count (network-fix net))
  (b* ((net (network-fix net))
        ((if (omap::emptyp net)) (make-scheduling-stutter))
        (pid (omap::head-key net))
        ((if (runnable? net pid)) (make-scheduling-run :p pid))
        (outbox (proc->outbox (omap::lookup pid net)))
        ((unless (omap::emptyp outbox)) (make-scheduling-deliver :p1 pid :p2 (omap::head-key outbox))))
      (in-order-schedule (omap::tail net)))
  :hints (("Goal" :in-theory (enable network-fix)))
  ///
    (defcong network-equiv equal (in-order-schedule net) 1)
    (verify-guards in-order-schedule
      :hints (("Goal" :in-theory (enable network-p))))
    (local (defrule crock-1
      (implies (and (omap::assoc x m) (not (omap::assoc x (omap::tail m))))
              (equal (omap::head-key m) x))))

    ; The scheduler is weakly fair
    (defrule in-order-scheduler-weakly-fair-when-runnable
      (implies 
        (and (pid-p pid)
             (network-p net)
             (omap::assoc pid net)
             (runnable? net pid))
        (not (equal (in-order-schedule net) '(:stutter))))
      :enable (runnable? proc-runnable?)
      :hints (("Subgoal *1/3" :use (:instance crock-1 (x pid) (m net)))))
    
    (defrule in-order-scheduler-weakly-fair-when-deliverable
      (implies 
        (and (pid-p pid) (pid-p dst)
             (network-p net)
             (omap::assoc pid net)
             (has-message-for-dst? net pid dst))
        (not (equal (in-order-schedule net) '(:stutter))))
      :enable (has-message-for-dst? proc-has-message-for-dst? proc->outbox)
      :hints (("Subgoal *1/5" :use (:instance crock-1 (x pid) (m net)))
              ("Subgoal *1/6" :use ((:instance crock-1 (x pid) (m net))))))
    
    ; The scheduler is correct
    (defrule in-order-scheduler-correct-of-run
      (implies
        (and (network-p net) (equal (scheduling-kind (in-order-schedule net)) :run))
        (runnable? net (scheduling-run->p (in-order-schedule net)))))
    
    (defrule in-order-scheduler-correct-of-deliver
      (implies
        (and (network-p net) (equal (scheduling-kind (in-order-schedule net)) :deliver))
        (has-message-for-dst?
          net
          (scheduling-deliver->p1 (in-order-schedule net))
          (scheduling-deliver->p2 (in-order-schedule net))))
      :enable (has-message-for-dst? proc-has-message-for-dst?)))

(defattach
  (schedule in-order-schedule)
  :hints (("Goal" :use (:instance in-order-scheduler-weakly-fair-when-deliverable))))