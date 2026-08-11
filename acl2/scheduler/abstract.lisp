(in-package "ACL2")
(include-book "proc")
(include-book "std/omaps/extensionality" :dir :system)

(set-induction-depth-limit 1)

; Possible Scheduling Steps ---------------------------------------------------

(fty::deftagsum scheduling
  (:deliver ((p1 pid-p) (p2 pid-p)))
  (:run ((p pid-p)))
  (:stutter ()))


; Weakly Fair Abstract Scheduler ----------------------------------------------

(encapsulate

  (((schedule * ) => *))

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
  
  (defrule crock-2
    (implies (network-p m) (network-p (omap::tail m)))
    :enable network-p)
  
  (defrule crock-3
    (implies (and (network-p m) (pid-p x) (omap::assoc x (omap::tail m)))
             (equal (omap::lookup x m)
                    (omap::lookup x (omap::tail m))))
    :enable (network-p network-gen-p)

    :use (:instance omap::lookup-of-tail-when-assoc-tail
            (key x) (map m)))

  (defrule scheduler-weakly-fair-when-runnable
    (implies 
      (and (pid-p pid)
           (network-p net)
           (omap::assoc pid net)
           (runnable? net pid))
      (not (equal (schedule net) (make-scheduling-stutter))))
    :enable (schedule runnable? proc-runnable?)
    :hints (("Subgoal *1/5" :use (:instance crock-1 (x pid) (m net)))))
  
  (defrule scheduler-weakly-fair-when-has-message
    (implies 
      (and (pid-p pid) (pid-p dst)
           (network-p net)
           (omap::assoc pid net)
           (has-message-for-dst? net pid dst))
      (not (equal (schedule net) (make-scheduling-stutter))))
    :enable (schedule has-message-for-dst? proc-has-message-for-dst? proc->outbox)
    :hints (("Subgoal *1/5" :use (:instance crock-1 (x pid) (m net)))
            ("Subgoal *1/6" :use ((:instance crock-1 (x pid) (m net))))))
  
  
  ; Theorems
  (defrule return-type-of-schedule-step
    (scheduler-step-p (schedule-step p)))
  (defrule return-type-of-schedule-proc
    (implies (and (network-p net) (not (terminated? net))) 
             (pid-p (schedule-proc net)))
    :enable (terminated? runnable?))
  (defrule return-type-of-schedule-src
    (implies (and (network-p net) (network-has-message? net))
             (pid-p (schedule-src net)))
    :enable (has-message? network-has-message?))
  (defrule return-type-of-schedule-dst
    (implies (and (proc-p src) (has-message? src))
             (pid-p (schedule-dst src)))
    :enable has-message?)
  
  ; schedule-proc
  (defrule scheduled-pid-is-in-the-network
    (implies
      (and (network-p net) (not (terminated? net))) 
      (omap::assoc (schedule-proc net) net))
    :enable (terminated? runnable?))
  
  (local (defrule scheduled-pid-is-a-runnable-proc-tail
    (implies
      (and (network-p net) (not (terminated? net)) 
           (omap::assoc (schedule-proc net) (omap::tail net))) 
      (runnable? (omap::lookup (schedule-proc net) net)))
    :enable (terminated? runnable? omap::lookup)
    :induct (terminated? net)))
  
  (local (defrule scheduled-pid-is-in-the-network-head
    (implies
      (and (network-p net) (not (terminated? net)) 
           (not (omap::assoc (schedule-proc net) (omap::tail net)))) 
      (equal (omap::head-key net) (schedule-proc net)))
    :enable (terminated? runnable? omap::lookup)
    :induct (terminated? net)))
  
  (local (defrule scheduled-pid-is-a-runnable-proc-head
    (implies
      (and (network-p net) (not (terminated? net)) 
           (not (omap::assoc (schedule-proc net) (omap::tail net)))) 
      (runnable? (omap::lookup (schedule-proc net) net)))
    :enable (terminated? runnable? omap::lookup)
    :induct (terminated? net)))
  
  (defrule scheduled-pid-is-a-runnable-proc
    (implies
      (and (network-p net) (not (terminated? net))) 
      (runnable? (omap::lookup (schedule-proc net) net)))
    :cases ((omap::assoc (schedule-proc net) (omap::tail net)))
    :disable schedule-proc)
  
  ; schedule-src
  (defrule scheduled-src-is-in-the-network
    (implies
      (and (network-p net) (network-has-message? net)) 
      (omap::assoc (schedule-src net) net))
    :enable (network-has-message? has-message?))
  
  (local (defrule scheduled-src-has-a-message-tail
    (implies
      (and (network-p net) (network-has-message? net) 
           (omap::assoc (schedule-src net) (omap::tail net))) 
      (has-message? (omap::lookup (schedule-src net) net)))
    :enable (network-has-message? has-message? omap::lookup)
    :induct (network-has-message? net)))
  
  (local (defrule scheduled-src-is-in-the-network-head
    (implies
      (and (network-p net) (network-has-message? net)
           (not (omap::assoc (schedule-src net) (omap::tail net)))) 
      (equal (omap::head-key net) (schedule-src net)))
    :enable (network-has-message? has-message? omap::lookup)
    :induct (network-has-message? net)))
  
  (local (defrule scheduled-src-has-a-message-head
    (implies
      (and (network-p net) (network-has-message? net)
           (not (omap::assoc (schedule-src net) (omap::tail net)))) 
      (has-message? (omap::lookup (schedule-src net) net)))
    :enable (network-has-message? has-message? omap::lookup)
    :induct (network-has-message? net)))
  
  (defrule scheduled-src-has-a-message
    (implies
      (and (network-p net) (network-has-message? net))
      (has-message? (omap::lookup (schedule-src net) net)))
    :cases ((omap::assoc (schedule-src net) (omap::tail net)))
    :disable schedule-src)
  
  ; schedule-dst
  (defrule src-has-message-for-scheduled-dst
    (implies
      (and (proc-p p) (has-message? p)) 
      (omap::assoc (schedule-dst p) (erl-state->outbox (proc->es p))))
    :enable has-message?))