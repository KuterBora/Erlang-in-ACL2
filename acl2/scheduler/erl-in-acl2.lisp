(in-package "ACL2")
(include-book "abstract")

; todo:
; verify guards
; remove the inbox distinction
; refactor duplicates

(define proc-receive ((proc proc-p))
  :returns (rp proc-p)
  :verify-guards nil
  :measure (len (proc->inbox-new (proc-fix proc)))
  (b* ((proc (proc-fix proc))
       
       ; If there are no more messages to try, the process is blocked.
       ((unless (proc->inbox-new proc))
        (b* ((- (cw "Pid: ~x0 failed to receive, it is now blocked.~%~%" (proc->pid proc))))
            (change-proc proc :ps :blocked)))

       (- (cw "Attempting to receive message ~x0~%" (car (proc->inbox-new proc))))
       (rs (update-erl-state->in (proc->s proc) (car (proc->inbox-new proc))))
       (rs (apply-k rs (proc->klst proc))))
      (cond
        ((equal (erl-val-kind (erl-state->in rs)) :blocked)
         (b* ((- (cw "Could not receive message. Trying next one.~%")))
              (proc-receive
                (change-proc
                   proc
                     :inbox-new (cdr (proc->inbox-new proc))
                     :inbox-tried (append (proc->inbox-tried proc) (list (car (proc->inbox-new proc))))))))
        ((equal (erl-val-kind (erl-state->in rs)) :receive)
         (b* ((- (cw "Received the message and ran till the next receive.~%~%")))
             (change-proc
               proc
                 :s rs
                 :ps :receive
                 :inbox-new (append (proc->inbox-tried proc) (cdr (proc->inbox-new proc)))
                 :inbox-tried nil
                 :klst (erl-val-receive->klst (erl-state->in rs)))))
        (t (b* ((- (cw "Process received a message and terminated with the value: ~x0~%~%" (erl-state->in rs))))
                (change-proc
                   proc
                     :s rs
                     :ps :terminated
                     :inbox-new (append (proc->inbox-tried proc) (cdr (proc->inbox-new proc)))
                     :inbox-tried nil))))))

(define erl-step ((net network-p))
  ;returns (rnet network-p)
  ;guard-hints (("Goal" :in-theory (enable network-p network-fix)))
  :verify-guards nil
  (b* ((net (network-fix net))
       ((if (terminated? net)) net)
       (sc (schedule net))
       (- (cw "Scheduler decision: ~x0.~%~%" sc)))
    (scheduling-case sc
      (:stutter net)
      (:run
        (b* ((- (cw "Running: ~x0.~%" (scheduling-run->p sc)))
             (pid (scheduling-run->p sc))
             (proc (omap::lookup pid net))
             (s (proc->s proc))
             (klst (proc->klst proc)))
            (if (equal (proc->ps proc) :idle)

                ; The program is running for the first time.
                (b* ((- (cw "Evaluating ~x0 for the first time. ~%" pid))
                     (ns (apply-k s klst)))
                    (if (equal (erl-val-kind (erl-state->in ns)) :receive)
                        ; The program ran until a receive was encountered.
                        (b*
                          ((- (cw "Evaluated ~x0 till the next receive. ~%~%" pid)))
                          (omap::update
                            pid
                            (change-proc proc
                                :s ns
                                :ps :receive
                                :klst (erl-val-receive->klst (erl-state->in ns)))
                            net))
                        ; The program terminated.
                        (b*
                          ((- (cw "~x0 terminated. ~%~%" pid)))
                          (omap::update
                            pid
                            (change-proc proc
                              :s ns
                              :ps :terminated
                             :klst nil)
                            net))))
                ; The program is attempting to receive.
                (b* ((- (cw "~x0 is trying to receive. ~%" pid)))
                    (omap::update
                      pid
                      (proc-receive proc)
                      net)))))
        (:deliver
          (b* ((src (scheduling-deliver->p1 sc))
               (dst (scheduling-deliver->p2 sc))

               (psrc (omap::lookup src net))
               (ssrc (proc->s psrc))

               (- (cw "Delivering message from: ~x0 to ~x1~%" src dst))
 
               ((unless (omap::assoc dst net))
                (b* ((- (cw "Destination: ~x0 does not exist.~%" dst)))
                     (omap::update
                       src
                       (change-proc psrc
                         :s  (update-erl-state->outbox
                               ssrc
                               (omap::update
                                 dst
                                 (cdr (omap::lookup dst (erl-state->outbox ssrc)))
                                 (erl-state->outbox ssrc))))
                       net)))
              
               (pdst (omap::lookup dst net))

               (- (cw "Message delivered from: ~x0 to ~x1.~%~%" src dst)))
              (if (equal (proc->ps pdst) :blocked)
                  (b*
                    ((- (cw "Dst: ~x0 is now unblocked.~%" dst)))
                    (omap::update
                      dst
                      (change-proc pdst
                        :inbox-new (append (proc->inbox-new pdst)
                                           (list (car (omap::lookup dst (erl-state->outbox ssrc)))))
                        :ps :receive)
                      (omap::update
                        src
                        (change-proc psrc
                          :s (update-erl-state->outbox
                               ssrc
                               (if (cdr (omap::lookup dst (erl-state->outbox ssrc)))
                                   (omap::update
                                     dst
                                     (cdr (omap::lookup dst (erl-state->outbox ssrc)))
                                     (erl-state->outbox ssrc))
                                   (omap::delete dst (erl-state->outbox ssrc)))))
                        net)))
                  (omap::update
                      dst
                      (change-proc pdst
                        :inbox-new (append (proc->inbox-new pdst)
                                           (list (car (omap::lookup dst (erl-state->outbox ssrc))))))
                      (omap::update
                        src
                        (change-proc psrc
                          :s (update-erl-state->outbox
                               ssrc
                               (if (cdr (omap::lookup dst (erl-state->outbox ssrc)))
                                   (omap::update
                                     dst
                                     (cdr (omap::lookup dst (erl-state->outbox ssrc)))
                                     (erl-state->outbox ssrc))
                                   (omap::delete dst (erl-state->outbox ssrc)))))
                        net))))))))

; TODO
; - guards
; - mbe

; Erlang Runtime --------------------------------------------------------------

; Run the Erlang processes, given the next step by the scheduler.
; TODO: lookup choice variables
(define erl-runner ((net network-p) (fuel natp))
  :measure (nfix fuel)
  :returns (rnet network-p)
  :verify-guards nil
  (b* ((net (network-fix net))
       (fuel (nfix fuel))
       ((if (= fuel 0)) net)
       ((if (terminated? net)) net))
      (erl-runner (erl-step net) (1- fuel))))