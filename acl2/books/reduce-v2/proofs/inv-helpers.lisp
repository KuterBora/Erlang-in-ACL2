(in-package "ACL2")
(include-book "util")

(set-induction-depth-limit 1)

; Helpers for the reduce invariant.


; Received Messages Well Formed  ----------------------------------------------
; Outbox Utility --------------------------------------------------------------


; forall messages in inbox
; the sender exists in cpids and net,
; the sender is terminated and has drained its outbox,
; the received message has the same value as the terminated
; process' value,
; and no two messages have the same sender, which is enforced by
; dropping each sender from cpids as it goes.
(define received-messages-wf
  ((inbox erl-vlst-p) (cpids erl-vlst-p) (net network-p))
  :returns (r booleanp)
  :measure (acl2-count (erl-vlst-fix inbox))
  (b* ((inbox (erl-vlst-fix inbox))
       (cpids (erl-vlst-fix cpids))
       (net (network-fix net))
       ((unless inbox) t)
       (m (car inbox))
       ((unless (equal (erl-val-kind m) :tuple)) nil)
       (lst (erl-val-tuple->lst m))
       ; The message is in the form {sender, value}.
       ((unless (equal (len lst) 2)) nil)
       (sender (car lst))
       (val (cadr lst))
       ; the sender exists
       ((unless (member-equal sender cpids)) nil)
       ((unless (omap::assoc sender net)) nil)
       (sproc (omap::lookup sender net))
       ; the sender must have terminated
       ((unless (equal (proc->ps sproc) :terminated)) nil)
       ; and the sender must have already sent its message,
       ; else there would be duplicates.
       ((unless (outbox-emptyp (proc->outbox sproc))) nil)
       ; the sender must have sent its own value
       ; which will be equal to its sum-range.
       (sval (erl-state->in (proc->s sproc)))
       ((unless (equal sval val)) nil))
      ; Ensure that no two messages have arrived from the same sender
      ; by dropping it from cpids.
      (received-messages-wf (cdr inbox) (remove-equal sender cpids) net))
  ///
    (defcong erl-vlst-equiv equal (received-messages-wf x y z) 1
      :hints (("Goal" :expand ((received-messages-wf x y z)
                               (received-messages-wf x-equiv y z)))))
    (defcong erl-vlst-equiv equal (received-messages-wf x y z) 2
      :hints (("Goal" :expand ((received-messages-wf x y z)
                               (received-messages-wf x y-equiv z)))))
    (defcong network-equiv equal (received-messages-wf x y z) 3
      :hints (("Goal" :expand ((received-messages-wf x y z)
                               (received-messages-wf x y z-equiv))))))
