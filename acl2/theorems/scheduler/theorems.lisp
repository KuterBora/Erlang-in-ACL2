(in-package "ACL2")
(include-book "../../scheduler/top")

; For now, I am writing theorems related to networks and
; the scheduler in this file.

(defrule erl-step-when-terminated
  (implies
    (and (network-p net) (terminated? net))
    (equal (erl-step net) net))
  :enable erl-step)

(defrule erl-step-when-stutter
  (implies
    (and (network-p net)
         (equal (scheduling-kind (schedule net)) :stutter))
    (equal (erl-step net) net))
  :enable erl-step)