(in-package "ACL2")
(include-book "inv-proof")


(defrule root-of-terminated-when-inv
  (and (network-p net)
       (inv-all net) (termianted? net)
       (pid-p pid) (omap::assoc pid net)
       (root-p (omap::lookup pid net)))
  (equal
    (erl-state->in (proc->s (omap::lookup pid net)))
    (sum (omap::size net))))

; TODO: inv of create-wtree


; function over indices

; TODO: later if I have time, show that erl-runner will terminate
;       given some fairness conditions.