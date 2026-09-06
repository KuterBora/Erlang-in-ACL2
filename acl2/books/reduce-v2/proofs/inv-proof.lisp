(in-package "ACL2")
(include-book "deliver")
(include-book "run")

; the goal:

(defrule inv-of-erl-step-of-assoc
  (implies
    (and (network-p net) (inv-all net)
         (omap::assoc pid (erl-step net)))
    (inv pid (erl-step net)))
  :use ((:instance inv-of-erl-step-of-run)
        (:instance inv-of-erl-step-of-deliver))
  :disable
    (inv-of-erl-step-of-run
     inv-of-erl-step-of-deliver))

(defrule inv-all0-of-erl-step-general
  (implies
    (and (network-p net) (network-p sub) (inv-all net)
         (omap::submap sub (erl-step net)))
    (inv-all0 sub (erl-step net)))
  :enable inv-all0)

(defrule inv-all-of-erl-step
  (implies
    (and (network-p net) (inv-all net))
    (inv-all (erl-step net)))
  :enable inv-all)



(defrule terminated-of-inv
  (implies
    (and
      (inv-all net) (terminated? net)
      (pid-p pid) (omap::assoc pid net))
    (equal (proc->ps (omap::lookup pid net)) :terminated)))


(defrule root-of-terminated-when-inv
  (and (network-p net)
       (inv-all net) (termianted? net)
       (pid-p pid) (omap::assoc pid net)
       (root-p (omap::lookup pid net)))
  (equal
    (erl-state->in (proc->s (omap::lookup pid net)))
    (sum (omap::size net))))


; inv of erl-runner
; later if time, show that erl-runner will terminate



