(in-package "ACL2")

; I cheat here and load props first, 
; so that it cerify in parallel.
(include-book "props")
(include-book "deliver")
(include-book "run")

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

(defrule inv-all-of-erl-runner
  (implies
    (and (network-p net) (inv-all net))
    (inv-all (erl-runner net fuel)))
  :enable erl-runner)
