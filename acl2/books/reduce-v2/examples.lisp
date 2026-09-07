; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "wtree/create-wtree/top")


; helper to print the leaf values.
(local (define print-omap-values ((n network-p))
  :measure (acl2-count (network-fix n))
  (b* ((n (network-fix n))
       ((if (omap::emptyp n)) 'ok)
       (val (erl-state->in (proc->s (omap::head-val n))))
       (- (cw "~x0~%" val)))
    (print-omap-values (omap::tail n)))))


; Reduce network with 10 processes.
; Run the processes for 40 steps and print the results.
; Remark: index starts at 0, so this one is a sum until n-1
#| 
  (print-omap-values (erl-runner (create-wtree 10) 40))
|#


; Reduce network with 100 processes.
; Run the processes for 400 steps and print the results.
; Remark: index starts at 0, so this one is a sum until n-1
#| 
  (print-omap-values (erl-runner (create-wtree 100) 400))
|#

; Reduce network with 1000 processes.
; Run the processes for 4000 steps and print the results.
; Remarks:
; - index starts at 0, so this one is a sum until n-1
; - there are a lot of processes, so it is better to
;   just print the head.
#|
  (erl-state->in
    (proc->s
        (omap::head-val
            (erl-runner (create-wtree 1000) 4000))))
|#