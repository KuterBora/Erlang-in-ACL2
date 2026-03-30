
;; ACL2 sum-n
; (define sum-n ((n natp))
;   (b* ((n (nfix n))
;        ((if (= n 0)) 0))
;       (+ n (sum-n (1- n)))))

; Commenting this out, as it introduces rewrite rules that we do not want yet.
; (defrule sum-n-formula
;   (implies (natp n)
;     (equal (sum-n n) (/ (* n (+ n 1)) 2)))
;   :enable (sum-n))