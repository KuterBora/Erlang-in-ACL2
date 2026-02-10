(in-package "ACL2")
(include-book "erl-eval")
(include-book "std/testing/assert-equal" :DIR :SYSTEM)


; Basic Anonymous Function -----------------------------------------------------

(assert-equal
  (apply-k 
    (make-erl-state) 
    (list 
      (make-erl-k 
        :fuel 10000 
        :kont 
          (make-kont-exprs 
            :exprs 
              '((:match 
                  (:var F) 
                  (:fun (((cases (:var X)) 
                          (guards) 
                          (body (:binop + (:var X) (:integer 1)))))))
                (:fun-call (:var F) ((:integer 1))))))))

  (update-erl-state->in-bind
    (make-erl-state)
    '(:integer 2)
    (omap::update
      'F 
      '(:fun 
        fun 
        1 
        (((cases (:var X)) (guards) (body (:binop + (:var X) (:integer 1)))))
        nil
        local)
      nil)))


; Remote Anonymous Function ----------------------------------------------------
; Recursive Anonymous Function -------------------------------------------------
; Remote Anonymous -------------------------------------------------------------