(in-package "ACL2")
(include-book "erl-eval")
(include-book "std/testing/assert-equal" :DIR :SYSTEM)

; BIFs -------------------------------------------------------------------------

(make-node-call :fn 'is_integer :args '((:integer 1)))
(make-node-call 
  :fn 'element 
  :args '((:integer 2) (:tuple ((:atom one) (:atom two) (:atom three)))))

(assert-equal
  (apply-k 
    (make-erl-state)
    (list 
      (make-erl-k 
      :fuel 10000 
      :kont (make-kont-expr
              :expr '(:call is_integer ((:integer 1)))))))
  (make-erl-state :in '(:atom true)))

(assert-equal
  (apply-k 
    (make-erl-state)
    (list 
      (make-erl-k 
      :fuel 10000 
      :kont (make-kont-expr
              :expr '(:call element
                            ((:integer 2)
                             (:tuple ((:atom one)
                                      (:atom two)
                                      (:atom three)))))))))
  (make-erl-state :in '(:atom two)))


; Simple Local Function --------------------------------------------------------




; Simple Remote Function -------------------------------------------------------
; Recursive Local Function -----------------------------------------------------
; Recursive Remote Function ----------------------------------------------------


(assert-equal
  (apply-k 
    (make-erl-state)
    (list 
      (make-erl-k 
        :fuel 10000 
        :kont (make-kont-exprs
                :exprs '((:match (:var X) (:integer 3))
                         (:match (:var Y) (:binop + (:var X) (:integer 2)))
                         (:binop * (:var Y) (:var X)))))))
  (make-erl-state :in '(:integer 15) 
                  :bind '((X :integer 3) (Y :integer 5))))