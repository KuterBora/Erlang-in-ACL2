(in-package "ACL2")
(include-book "erl-eval")
(include-book "std/testing/assert-equal" :DIR :SYSTEM)

(set-induction-depth-limit 1)

; Erlang If --------------------------------------------------------------------

; If constructor

; if
;   X, Y -> 
;     A = 2,
;     A - 1;
;   X ->
;     A = 2;
;   Y ->
;     A = 6,
;     A div 2;
;   true -> A = 4
; end.
(assert-equal
  (make-node-if 
    :clauses 
      (list
        (make-node-clause 
          :cases nil 
          :guards (list '(:var X) '(:var Y))
          :body (list '(:match (:var A) (:integer 2))
                      '(:binop - (:var A) (:integer 1))))
        (make-node-clause
          :cases nil 
          :guards (list '(:var X))
          :body (list '(:match (:var A) (:integer 2))))
        (make-node-clause 
          :cases nil 
          :guards (list '(:var Y))
          :body (list '(:match (:var A) (:integer 6))
                      '(:binop div (:var A) (:integer 2))))
        (make-node-clause 
          :cases nil                 
          :guards (list '(:atom true)) 
          :body (list '(:match (:var A) (:integer 3))))))
    '(:if (((cases)
            (guards (:var X) (:var Y))
            (body (:match (:var A) (:integer 2))
                  (:binop - (:var A) (:integer 1))))
            ((cases)
            (guards (:var X))
            (body (:match (:var A) (:integer 2))))
            ((cases)
            (guards (:var Y))
            (body (:match (:var A) (:integer 6))
                  (:binop div (:var A) (:integer 2))))
            ((cases)
            (guards (:atom true))
            (body (:match (:var A) (:integer 4)))))))


(assert-equal
  (apply-k 
    (make-erl-state :bind '((X :atom true) (Y :atom true)))
    (list
      (make-erl-k 
        :fuel 10000 
        :kont (make-kont-expr
                :expr 
                  '(:if (((cases)
                          (guards (:var X) (:var Y))
                          (body (:match (:var A) (:integer 2))
                                (:binop - (:var A) (:integer 1))))
                          ((cases)
                          (guards (:var X))
                          (body (:match (:var A) (:integer 2))))
                          ((cases)
                          (guards (:var Y))
                          (body (:match (:var A) (:integer 6))
                                (:binop div (:var A) (:integer 2))))
                          ((cases)
                          (guards (:atom true))
                          (body (:match (:var A) (:integer 4))))))))))
  (make-erl-state :in '(:integer 1) 
                  :bind '((A :integer 2) (X :atom true) (Y :atom true))))

(assert-equal
  (apply-k 
    (make-erl-state :bind '((X :atom true) (Y :atom false)))
    (list
      (make-erl-k 
        :fuel 10000 
        :kont (make-kont-expr
                :expr 
                  '(:if (((cases)
                          (guards (:var X) (:var Y))
                          (body (:match (:var A) (:integer 2))
                                (:binop - (:var A) (:integer 1))))
                          ((cases)
                          (guards (:var X))
                          (body (:match (:var A) (:integer 2))))
                          ((cases)
                          (guards (:var Y))
                          (body (:match (:var A) (:integer 6))
                                (:binop div (:var A) (:integer 2))))
                          ((cases)
                          (guards (:atom true))
                          (body (:match (:var A) (:integer 4))))))))))
  (make-erl-state :in '(:integer 2) 
                  :bind '((A :integer 2) (X :atom true) (Y :atom false))))

(assert-equal
  (apply-k 
    (make-erl-state :bind '((X :atom false) (Y :atom true)))
    (list
      (make-erl-k 
        :fuel 10000 
        :kont (make-kont-expr
                :expr 
                  '(:if (((cases)
                          (guards (:var X) (:var Y))
                          (body (:match (:var A) (:integer 2))
                                (:binop - (:var A) (:integer 1))))
                          ((cases)
                          (guards (:var X))
                          (body (:match (:var A) (:integer 2))))
                          ((cases)
                          (guards (:var Y))
                          (body (:match (:var A) (:integer 6))
                                (:binop div (:var A) (:integer 2))))
                          ((cases)
                          (guards (:atom true))
                          (body (:match (:var A) (:integer 4))))))))))
  (make-erl-state :in '(:integer 3) 
                  :bind '((A :integer 6) (X :atom false) (Y :atom true))))

(assert-equal
  (apply-k 
    (make-erl-state :bind '((X :atom false) (Y :atom false)))
    (list
      (make-erl-k 
        :fuel 10000 
        :kont (make-kont-expr
                :expr 
                  '(:if (((cases)
                          (guards (:var X) (:var Y))
                          (body (:match (:var A) (:integer 2))
                                (:binop - (:var A) (:integer 1))))
                          ((cases)
                          (guards (:var X))
                          (body (:match (:var A) (:integer 2))))
                          ((cases)
                          (guards (:var Y))
                          (body (:match (:var A) (:integer 6))
                                (:binop div (:var A) (:integer 2))))
                          ((cases)
                          (guards (:atom true))
                          (body (:match (:var A) (:integer 4))))))))))
  (make-erl-state :in '(:integer 4) 
                  :bind '((A :integer 4) (X :atom false) (Y :atom false))))


; Erlang Case ------------------------------------------------------------------


; Erlang Catch -----------------------------------------------------------------


; Erlang Try Catch -------------------------------------------------------------


