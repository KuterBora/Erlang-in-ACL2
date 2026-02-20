(in-package "ACL2")
(include-book "../erl-eval")
(include-book "std/testing/assert-equal" :DIR :SYSTEM)

; This file contains some tests for evaluating if and case clauses

; TODO: 
; This file probably does not have enough tests. Especially for error conditions.


; Erlang If --------------------------------------------------------------------

; If constructor

; if
;   X, Y -> 2 - 1;
;   X > 0 -> 2;
;   false; Y; false -> 3;
;   1 div 0; X == -1 -> 4;
;   true -> 5
; end.
; (make-node-if 
;   :clauses 
;     (list
;       (make-node-clause 
;         :cases nil
;         :guards '(((:var X) (:var Y)))
;         :body '((:binop - (:integer 2) (:integer 1))))
;       (make-node-clause
;         :cases nil
;         :guards '(((:binop > (:var X) (:integer 0))))
;         :body '((:integer 2)))
;       (make-node-clause 
;         :cases nil
;         :guards '(((:atom false)) ((:var Y)) ((:atom false)))
;         :body '((:integer 3)))
;       (make-node-clause 
;         :cases nil                 
;         :guards '(((:binop div (:integer 1) (:integer 0))) 
;                   ((:binop == (:var X) (:integer -1)))) 
;         :body '((:integer 4)))
;       (make-node-clause 
;         :cases nil                 
;         :guards '(((:atom true))) 
;         :body '((:integer 5)))))

(assert-equal 
  (apply-k
    (make-erl-state :bind '((X :atom true) (Y :atom true)))
    (list
      (make-erl-k 
        :fuel 10000 
        :kont 
          (make-kont-expr
            :expr 
              '(:if 
                (((cases)
                  (guards ((:var X) (:var Y)))
                  (body (:binop - (:integer 2) (:integer 1))))
                 ((cases)
                  (guards ((:binop > (:var X) (:integer 0))))
                  (body (:integer 2)))
                 ((cases)
                  (guards ((:atom false))
                          ((:var Y))
                          ((:atom false)))
                  (body (:integer 3)))
                 ((cases)
                  (guards ((:binop div (:integer 1) (:integer 0)))
                          ((:binop == (:var X) (:integer -1))))
                  (body (:integer 4)))
                 ((cases)
                  (guards ((:atom true)))
                  (body (:integer 5)))))))))
  (make-erl-state :in '(:integer 1) :bind '((X :atom true) (Y :atom true))))

(assert-equal 
  (apply-k
    (make-erl-state :bind '((X :integer 1) (Y :atom true)))
    (list
      (make-erl-k 
        :fuel 10000 
        :kont 
          (make-kont-expr
            :expr 
              '(:if 
                (((cases)
                  (guards ((:var X) (:var Y)))
                  (body (:binop - (:integer 2) (:integer 1))))
                 ((cases)
                  (guards ((:binop > (:var X) (:integer 0))))
                  (body (:integer 2)))
                 ((cases)
                  (guards ((:atom false))
                          ((:var Y))
                          ((:atom false)))
                  (body (:integer 3)))
                 ((cases)
                  (guards ((:binop div (:integer 1) (:integer 0)))
                          ((:binop == (:var X) (:integer -1))))
                  (body (:integer 4)))
                 ((cases)
                  (guards ((:atom true)))
                  (body (:integer 5)))))))))
  (make-erl-state :in '(:integer 2) :bind '((X :integer 1) (Y :atom true))))

(assert-equal 
  (apply-k
    (make-erl-state :bind '((X :integer -1) (Y :atom true)))
    (list
      (make-erl-k 
        :fuel 10000 
        :kont 
          (make-kont-expr
            :expr 
              '(:if 
                (((cases)
                  (guards ((:var X) (:var Y)))
                  (body (:binop - (:integer 2) (:integer 1))))
                 ((cases)
                  (guards ((:binop > (:var X) (:integer 0))))
                  (body (:integer 2)))
                 ((cases)
                  (guards ((:atom false))
                          ((:var Y))
                          ((:atom false)))
                  (body (:integer 3)))
                 ((cases)
                  (guards ((:binop div (:integer 1) (:integer 0)))
                          ((:binop == (:var X) (:integer -1))))
                  (body (:integer 4)))
                 ((cases)
                  (guards ((:atom true)))
                  (body (:integer 5)))))))))
  (make-erl-state :in '(:integer 3) :bind '((X :integer -1) (Y :atom true))))

(assert-equal 
  (apply-k
    (make-erl-state :bind '((X :integer -1) (Y :atom false)))
    (list
      (make-erl-k 
        :fuel 10000 
        :kont 
          (make-kont-expr
            :expr 
              '(:if 
                (((cases)
                  (guards ((:var X) (:var Y)))
                  (body (:binop - (:integer 2) (:integer 1))))
                 ((cases)
                  (guards ((:binop > (:var X) (:integer 0))))
                  (body (:integer 2)))
                 ((cases)
                  (guards ((:atom false))
                          ((:var Y))
                          ((:atom false)))
                  (body (:integer 3)))
                 ((cases)
                  (guards ((:binop div (:integer 1) (:integer 0)))
                          ((:binop == (:var X) (:integer -1))))
                  (body (:integer 4)))
                 ((cases)
                  (guards ((:atom true)))
                  (body (:integer 5)))))))))
  (make-erl-state :in '(:integer 4) :bind '((X :integer -1) (Y :atom false))))

(assert-equal 
  (apply-k
    (make-erl-state :bind '((X :integer -2) (Y :atom false)))
    (list
      (make-erl-k 
        :fuel 10000 
        :kont 
          (make-kont-expr
            :expr 
              '(:if 
                (((cases)
                  (guards ((:var X) (:var Y)))
                  (body (:binop - (:integer 2) (:integer 1))))
                 ((cases)
                  (guards ((:binop > (:var X) (:integer 0))))
                  (body (:integer 2)))
                 ((cases)
                  (guards ((:atom false))
                          ((:var Y))
                          ((:atom false)))
                  (body (:integer 3)))
                 ((cases)
                  (guards ((:binop div (:integer 1) (:integer 0)))
                          ((:binop == (:var X) (:integer -1))))
                  (body (:integer 4)))
                 ((cases)
                  (guards ((:atom true)))
                  (body (:integer 5)))))))))
  (make-erl-state :in '(:integer 5) :bind '((X :integer -2) (Y :atom false))))


; Erlang Case ------------------------------------------------------------------

; case X of
;   {One, 2} when One == 1 -> One + 2;
;   {Two, 1 + 1} when Two == 2 -> Two * Two;
;   {Nat, _} when is_integer(Nat), Nat >= 0 -> 'at_least_it_is_nat;
;   {Int, _} when is_integer(Int) -> 'at_least_it_is_int;
;   _ -> 'no_match
; end

; (make-node-case-of
;   :expr '(:var X)
;   :clauses
;     (list
;       (make-node-clause 
;         :cases '((:tuple ((:var One) (:integer 2))))
;         :guards '(((:binop == (:var One) (:integer 1))))
;         :body '((:binop + (:var One) (:integer 2))))
;       (make-node-clause
;         :cases '((:tuple ((:var Two) (:binop + (:integer 1) (:integer 1)))))
;         :guards '(((:binop == (:var Two) (:integer 2))))
;         :body '((:binop * (:var Two) (:var Two))))
;       (make-node-clause
;         :cases '((:tuple ((:var Nat) (:var _))))
;         :guards '(((:call is_integer ((:var Nat))) 
;                    (:binop >= (:var Nat) (:integer 0))))
;         :body '((:atom at_least_it_is_nat)))
;       (make-node-clause
;         :cases '((:tuple ((:var Int) (:var _))))
;         :guards '(((:call is_integer ((:var Int)))))
;         :body '((:atom at_least_it_int)))
;       (make-node-clause
;         :cases '((:var _))            
;         :guards nil 
;         :body '((:atom no_match_at_all)))))

(assert-equal 
  (apply-k
    (make-erl-state :bind '((X :tuple ((:integer 1) (:integer 2)))))
    (list
      (make-erl-k 
        :fuel 10000 
        :kont 
          (make-kont-expr
            :expr
              '(:case-of 
                (:var X)
                (((cases (:tuple ((:var One) (:integer 2))))
                  (guards ((:binop == (:var One) (:integer 1))))
                  (body (:binop + (:var One) (:integer 2))))
                ((cases (:tuple ((:var Two)
                                  (:binop + (:integer 1) (:integer 1)))))
                  (guards ((:binop == (:var Two) (:integer 2))))
                  (body (:binop * (:var Two) (:var Two))))
                ((cases (:tuple ((:var Nat) (:var _))))
                  (guards ((:call is_integer ((:var Nat)))
                            (:binop >= (:var Nat) (:integer 0))))
                  (body (:atom at_least_it_is_nat)))
                ((cases (:tuple ((:var Int) (:var _))))
                  (guards ((:call is_integer ((:var Int)))))
                  (body (:atom at_least_it_int)))
                ((cases (:var _))
                  (guards)
                  (body (:atom no_match_at_all)))))))))
  (make-erl-state 
    :in '(:integer 3) 
    :bind '((One :integer 1)
            (X :tuple ((:integer 1) (:integer 2))))))

(assert-equal 
  (apply-k
    (make-erl-state :bind '((X :tuple ((:integer 2) (:integer 2)))))
    (list
      (make-erl-k 
        :fuel 10000 
        :kont 
          (make-kont-expr
            :expr
              '(:case-of 
                (:var X)
                (((cases (:tuple ((:var One) (:integer 2))))
                  (guards ((:binop == (:var One) (:integer 1))))
                  (body (:binop + (:var One) (:integer 2))))
                ((cases (:tuple ((:var Two)
                                  (:binop + (:integer 1) (:integer 1)))))
                  (guards ((:binop == (:var Two) (:integer 2))))
                  (body (:binop * (:var Two) (:var Two))))
                ((cases (:tuple ((:var Nat) (:var _))))
                  (guards ((:call is_integer ((:var Nat)))
                            (:binop >= (:var Nat) (:integer 0))))
                  (body (:atom at_least_it_is_nat)))
                ((cases (:tuple ((:var Int) (:var _))))
                  (guards ((:call is_integer ((:var Int)))))
                  (body (:atom at_least_it_int)))
                ((cases (:var _))
                  (guards)
                  (body (:atom no_match_at_all)))))))))
  (make-erl-state 
    :in '(:integer 4)
    :bind '((Two :integer 2)
            (X :tuple ((:integer 2) (:integer 2))))))

(assert-equal 
  (apply-k
    (make-erl-state :bind '((X :tuple ((:integer 3) (:atom bogus)))))
    (list
      (make-erl-k 
        :fuel 10000 
        :kont 
          (make-kont-expr
            :expr
              '(:case-of 
                (:var X)
                (((cases (:tuple ((:var One) (:integer 2))))
                  (guards ((:binop == (:var One) (:integer 1))))
                  (body (:binop + (:var One) (:integer 2))))
                ((cases (:tuple ((:var Two)
                                  (:binop + (:integer 1) (:integer 1)))))
                  (guards ((:binop == (:var Two) (:integer 2))))
                  (body (:binop * (:var Two) (:var Two))))
                ((cases (:tuple ((:var Nat) (:var _))))
                  (guards ((:call is_integer ((:var Nat)))
                            (:binop >= (:var Nat) (:integer 0))))
                  (body (:atom at_least_it_is_nat)))
                ((cases (:tuple ((:var Int) (:var _))))
                  (guards ((:call is_integer ((:var Int)))))
                  (body (:atom at_least_it_int)))
                ((cases (:var _))
                  (guards)
                  (body (:atom no_match_at_all)))))))))
  (make-erl-state 
    :in '(:atom at_least_it_is_nat)
    :bind '((Nat :integer 3)
            (X :tuple ((:integer 3) (:atom bogus))))))

(assert-equal 
  (apply-k
    (make-erl-state :bind '((X :tuple ((:integer -1) (:atom bogus)))))
    (list
      (make-erl-k 
        :fuel 10000 
        :kont 
          (make-kont-expr
            :expr
              '(:case-of 
                (:var X)
                (((cases (:tuple ((:var One) (:integer 2))))
                  (guards ((:binop == (:var One) (:integer 1))))
                  (body (:binop + (:var One) (:integer 2))))
                ((cases (:tuple ((:var Two)
                                  (:binop + (:integer 1) (:integer 1)))))
                  (guards ((:binop == (:var Two) (:integer 2))))
                  (body (:binop * (:var Two) (:var Two))))
                ((cases (:tuple ((:var Nat) (:var _))))
                  (guards ((:call is_integer ((:var Nat)))
                            (:binop >= (:var Nat) (:integer 0))))
                  (body (:atom at_least_it_is_nat)))
                ((cases (:tuple ((:var Int) (:var _))))
                  (guards ((:call is_integer ((:var Int)))))
                  (body (:atom at_least_it_is_int)))
                ((cases (:var _))
                  (guards)
                  (body (:atom no_match_at_all)))))))))
  (make-erl-state 
    :in '(:atom at_least_it_is_int)
    :bind '((Int :integer -1)
            (X :tuple ((:integer -1) (:atom bogus))))))

(assert-equal 
  (apply-k
    (make-erl-state :bind '((X :tuple ((:atom bogus) (:atom bogus)))))
    (list
      (make-erl-k 
        :fuel 10000 
        :kont 
          (make-kont-expr
            :expr
              '(:case-of 
                (:var X)
                (((cases (:tuple ((:var One) (:integer 2))))
                  (guards ((:binop == (:var One) (:integer 1))))
                  (body (:binop + (:var One) (:integer 2))))
                ((cases (:tuple ((:var Two)
                                  (:binop + (:integer 1) (:integer 1)))))
                  (guards ((:binop == (:var Two) (:integer 2))))
                  (body (:binop * (:var Two) (:var Two))))
                ((cases (:tuple ((:var Nat) (:var _))))
                  (guards ((:call is_integer ((:var Nat)))
                            (:binop >= (:var Nat) (:integer 0))))
                  (body (:atom at_least_it_is_nat)))
                ((cases (:tuple ((:var Int) (:var _))))
                  (guards ((:call is_integer ((:var Int)))))
                  (body (:atom at_least_it_is_int)))
                ((cases (:var _))
                  (guards)
                  (body (:atom no_match_at_all)))))))))
  (make-erl-state 
    :in '(:atom no_match_at_all)
    :bind '((X :tuple ((:atom bogus) (:atom bogus))))))