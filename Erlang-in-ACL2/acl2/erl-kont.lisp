(in-package "ACL2")
(include-book "erl-ast")
(include-book "erl-value")

; Continuations ----------------------------------------------------------------

(set-induction-depth-limit 1)
(set-well-founded-relation l<)

; Types of continuations that describe the next step of evaluation.
(fty::deftagsum kont
    ; Erlang expression to be evaluated.
    (:expr ((expr expr-p)))

    ; List of Erlang expression to be evaluated in order.
    (:exprs ((exprs expr-list-p)))

    ; Continue after the car of a list has been evaluated.
    (:cons 
      ((cdr-expr expr-p)
       (bind-0 bind-p)))
    
    ; Continue after the cdr of a list has been evaluated.
    (:cons-merge
      ((car-val erl-val-p)
       (car-bind bind-p)))
    
    ; Continue after the first element of a tuple has been evaluated.
    (:tuple
      ((t-rem expr-p)
       (bind-0 bind-p)))
    
    ; Continue after the rest of a tuple has been evaluated.
    (:tuple-merge
      ((t-hd erl-val-p)
       (t-bind bind-p)))

    ; Continue after the operand of an unop has been evaluated.
    (:unop ((op erl-unop-p)))

    ; Continue after the first operand of a binop has been evaluated.
    (:binop-expr1
      ((op erl-binop-p)
       (right expr-p)
       (bind-0 bind-p)))
    ; Continue after the second operand of a binop has been evaluated.
    (:binop-expr2 
      ((op erl-binop-p)
       (val erl-val-p)
       (left-bind bind-p))))

; A continutaion that is paired with a fuel that limits how many times
; the continuation can expand during evaluation.
(fty::defprod erl-k
    ((fuel natp)
     (kont kont-p)))

; List of erl-k
(fty::deflist erl-klst
  :elt-type erl-k
  :true-listp t)

(set-well-founded-relation o<)