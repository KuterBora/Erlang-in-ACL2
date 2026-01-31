(in-package "ACL2")
(include-book "erl-ast")
(include-book "erl-value")

(set-induction-depth-limit 1)

; Continuations ----------------------------------------------------------------

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
       (left-bind bind-p)))
    
    ; Continue after the rhs of the match has been evaluated.
    (:match ((lhs pattern-p)))

    ; Continue after the expression of the case had been evaluated.
    ; The expression would be `X` in `case X of ... end`
    (:case-of ((clauses erl-clause-list-p)))

    ; List of function arguments to be evaluated
    (:function-args-start ((args expr-list-p)))

    ; Continue function argument evaluation. Each argument in rest needs to be
    ; evaluated and moved to done.
    (:function-args ((done erl-vlst-p) (rest expr-list-p)))

    ; Continue after argument evaluation is finished by calling the function.
    (:local-call ((call symbolp)))
    (:remote-call ((module symbolp) (call symbolp)))

    ; Continue after the function returns.
    (:function-return ((bind bind-p) (module symbolp))))

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