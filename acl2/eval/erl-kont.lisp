(in-package "ACL2")
(include-book "erl-ast")
(include-book "erl-value")

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
    
    ; Construct a tuple after all of its elements have been evaluated.
    (:tuple ())

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

    ; Continue after argument evaluation is finished by calling the function.
    (:local-call ((call symbolp)))
    (:remote-call ((module symbolp) (call symbolp)))
    
    ; When there is a call to an anonymous function, first evaluate the fun expression,
    ; then the arguments, and finally the clauses.
    (:fun-call-args ((args expr-p)))
    (:fun-call ((fun erl-val-p)))

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

(defcong erl-klst-equiv equal (consp kl) 1
  :hints(("Goal" :in-theory (enable erl-klst-fix))))

(set-well-founded-relation o<)