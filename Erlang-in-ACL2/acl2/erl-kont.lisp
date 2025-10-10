(in-package "ACL2")
(include-book "centaur/fty/top" :DIR :SYSTEM)
(include-book "std/util/top" :DIR :SYSTEM)
(include-book "erl-ast")
(include-book "erl-value")

; Continuations ----------------------------------------------------------------

(set-induction-depth-limit 1)
(set-well-founded-relation l<)

; Types of continuations that describe the next step of evaluation.
(fty::deftagsum kont
    ; Erlang expression to be evaluated.
    (:expr ((expr expr-p)))

    ; Continue after the first operand of a binop has been evaluated.
    (:binop-expr1 (
      (op erl-binop-p)
      (right expr-p)
      (bind0 bind-p)))
    ; Continue after the second operand of a binop has been evaluated.
    (:binop-expr2 (
      (op erl-binop-p)
      (val erl-val-p)
      (bindL bind-p))))

; A continutaion that is paired with a fuel that limits how many times
; the continuation can expand during evaluation.
(fty::defprod erl-k
    ((fuel natp)
     (kont kont-p)))

(fty::deflist erl-klst
  :elt-type erl-k
  :true-listp t)

(set-well-founded-relation o<)