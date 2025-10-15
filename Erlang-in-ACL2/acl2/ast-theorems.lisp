(in-package "ACL2")
(include-book "erl-ast")
(include-book "erl-value")

; AST Theorems -----------------------------------------------------------------

(set-induction-depth-limit 1)

; Sub-nodes of a binop expression are also expressions.
(defrule expr-binop-ensures
  (implies (and (expr-p x) (equal (node-kind x) :binop))
           (and (erl-binop-p (node-binop->op x))
                (expr-p (node-binop->left x))
                (expr-p (node-binop->right x))))
  :enable expr-p)
