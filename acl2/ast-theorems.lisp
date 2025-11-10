(in-package "ACL2")
(include-book "erl-ast")

; AST Theorems -----------------------------------------------------------------

(set-induction-depth-limit 1)


; Sub-nodes of a cons expression are also expressions.
(defrule expr-cons-ensures
  (implies (and (expr-p x) (equal (node-kind x) :cons))
           (and (expr-p (node-cons->hd x))
                (expr-p (node-cons->tl x))))
  :enable expr-p)

; Sub-nodes of a tuple expression are also expressions.
(defrule expr-tuple-ensures
  (implies (and (expr-p x) (equal (node-kind x) :tuple))
           (expr-list-p (node-tuple->lst x)))
  :enable expr-p)

; Creating a tuple with a list of expressions will produce and expression.
(defrule expr-tuple-lst-ensures
  (implies (expr-list-p lst)
           (expr-p (node-tuple lst)))
  :enable expr-p)
  
; Sub-nodes of a binop expression are also expressions.
(defrule expr-binop-ensures
  (implies (and (expr-p x) (equal (node-kind x) :binop))
           (and (erl-binop-p (node-binop->op x))
                (expr-p (node-binop->left x))
                (expr-p (node-binop->right x))))
  :enable expr-p)

; Sub-node of an unop expression is also an expression.
(defrule expr-unop-ensures
  (implies (and (expr-p x) (equal (node-kind x) :unop))
           (and (erl-unop-p (node-unop->op x))
                (expr-p (node-unop->expr x))))
  :enable expr-p)