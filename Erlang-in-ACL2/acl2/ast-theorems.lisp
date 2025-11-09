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

; Sub-nodes of a tuple expression are also expressions.
(defrule expr-tuple-ensures
  (implies (and (expr-p x) (equal (node-kind x) :tuple))
           (expr-list-p (node-tuple->lst x)))
  :enable expr-p)

(defrule expr-tuple-ensures
  (implies (and (expr-list-p lst))
           (expr-p (node-tuple lst)))
  :expand (expr-p (node-tuple lst)))



(defrule hmwhat-1
  (implies (and (consp lst) (expr-list-p lst))
           (node-p (car lst)))
  :expand (expr-list-p lst))

(defrule hmwhat-2
  (implies (and (null lst) (expr-list-p lst))
           (node-list-p lst)))

(defrule hmwhat-3
  (implies (and (consp lst) (expr-list-p lst))
           (expr-list-p (cdr lst)))
  :expand (expr-list-p lst))


(defrule hmwhat-4
  (implies (expr-list-p lst)
           (node-list-p lst))
  :enable (expr-list-p node-list-p expr-p))