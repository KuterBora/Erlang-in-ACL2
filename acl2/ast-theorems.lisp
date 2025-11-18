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

; Sub-nodes of a cons pattern are also patterns.
(defrule pattern-cons-ensures
  (implies (and (pattern-p x) (equal (node-kind x) :cons))
           (and (pattern-p (node-cons->hd x))
                (pattern-p (node-cons->tl x))))
  :enable (arithm-expr-p pattern-p))

; Sub-nodes of a cons guard are also guards.
(defrule guard-cons-ensures
  (implies (and (guard-expr-p x) (equal (node-kind x) :cons))
           (and (guard-expr-p (node-cons->hd x))
                (guard-expr-p (node-cons->tl x))))
  :enable guard-expr-p)

; Sub-nodes of a tuple expression are also expressions.
(defrule expr-tuple-ensures
  (implies (and (expr-p x) (equal (node-kind x) :tuple))
           (expr-list-p (node-tuple->lst x)))
  :enable expr-p)

; Sub-nodes of a tuple pattern are also patterns.
(defrule pattern-tuple-ensures
  (implies (and (pattern-p x) (equal (node-kind x) :tuple))
           (pattern-list-p (node-tuple->lst x)))
  :enable (arithm-expr-p pattern-p))

; Sub-nodes of a tuple guard are also guards.
(defrule guard-tuple-ensures
  (implies (and (guard-expr-p x) (equal (node-kind x) :tuple))
           (guard-expr-list-p (node-tuple->lst x)))
  :enable guard-expr-p)

; Creating a tuple with a list of expressions will produce an expression.
(defrule expr-tuple-lst-ensures
  (implies (expr-list-p lst)
           (expr-p (node-tuple lst)))
  :enable expr-p)

; Creating a tuple with a list of patterns will produce a pattern.
(defrule pattern-tuple-lst-ensures
  (implies (pattern-list-p lst)
           (pattern-p (node-tuple lst)))
  :enable (arithm-expr-p pattern-p))

; Creating a tuple with a list of guards will produce a guard.
(defrule guard-tuple-lst-ensures
  (implies (guard-expr-list-p lst)
           (guard-expr-p (node-tuple lst)))
  :enable guard-expr-p)
  
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

; Sub-nodes of a numeric binop expression are also expressions.
(defrule arirhm-expr-binop-ensures
  (implies (and (arithm-expr-p x) (equal (node-kind x) :binop))
           (and (erl-binop-p (node-binop->op x))
                (arithm-expr-p (node-binop->left x))
                (arithm-expr-p (node-binop->right x))))
  :enable arithm-expr-p)

; Sub-node of a numeric unop expression is also an expression.
(defrule arithm-expr-unop-ensures
  (implies (and (arithm-expr-p x) (equal (node-kind x) :unop))
           (and (erl-unop-p (node-unop->op x))
                (arithm-expr-p (node-unop->expr x))))
  :enable arithm-expr-p)

; Sub-nodes of a binop guard are also guards.
(defrule guard-binop-ensures
  (implies (and (guard-expr-p x) (equal (node-kind x) :binop))
           (and (erl-binop-p (node-binop->op x))
                (guard-expr-p (node-binop->left x))
                (guard-expr-p (node-binop->right x))))
  :enable guard-expr-p)

; Sub-node of an unop guard is also a guard.
(defrule guard-unop-ensures
  (implies (and (guard-expr-p x) (equal (node-kind x) :unop))
           (and (erl-unop-p (node-unop->op x))
                (guard-expr-p (node-unop->expr x))))
  :enable guard-expr-p)

; Sub-nodes of a match expression are expressions, and lhs is a pattern.
(defrule expr-match-ensures
  (implies (and (expr-p x) (equal (node-kind x) :match))
           (and (expr-p (node-match->rhs x))
                (expr-p (node-match->lhs x))
                (pattern-p (node-match->lhs x))))
  :enable expr-p)

; Sub-nodes of a match pattern are patterns.
(defrule pattern-match-ensures
  (implies (and (pattern-p x) (equal (node-kind x) :match))
           (and (pattern-p (node-match->rhs x))
                (pattern-p (node-match->lhs x))))
  :enable (arithm-expr-p pattern-p))

; Clauses of an if expression are erl-clauses
(defrule expr-if-ensures
  (implies (and (expr-p x) (equal (node-kind x) :if))
           (erl-clause-list-p (node-if->clauses x)))
  :enable expr-p)

; Clauses of a case-of expression are erl-clauses, and its expr is an Expression
(defrule expr-case-of-ensures
  (implies (and (expr-p x) (equal (node-kind x) :case-of))
           (and (expr-p (node-case-of->expr x))
                (erl-clause-list-p (node-case-of->clauses x))))
  :enable expr-p)

; Clauses consist of pattern, guards, and a list of expressions.
(defrule clause-ensures
  (implies (erl-clause-p x)
           (and (pattern-list-p (node-clause->cases x))
                (guard-expr-list-p (node-clause->guards x))
                (expr-list-p (node-clause->body x))))
  :enable erl-clause-p)

; If an Expression list is not null, then it must be consp.
(defrule consp-of-expr-list-p
  (implies
    (and x (expr-list-p x))
    (consp x)))