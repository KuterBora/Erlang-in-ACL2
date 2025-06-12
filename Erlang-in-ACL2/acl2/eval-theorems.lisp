(in-package "ACL2")
(include-book "centaur/fty/top" :DIR :SYSTEM)
(include-book "std/util/top" :DIR :SYSTEM)
(set-induction-depth-limit 1)

;; Theorems to help admit the evaluator

(defrule node-kind-is-car-of-node
  (implies (node-p x)
           (equal (car x) (node-kind x)))
  :expand ((node-p x) (node-kind x)))

(defrule node-kind-is-car-of-expr
  (implies (expr-p x)
           (equal (car x) (node-kind x)))
  :expand ((expr-p x) (node-kind x)))

(defrule erl-ast-is-erl-value-when-term
  (implies (and (expr-p x)
                (or (equal (node-kind x) :integer)
                    (equal (node-kind x) :atom)
                    (equal (node-kind x) :string)
                    (equal (node-kind x) :nil)))
           (erl-value-p x))
  :expand ((expr-p x) (erl-value-p x) (node-kind x) (node-p x)))

(defrule expr-binary-op-ensures
    (implies (and (expr-p x) (equal (node-kind x) :binary-op))
             (and (expr-p (node-binary-op->left x))
                  (expr-p (node-binary-op->right x))))
    :expand (expr-p x))

(defrule expr-implies-node
  (implies (expr-p x)
           (node-p x))
  :expand (expr-p x))