(in-package "ACL2")
(include-book "std/util/top" :dir :system)
(include-book "centaur/fty/top" :DIR :SYSTEM)
(include-book "kestrel/fty/defsubtype" :DIR :SYSTEM)

; Erlang AST Types -------------------------------------------------------------

(set-induction-depth-limit 1)
(set-well-founded-relation l<)

; Term comparison operations
; Does not include term equivalence/non-equivalence
(define comp-binop-p ((x symbolp))
  (b* ((x (symbol-fix x)))
      (not (null (member x '(== /= =< < >= >))))))

; Arithmetic binary operations
; Does not include / or the bitwise operations
(define arithm-binop-p ((x symbolp))
  (b* ((x (symbol-fix x)))
      (not (null (member x '(+ - * div))))))

; Arithmetic unary operations
(define arithm-unop-p ((x symbolp))
  (b* ((x (symbol-fix x)))
      (not (null (member x '(+ -))))))

; Binary boolean operations
(define bool-binop-p ((x symbolp))
  (b* ((x (symbol-fix x)))
      (not (null (member x '(and or xor))))))

; Unary boolean operations
(define bool-unop-p ((x symbolp))
  (b* ((x (symbol-fix x)))
      (not (member x '(not)))))

; Short-circuit operations
(define short-circ-op-p ((x symbolp))
  (b* ((x (symbol-fix x)))
      (not (member x '(orelse andalso)))))

; List operations
(define list-op-p ((x symbolp))
  (b* ((x (symbol-fix x)))
      (not (member x '(++ --)))))

; Erlang binary operators
(fty::defsubtype erl-binop
  :supertype symbolp
  :restriction 
    (lambda (x) 
      (or (comp-binop-p x)
          (arithm-binop-p x)
          (bool-binop-p x)
          (short-circ-op-p x)
          (list-op-p x)))
  :fix-value '+)

; Erlang unary operators
(fty::defsubtype erl-unop
  :supertype symbolp
  :restriction 
    (lambda (x) 
      (or (arithm-unop-p x)
          (bool-unop-p x)))
  :fix-value '+)

; Erlang binary arithmetic operators
(fty::defsubtype erl-numeric-binop
  :supertype erl-binop-p
  :restriction (lambda (x) (arithm-binop-p x))
  :fix-value '+)

; Erlang unary arithmetic operators
(fty::defsubtype erl-numeric-unnop
  :supertype erl-unop-p
  :restriction (lambda (x) (arithm-unop-p x))
  :fix-value '+)

; Node represents an Erlang AST without the restrictions of patterns and guards.
(fty::deftypes node
  (fty::deftagsum node
    (:integer ((val integerp)))
    (:atom ((val symbolp)))
    (:string ((val stringp)))
    (:var ((id symbolp)))
    (:binop ((op erl-binop-p)
		         (left node-p)
             (right node-p)))
    :measure (list (acl2-count x) 1))

  (fty::deflist node-list
    :elt-type node-p
    :true-listp t
    :measure (list (acl2-count x) 0)))


; Arithmetic Expression --------------------------------------------------------

; Arithmetic expressions are expressions allowed in patterns.
;  1) They contain only numeric and bitwise operations.
;  2) They can be evaluated to a constant when compiled. For the ACL2 evaluator,
;     this means that they can be evaluated in isolation, i.e. without bindings,
;     and will not have any side effects, i.e. no new bindings, messages, etc.. 
(define arithm-expr-p ((x acl2::any-p))
  :returns (ok booleanp)
  :measure (node-count x)
  (and (node-p x)
       (case (node-kind x)
         (:integer t)
         (:atom nil)
         (:string nil)
         (:var nil)
         (:binop (and (erl-numeric-binop-p (node-binop->op x))
                      (arithm-expr-p (node-binop->left x))
                      (arithm-expr-p (node-binop->right x)))))))

; Erlang Pattern ---------------------------------------------------------------

; A pattern has the same structure as a term but can contain unbound variables.
; - The match operator is allowed if both operands are valid patterns.
; - Arithmetic expressions are allowed.
; - List concatenation is allowed, but not list substraction.
(define pattern-p ((x acl2::any-p))
  :returns (ok booleanp)
  :measure (node-count x)
  (and 
    (node-p x)
    (or (arithm-expr-p x)
        (case (node-kind x)
              (:integer t)
              (:atom t)
              (:string t)
              (:var t)
              (:binop
                ;; TODO: I need to enforce more things here
                (or (equal (node-binop->op x) '++)
                    (pattern-p (node-binop->left x))
                    (pattern-p (node-binop->right x))))))))

; List of Erlang patterns
(define pattern-list-p ((x acl2::any-p))
  :returns (ok booleanp)
  :measure (node-list-count x)
  (if (consp x)
      (and (pattern-p (car x)) (pattern-list-p (cdr x)))
      (null x)))


; Erlang Expression ------------------------------------------------------------

; All Erlang expression types supported by the evaluator.
(define expr-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-count x)
    (and (node-p x)
         (case (node-kind x)
          (:integer t)
          (:atom t)
          (:string t)
          (:var t)
          (:binop (and (expr-p (node-binop->left x))
                       (expr-p (node-binop->right x)))))))

; List of Erlang Expressions
(define expr-list-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-list-count x)
    (if (consp x)
        (and (expr-p (car x)) (expr-list-p (cdr x)))
        (null x)))


; Theorems ---------------------------------------------------------------------

;; Arithmetic Expression is a subtype of Expression
(defrule arithm-expr-is-subtype-of-expr
  (implies (arithm-expr-p x) (expr-p x))
  :enable (arithm-expr-p expr-p))

;; Pattern is a subtype of Expression
(defrule pattern-is-subtype-of-expr
  (implies (pattern-p x) (expr-p x))
  :enable (expr-p pattern-p))

(defrule expr-is-subtype-of-node
  (implies (expr-p x) (node-p x))
  :expand (expr-p x))

(set-well-founded-relation o<)


; Fixing Functions -------------------------------------------------------------

(define arithm-expr-fix ((x arithm-expr-p))
  :inline t
  (mbe :logic (if (arithm-expr-p x) x (make-node-atom :val 'oops))
       :exec x))

(defrule arithm-expr-fix-produces-arithm-expr
  (arithm-expr-p (arithm-expr-fix x))
  :expand (arithm-expr-fix x))

(defrule arithm-expr-fix-is-the-identity-on-arithm-expr
  (implies (arithm-expr-p x)
           (equal (arithm-expr-fix x) x))
  :expand (arithm-expr-fix x))

(define pattern-fix ((x pattern-p))
  :inline t
  (mbe :logic (if (pattern-p x) x (make-node-atom :val 'oops))
       :exec x))

(defrule pattern-fix-produces-pattern
  (pattern-p (pattern-fix x))
  :expand (pattern-fix x))

(defrule pattern-fix-is-the-identity-on-pattern
  (implies (pattern-p x)
           (equal (pattern-fix x) x))
  :expand (pattern-fix x))

(define expr-fix ((x expr-p))
  :inline t
  (mbe :logic (if (expr-p x) x (make-node-atom :val 'oops))
       :exec x))

(defrule expr-fix-produces-expr
  (expr-p (expr-fix x))
  :expand (expr-fix x))

(defrule expr-fix-is-the-identity-on-expr
  (implies (expr-p x)
           (equal (expr-fix x) x))
  :expand (expr-fix x))


; FTY Types --------------------------------------------------------------------

; Arithmetic Erlang Expression
(fty::deffixtype arithm-expr
  :pred   arithm-expr-p
  :fix    arithm-expr-fix
  :equiv  arithm-expr-equiv
  :define t
  :forward t)

; Erlang Pattern
(fty::deffixtype pattern
  :pred   pattern-p
  :fix    pattern-fix
  :equiv  pattern-equiv
  :define t
  :forward t)

(fty::deflist pattern-list
  :elt-type pattern-p
  :true-listp t
  :pred pattern-list-p)

; Erlang Expression
(fty::deffixtype expr
  :pred   expr-p
  :fix    expr-fix
  :equiv  expr-equiv
  :define t
  :forward t)

(fty::deflist expr-list
  :elt-type expr-p
  :true-listp t
  :pred expr-list-p)