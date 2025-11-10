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
(fty::defsubtype erl-numeric-unop
  :supertype erl-unop-p
  :restriction (lambda (x) (arithm-unop-p x))
  :fix-value '+)

; Node represents an Erlang AST without the restrictions of patterns and guards.
(fty::deftypes node
  (fty::deftagsum node
    (:integer ((val integerp)))
    (:atom ((val symbolp)))
    (:string ((val stringp)))
    (:nil ())
    (:cons ((hd node-p)
            (tl node-p)))
    (:tuple ((lst node-list-p)))
    (:var ((id symbolp)))
    (:unop ((op erl-unop-p) (expr node-p)))
    (:binop ((op erl-binop-p)
		         (left node-p)
             (right node-p)))
    (:match ((lhs node-p) (rhs node-p)))
    :measure (list (acl2-count x) 1))

  (fty::deflist node-list
    :elt-type node-p
    :true-listp t
    :measure (list (acl2-count x) 0)))

; Arithmetic Expression --------------------------------------------------------

; Arithmetic expressions are expressions allowed in patterns.
;  1) They contain only numeric and bitwise operations.
;  2) They can be evaluated to a constant during compilation. For the ACL2 evaluator,
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
         (:nil nil)
         (:cons nil)
         (:tuple nil)
         (:var nil)
         (:unop (and (erl-numeric-unop-p (node-unop->op x))
                     (arithm-expr-p (node-unop->expr x))))
         (:binop (and (erl-numeric-binop-p (node-binop->op x))
                      (arithm-expr-p (node-binop->left x))
                      (arithm-expr-p (node-binop->right x))))
         (:match nil))))

; Erlang Pattern ---------------------------------------------------------------

; A pattern has the same structure as a term but can contain unbound variables.
; - The match operator is allowed if both operands are valid patterns.
; - Arithmetic expressions are allowed.
; - List concatenation is allowed, but not list substraction.
(defines pattern
  :flag-local nil
  (define pattern-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-count x)
    :flag pattern
    (and 
      (node-p x)
      (or (arithm-expr-p x)
          (case (node-kind x)
                (:integer t)
                (:atom t)
                (:string t)
                (:nil t)
                (:cons
                  (and (pattern-p (node-cons->hd x))
                       (pattern-p (node-cons->tl x))))
                (:tuple (pattern-list-p (node-tuple->lst x)))
                (:var t)
                (:unop nil)
                ; TODO: strings concat is allowed
                (:binop nil)
                (:match (and (pattern-p (node-match->lhs x))
                             (pattern-p (node-match->rhs x))))))))
  (define pattern-list-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-list-count x)
    :flag pattern-list
    (if (consp x)
        (and (pattern-p (car x)) (pattern-list-p (cdr x)))
        (null x)))
    
    ///
    (std::deflist pattern-list-p (x)
        (pattern-p x)
        :already-definedp t
        :true-listp t))


; Erlang Expression ------------------------------------------------------------

; All Erlang expression types supported by the evaluator.
(defines expr
  :flag-local nil
  (define expr-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-count x)
    :flag expr
    (and (node-p x)
        (case (node-kind x)
          (:integer t)
          (:atom t)
          (:string t)
          (:nil t)
          (:cons 
            (and (expr-p (node-cons->hd x))
                 (expr-p (node-cons->tl x))))
          (:tuple (expr-list-p (node-tuple->lst x)))
          (:var t)
          (:unop (expr-p (node-unop->expr x)))
          (:binop (and (expr-p (node-binop->left x))
                       (expr-p (node-binop->right x))))
          (:match (and (pattern-p (node-match->lhs x))
                       (expr-p (node-match->rhs x)))))))

  ; List of Erlang Expressions
  (define expr-list-p ((x acl2::any-p))
      :returns (ok booleanp)
      :measure (node-list-count x)
      :flag expr-list
      (if (consp x)
          (and (expr-p (car x)) (expr-list-p (cdr x)))
          (null x)))
    
    ///
    (std::deflist expr-list-p (x)
        (expr-p x)
        :already-definedp t
        :true-listp t))


; Theorems ---------------------------------------------------------------------

(defthm-expr-flag
  ; Expression list is a subtype of Node list
  (defthm expr-list-is-subtype-of-node-list
    (implies (expr-list-p x) (node-list-p x))
    :flag expr-list)
  ; Expression is a subtype of Node
  (defthm expr-is-subtype-of-node
    (implies (expr-p x) (node-p x))
    :flag expr)
  :hints (("Goal" :in-theory (enable expr-p))))

; Arithmetic Expression is a subtype of Expression
(defrule arithm-expr-is-subtype-of-expr
  (implies (arithm-expr-p x) (expr-p x))
  :enable (arithm-expr-p expr-p))

; Arithmetic Expression is a subtype of Pattern
(defrule arithm-expr-is-subtype-of-pattern
  (implies (arithm-expr-p x) (pattern-p x))
  :enable (arithm-expr-p pattern-p))

(defthm-pattern-flag
  ; Pattern list is a subtype of Expression list
  (defthm pattern-list-is-subtype-of-expr-list
    (implies (pattern-list-p x) (expr-list-p x))
    :flag pattern-list)
  ; Pattern is a subtype of Expression
  (defthm pattern-is-subtype-of-expr
    (implies (pattern-p x) (expr-p x))
    :flag pattern)
  :hints (("Goal" :in-theory (enable pattern-p expr-p))))

(set-well-founded-relation o<)


; Fixing Functions -------------------------------------------------------------

(define arithm-expr-fix ((x arithm-expr-p))
  :inline t
  (mbe :logic (if (arithm-expr-p x) x (make-node-integer :val 0))
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