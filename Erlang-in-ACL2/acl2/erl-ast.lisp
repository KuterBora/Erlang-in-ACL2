(in-package "ACL2")
(include-book "centaur/fty/top" :DIR :SYSTEM)
(include-book "std/util/top" :DIR :SYSTEM)
(set-induction-depth-limit 1)

(set-well-founded-relation l<)

;; Node represents an Erlang AST without the restrictions of patterns and guards.
;; TODO: fun, receive, call, pid
;; TODO: op's symbolp should have a contraint, for example: (member op '(+ - * div)) 
(fty::deftypes node
  (fty::deftagsum node
    (:integer ((val integerp)))
    (:atom ((val symbolp)))
    (:string ((val stringp)))
    (:nil ())
    (:cons ((left node-p)
            (right node-p)))
    (:tuple ((lst node-list-p)))
    (:var ((var symbolp)))
    (:unary-op ((op symbolp)
		            (opand node-p)))
    (:binary-op ((op symbolp)
		             (left node-p)
                 (right node-p)))
    (:if ((clauses node-clause-list-p)))
    (:case-of ((expr node-p) (clauses node-clause-list-p)))
    (:match ((lhs node-p)
             (rhs node-p)))
    (:fault ())
    :measure (list (acl2-count x) 1))
  (fty::deflist node-list
    :elt-type node-p
    :true-listp t
    :measure (list (acl2-count x) 0))
    
  (fty::defprod node-clause
    ((cases node-list-p)
     (guards node-list-p :default nil)
     (body node-p))
    :measure (list (acl2-count x) 2))
  (fty::deflist node-clause-list
    :elt-type node-clause-p
    :true-listp t
    :measure (list (acl2-count x) 0)))


;; Erl Pattern
;; Not allowed to have case/if/receive/fun/call
(defines pattern
  :flag-local nil
  (define pattern-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-count x)
    :flag pattern
    (and (node-p x)
         (case (node-kind x)
          (:integer t)
          (:atom t)
          (:string t)
          (:nil t)
          (:cons (and (pattern-p (node-cons->left x))
                      (pattern-p (node-cons->right x))))
          (:tuple (pattern-list-p (node-tuple->lst x)))
          (:var t)
          (:unary-op (pattern-p (node-unary-op->opand x)))
          (:binary-op (and (pattern-p (node-binary-op->left x))
                           (pattern-p (node-binary-op->right x))))
          (:if nil)
          (:case-of nil)
          (:match (and (pattern-p (node-match->lhs x))
                       (pattern-p (node-match->rhs x))))
          (:fault t))))
  (define pattern-list-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-list-count x)
    :flag pattern-lst
    (if (consp x)
      (and (pattern-p (car x)) (pattern-list-p (cdr x)))
      (null x))))


;; Erl Guard
;; Not allowed to have match/case/if/receive/fun/call
(defines erl-guard
  :flag-local nil
  (define erl-guard-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-count x)
    :flag erl-guard
    (and (node-p x)
         (case (node-kind x)
          (:integer t)
          (:atom t)
          (:string t)
          (:nil t)
          (:cons (and (erl-guard-p (node-cons->left x))
                      (erl-guard-p (node-cons->right x))))
          (:tuple (erl-guard-list-p (node-tuple->lst x)))
          (:var t)
          (:unary-op (erl-guard-p (node-unary-op->opand x)))
          (:binary-op (and (erl-guard-p (node-binary-op->left x))
                           (erl-guard-p (node-binary-op->right x))))
          (:if nil)
          (:case-of nil)
          (:match nil)
          (:fault t))))
  (define erl-guard-list-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-list-count x)
    :flag erl-guard-lst
    (if (consp x)
      (and (erl-guard-p (car x)) (erl-guard-list-p (cdr x)))
      (null x))))


;; Erl Expression
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
          (:cons (and (expr-p (node-cons->left x))
                      (expr-p (node-cons->right x))))
          (:tuple (expr-list-p (node-tuple->lst x)))
          (:var t)
          (:unary-op (expr-p (node-unary-op->opand x)))
          (:binary-op (and (expr-p (node-binary-op->left x))
                           (expr-p (node-binary-op->right x))))
          (:if (clause-list-p (node-if->clauses x)))
          (:case-of (clause-list-p (node-case-of->clauses x)))
          (:match (and (pattern-p (node-match->lhs x))
                       (expr-p (node-match->rhs x))))
          (:fault t))))
  (define expr-list-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-list-count x)
    :flag expr-lst
    (if (consp x)
      (and (expr-p (car x)) (expr-list-p (cdr x)))
      (null x)))

  (define clause-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-clause-count x)
    :flag clause 
    (and (node-clause-p x)
         (pattern-list-p (node-clause->cases x))
         (erl-guard-list-p (node-clause->guards x))
         (expr-p (node-clause->body x))))
  (define clause-list-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (node-clause-list-count x)
    :flag clause-list
    (if (consp x)
      (and (clause-p (car x)) (clause-list-p (cdr x)))
      (null x))))


;; Theorems

;; pattern-is-expr
(defthm-pattern-flag
  (defthm pattern-is-subtype-of-expr
    (implies (pattern-p x) (expr-p x))
    :flag pattern
    :hints ('(:expand ((expr-p x) (pattern-p x)))))

  (defthm pattern-list-is-subtype-of-expr-list
    (implies (pattern-list-p x) (expr-list-p x))
    :flag pattern-lst
    :hints ('(:expand ((expr-list-p x) (pattern-list-p x))))))

;; erl-guard-is-expr
(defthm-erl-guard-flag
  (defthm erl-guard-is-subtype-of-expr
    (implies (erl-guard-p x) (expr-p x))
    :flag erl-guard
    :hints ('(:expand ((expr-p x) (erl-guard-p x)))))

  (defthm erl-guard-list-is-subtype-of-expr-list
    (implies (erl-guard-list-p x) (expr-list-p x))
    :flag erl-guard-lst
    :hints ('(:expand ((expr-list-p x) (erl-guard-list-p x))))))

(set-well-founded-relation o<)


;; Fixing Functions

;; pattern-fix
(define pattern-fix ((x pattern-p))
  :inline t
  (mbe :logic (if (pattern-p x) x (make-node-fault))
       :exec x))

(defrule pattern-fix-produces-pattern
  (pattern-p (pattern-fix x))
  :expand (pattern-fix x))

(defrule pattern-fix-is-the-identity-on-pattern
  (implies (pattern-p x)
           (equal (pattern-fix x) x))
  :expand (pattern-fix x))

;; guard-fix
(define erl-guard-fix ((x erl-guard-p))
  :inline t
  (mbe :logic (if (erl-guard-p x) x (make-node-fault))
       :exec x))

(defrule erl-guard-fix-produces-erl-guard
  (erl-guard-p (erl-guard-fix x))
  :expand (erl-guard-fix x))

(defrule erl-guard-fix-is-the-identity-on-erl-guard
  (implies (erl-guard-p x)
           (equal (erl-guard-fix x) x))
  :expand (erl-guard-fix x))

;; expr-fix
(define expr-fix ((x expr-p))
  :inline t
  (mbe :logic (if (expr-p x) x (make-node-fault))
       :exec x))

(defrule expr-fix-produces-expr
  (expr-p (expr-fix x))
  :expand (expr-fix x))

(defrule expr-fix-is-the-identity-on-expr
  (implies (expr-p x)
           (equal (expr-fix x) x))
  :expand (expr-fix x))

;; clause-fix
(define clause-fix ((x clause-p))
  :inline t
  (mbe :logic (if (clause-p x) 
                  x 
                  '((cases) (guards) (body :fault)))
       :exec x))

(defrule clause-fix-produces-clause
  (clause-p (clause-fix x))
  :expand (clause-fix x))

(defrule clause-fix-is-the-identity-on-clause
  (implies (clause-p x)
           (equal (clause-fix x) x))
  :expand (clause-fix x))


;; FTY Types
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

(fty::deffixtype erl-guard
  :pred   erl-guard-p
  :fix    erl-guard-fix
  :equiv  erl-guard-equiv
  :define t
  :forward t)

(fty::deflist erl-guard-list
    :elt-type erl-guard-p
    :true-listp t
    :pred erl-guard-list-p)

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

(fty::deffixtype clause
  :pred   clause-p
  :fix    clause-fix
  :equiv  clause-equiv
  :define t
  :forward t)

(fty::deflist clause-list
    :elt-type clause-p
    :true-listp t
    :pred clause-list-p)