(in-package "ACL2")
(include-book "centaur/fty/top" :DIR :SYSTEM)
(include-book "std/util/top" :DIR :SYSTEM)

(set-induction-depth-limit 1)
(set-well-founded-relation l<)

;; TODO
;; Check the clause definition again, is the second arg a single Pattern or a listof Pattern> 
;; There should be a consistent naming convention

; abstract all 3 types to a node type
; seperate if and case clauses as required
; well-formed-p might be needed

;; Erl Pattern
;; Not allowed to have case/if/receive/fun/call
(fty::deftypes patterns
  (fty::deftagsum pattern
    (:integer ((val integerp)))
    (:atom ((val symbolp)))
    (:string ((val stringp)))
    (:nil ())
    (:cons ((car-pattern pattern-p)
            (cdr-pattern pattern-p)))
    (:tuple ((lst pattern-list-p)))
    (:var ((var symbolp)))
    (:unary-op ((op symbolp)
		            (pattern pattern-p)))
    (:binary-op ((op symbolp)
		             (left pattern-p)
                 (right pattern-p)))
    (:match ((lhs pattern-p)
             (rhs pattern-p)))
    :measure (list (acl2-count x) 1))
    
  (fty::deflist pattern-list
    :elt-type pattern-p
    :measure (list (acl2-count x) 0)
    :true-listp t))

;; Erl Guard
;; Not allowed to have case/if/match/receive/fun/call except bifs
(fty::deftypes guards
  (fty::deftagsum erl-guard
    (:integer ((val integerp)))
    (:atom ((val symbolp)))
    (:string ((val stringp)))
    (:nil ())
    (:cons ((car-guard erl-guard-p)
            (cdr-guard erl-guard-p)))
    (:tuple ((lst erl-guard-list-p)))
    (:var ((var symbolp)))
    (:unary-op ((op symbolp)
		            (guard erl-guard-p)))
    (:binary-op ((op symbolp)
		             (left erl-guard-p)
                 (right erl-guard-p)))
    :measure (list (acl2-count x) 1))
    
  (fty::deflist erl-guard-list
    :elt-type erl-guard-p
    :measure (list (acl2-count x) 0)
    :true-listp t))

;; Erl Clause
; TODO: maybe separate if, case and function clauses?
(fty::defprod clause
    ((cases pattern-list-p)
     (guards erl-guard-list-p))
     :measure (list (acl2-count x) 1))
(fty::deflist clause-list
  :elt-type clause-p
  :measure (list (acl2-count x) 0)
  :true-listp t)

;; Erl Expression
(fty::deftypes exprs
  (fty::deftagsum expr
    (:integer ((val integerp)))
    (:atom ((val symbolp)))
    (:string ((val stringp)))
    (:nil ())
    (:cons ((car-expr expr-p)
            (cdr-expr expr-p)))
    (:tuple ((lst expr-list-p)))
    (:var ((var symbolp)))
    (:unary-op ((op symbolp)
		            (expr expr-p)))
    (:binary-op ((op symbolp)
		             (left expr-p)
                 (right expr-p)))
    (:if ((clauses clause-list-p)))
    (:case-of ((clauses clause-list-p)))
    (:match ((lhs pattern-p)
             (rhs expr-p)))
    ; TODO:
    ; erl-call (bif/local/remote/fun - might need to define a type for calls)
    ; erl-fun
    ; erl-pid
    ; erl-receive
    :measure (list (acl2-count x) 1))
  (fty::deflist expr-list
    :elt-type expr-p
    :measure (list (acl2-count x) 0)
    :true-listp t))

;; Erl AST, has a line number and expr
(fty::defprod erl-ast
  ((linenum natp :default 0)
   (expr expr-p)))
  
(set-well-founded-relation o<)

(defines expr-p-of-pattern-p-induction
  :verify-guards nil
  (define induct-pattern ((x pattern-p))
    :flag pattern
    :measure (pattern-count x)
    (and (equal (expr-kind x) (pattern-kind x)) 
      (case (pattern-kind x)
        (:cons (list (induct-pattern (pattern-cons->car-pattern x))
                    (induct-pattern (pattern-cons->cdr-pattern x))))
        (:tuple (induct-pattern-list (pattern-tuple->lst x)))
        (:unary-op (induct-pattern (pattern-unary-op->pattern x)))
        (:binary-op (list (induct-pattern (pattern-binary-op->left x))
                          (induct-pattern (pattern-binary-op->right x))))
        (:match (list (induct-pattern (pattern-match->lhs x)) 
                      (induct-pattern (pattern-match->rhs x))))
        (otherwise (expr-p x)))))
  (define induct-pattern-list ((lst1 pattern-list-p))
    :flag list
    :measure (pattern-list-count lst1)
    (if (and (consp lst1))
	      (list (induct-pattern (car lst1))
		          (induct-pattern-list (cdr lst1)))
	      t)))


(defrule expr-p-of-pattern-p
  :in-theory (enable expr-p pattern-p induct-pattern)
  :induct (induct-pattern x)
  (implies (pattern-p x)
           (expr-p x)))
  

(defrule expr-p-of-guard-p
  (implies (guard-p x)
           (expr-p x)))

;;==================================================================================

;; pattern-p implies expr-p
(defrule pattern-is-subtype-of-node
  (implies (pattern-p x) (node-p x))
  :expand (pattern-p x))
  
(defrule pattern-can-be-term
    (implies (AND (FLAG-IS 'PATTERN)
                  (NOT (EQUAL (NODE-KIND X) :CONS))
                  (NOT (EQUAL (NODE-KIND X) :TUPLE))
                  (NOT (EQUAL (NODE-KIND X) :UNARY-OP))
                  (NOT (EQUAL (NODE-KIND X) :BINARY-OP))
                  (NOT (EQUAL (NODE-KIND X) :IF))
                  (NOT (EQUAL (NODE-KIND X) :CASE-OF))
                  (NOT (EQUAL (NODE-KIND X) :MATCH))
                  (PATTERN-P X))
            (OR (EQUAL (NODE-KIND X) :INTEGER)
                (EQUAL (NODE-KIND X) :ATOM)
                (EQUAL (NODE-KIND X) :STRING)
                (EQUAL (NODE-KIND X) :NIL)
                (EQUAL (NODE-KIND X) :VAR)))
      :expand ((pattern-p x) (node-p x)))

(defrule stupid-3
  (implies (and (node-p x)
                (OR (EQUAL (NODE-KIND X) :INTEGER)
                    (EQUAL (NODE-KIND X) :ATOM)
                    (EQUAL (NODE-KIND X) :STRING)
                    (EQUAL (NODE-KIND X) :NIL)
                    (EQUAL (NODE-KIND X) :VAR)))
            (expr-p x))
  :expand ((expr-p x)))


(defrule stupid-4
  (IMPLIES (and (pattern-p x)
                (EQUAL (NODE-KIND X) :MATCH))
          (PATTERN-P (NODE-MATCH->LHS X)))
    :expand (pattern-p x)
    :rule-classes (:forward-chaining))

(defrule stupid-5
  (IMPLIES (and (pattern-p x)
                (EQUAL (NODE-KIND X) :MATCH))
          (PATTERN-P (NODE-MATCH->RHS X)))
    :expand (pattern-p x)
    :rule-classes (:forward-chaining))

(defrule stupid-6 
  (IMPLIES (AND (EQUAL (NODE-KIND X) :MATCH)
                (EXPR-P (NODE-MATCH->LHS X))
                (EXPR-P (NODE-MATCH->RHS X))
                (pattern-p x))
         (EXPR-P X))
  :expand (expr-p x))

(defrule stupid-7
  (implies (pattern-p x)
           (and (not (equal (node-kind x) :CASE-OF))
                (not (equal (node-kind x) :IF))))
  :expand (pattern-p x))

(defrule stupid-8
  (implies (and (pattern-p x)
                (EQUAL (NODE-KIND X) :BINARY-OP))
           (pattern-p (node-binary-op->left x)))
  :expand (pattern-p x)
  :rule-classes (:forward-chaining))

(defrule stupid-9
  (implies (and (pattern-p x)
                (EQUAL (NODE-KIND X) :BINARY-OP))
           (pattern-p (node-binary-op->right x)))
  :expand (pattern-p x)
  :rule-classes (:forward-chaining))

(defrule stupid-10
  (IMPLIES (AND (EQUAL (NODE-KIND X) :BINARY-OP)
                (EXPR-P (NODE-BINARY-OP->LEFT X))
                (EXPR-P (NODE-BINARY-OP->RIGHT X))
                (pattern-p x))
         (EXPR-P X))
  :expand (expr-p x))

(defrule stupid-11
  (implies (and (pattern-p x) 
                (equal (node-kind x) :unary-op))
           (pattern-p (node-unary-op->opand x)))
  :expand (pattern-p x))

(defrule stupid-12
  (IMPLIES (AND (EQUAL (NODE-KIND X) :UNARY-OP)
                (EXPR-P (NODE-UNARY-OP->OPAND X))
                (PATTERN-P X))
           (EXPR-P X))
  :expand (expr-p x))

(defrule stupid-13
  (implies (and (pattern-list-p x) (not (consp x)))
           (and (null x) (expr-list-p x)))
  :expand ((pattern-list-p x) (expr-list-p x)))

(defrule stupid-14
  (implies (and (pattern-list-p x) (consp x))
           (pattern-p (car x)))
  :expand (pattern-list-p x))

(defrule stupid-15
  (implies (and (pattern-list-p x) (consp x))
           (pattern-list-p (cdr x)))
  :expand (pattern-list-p x))

(defrule stupid-16
  (implies (and (expr-list-p (cdr x))
                (expr-p (car x)))
            (expr-list-p x))
  :expand (expr-list-p x))

(defrule stupid-17
  (implies (and (pattern-p x)
                (EQUAL (NODE-KIND X) :TUPLE))
           (pattern-list-p (node-tuple->lst x)))
  :expand (pattern-p x))

(defrule stupid-18
  (implies (and (pattern-p x)
                (EQUAL (NODE-KIND X) :TUPLE)
                (EXPR-LIST-P (NODE-TUPLE->LST X)))
           (expr-p x))
  :expand (expr-p x))

(defrule stupid-19
  (implies (and (pattern-p x)
                (EQUAL (NODE-KIND X) :CONS))
           (pattern-p (node-cons->left x)))
  :expand (pattern-p x)
  :rule-classes (:forward-chaining))

(defrule stupid-20
  (implies (and (pattern-p x)
                (EQUAL (NODE-KIND X) :CONS))
           (pattern-p (node-cons->right x)))
  :expand (pattern-p x)
  :rule-classes (:forward-chaining))

(defrule stupid-21
  (IMPLIES (AND (EQUAL (NODE-KIND X) :CONS)
                (EXPR-P (NODE-CONS->LEFT X))
                (EXPR-P (NODE-CONS->RIGHT X))
                (pattern-p x))
         (EXPR-P X))
  :expand (expr-p x))

(defthm-pattern-flag
  (defthm pattern-is-subtype-of-expr
    (implies (pattern-p x)  (expr-p x))
    :flag pattern)
  (defthm pattern-list-is-subtype-of-expr-list
    (implies (pattern-list-p x)  (expr-list-p x))
    :flag pattern-lst))