(in-package "ACL2")
(include-book "centaur/fty/top" :DIR :SYSTEM)
(include-book "std/util/top" :DIR :SYSTEM)

(set-induction-depth-limit 1)

;; TODO
;; seperate if and case clauses? One of them has a pattern and guards, the other
;; only has guards

;; Check the clause definition again, is the second arg a single Pattern or a listof Pattern> 

;; There should be a consistent naming convention

(set-well-founded-relation l<)
(fty::deftypes erl-ast
  (fty::defprod expr
    ((linenum natp :default 0)
     (body body-p))
    :measure (list (acl2-count x) 3))
  (fty::deflist expr-list
    :elt-type expr-p
    :true-listp t
    :measure (list (acl2-count x) 0))

  (fty::deftagsum body
    (:erl-term ((term erl-term-p)))
    (:erl-var ((var symbolp)))
    (:erl-unary-op ((op symbolp)
		                (expr expr-p)))
    (:erl-binary-op ((op symbolp)
		                (left expr-p)
                    (right expr-p)))
    (:erl-if ((clauses clause-list-p)))
    (:erl-case ((clauses clause-list-p)))
    (:erl-match ((lhs pattern-p)
                 (rhs expr-p)))
    ; TODO:
    ; erl-call (bif/local/remote/fun - might need to define a type for calls)
    ; erl-fun
    ; erl-pid
    ; erl-receive
    :base-case-override :erl-term
    :measure (list (acl2-count x) 2))

  (fty::deftagsum erl-term
    (:integer ((val integerp)))
    (:atom ((val symbolp)))
    (:string ((val stringp)))
    (:nil ())
    (:cons ((car-expr expr-p)
            (cdr-expr expr-p)))
    (:tuple ((expr-list expr-list-p)))
    :measure (list (acl2-count x) 1))
    
  (fty::defprod clause
    ((linenum natp :default 0)
     (cases pattern-list-p)
     (guards erl-guard-list-p))
     :measure (list (acl2-count x) 2))
  (fty::deflist clause-list
    :elt-type clause-p
    :true-listp t
    :measure (list (acl2-count x) 0))

  ; Not allowed to have case/if/receive/fun/call
  (fty::defprod pattern
    ((linenum natp :default 0)
     (body pattern-body-p))
    :measure (list (acl2-count x) 3))
  (fty::deflist pattern-list
    :elt-type pattern-p
    :true-listp t
    :measure (list (acl2-count x) 0))
  
  (fty::deftagsum pattern-body
    (:erl-term ((term pattern-term-p)))
    (:erl-var ((var symbolp)))
    (:erl-unary-op ((op symbolp)
		                (expr pattern-p)))
    (:erl-binary-op ((op symbolp)
		                (left pattern-p)
                    (right pattern-p)))
    (:erl-match ((lhs pattern-p)
                 (rhs pattern-p)))
    :base-case-override :erl-term
    :measure (list (acl2-count x) 2))
  
  (fty::deftagsum pattern-term
    (:integer ((val integerp)))
    (:atom ((val symbolp)))
    (:string ((val stringp)))
    (:nil ())
    (:cons ((car-expr pattern-p)
            (cdr-expr pattern-p)))
    (:tuple (expr-list pattern-list-p))
    :measure (list (acl2-count x) 1))
  
  ; Not allowed to have case/if/match/receive/fun/call except bifs
  (fty::defprod erl-guard
    ((linenum natp :default 0)
     (body guard-body-p))
    :measure (list (acl2-count x) 3))
  (fty::deflist erl-guard-list
    :elt-type erl-guard-p
    :true-listp t
    :measure (list (acl2-count x) 0))
  
  (fty::deftagsum guard-body
    (:erl-term ((term guard-term-p)))
    (:erl-var ((var symbolp)))
    (:erl-unary-op ((op symbolp)
		                (expr erl-guard-p)))
    (:erl-binary-op ((op symbolp)
		                (left erl-guard-p)
                    (right erl-guard-p)))
    :base-case-override :erl-term
    :measure (list (acl2-count x) 2))
  
  (fty::deftagsum guard-term
    (:integer ((val integerp)))
    (:atom ((val symbolp)))
    (:string ((val stringp)))
    (:nil ())
    (:cons ((car-expr erl-guard-p)
            (cdr-expr erl-guard-p)))
    (:tuple (expr-list erl-guard-list-p))
    :measure (list (acl2-count x) 1)))
(set-well-founded-relation o<)







;; INDUCTION
(set-well-founded-relation l<)
(defines erl-ast-induction
  (define expr-induction ((x expr-p))
    (let ((b (body-fix (expr->body x))))
      (body-case b
        :erl-term (let ((tr (erl-term-fix b.term)))
                    (erl-term-case tr
                      :integer x
                      :atom x
                      :string x
                      :nil x
                      :cons (list (expr-induction (expr-fix tr.car-expr))
                                  (expr-induction (expr-fix tr.cdr-expr)))
                      :tuple (expr-list-induction (expr-list-fix tr.expr-list))))
        :erl-var x
        :erl-unary-op (list b.op (expr-induction (expr-fix b.expr)))
        :erl-binary-op (list b.op 
                            (expr-induction (expr-fix b.left))
                            (expr-induction (expr-fix b.right)))
        :erl-if (clause-list-induction (clause-list-fix b.clauses))
        :erl-case (clause-list-induction (clause-list-fix b.clauses))
        :erl-match (list (pattern-induction (pattern-fix b.rhs))
                         (expr-induction (expr-fix b.lhs))))))
  (define expr-list-induction ((x expr-list-p))
    (if (atom x)
        x
        (list (expr-induction (car (expr-fix x)))
              (expr-list-induction (cdr x)))))
  
  (define clause-induction ((x clause-p))
    :measure (+ (pattern-list-count (clause->cases x)) 
                (erl-guard-list-count (clause->guards x)))
    (let ((p (pattern-list-fix (clause->cases x)))
          (g (erl-guard-list-fix (clause->guards x))))
      (list (pattern-list-induction p)
            (guard-list-induction g))))
  (define clause-list-induction ((x clause-list-p))
    :measure (clause-list-count x)
    (if (atom x)
        x 
        (list (clause-induction (clause-fix (car x)))
              (clause-list-induction (clause-list-fix (cdr x))))))

  (define pattern-induction ((x pattern-p))
    :measure (pattern-count x)
    (let ((b (pattern-body-fix (pattern->body x))))
      (pattern-body-case b
        :erl-term (let ((tr (pattern-term-fix b.term)))
                    (pattern-term-case tr
                      :integer x
                      :atom x
                      :string x
                      :nil x
                      :cons (list (pattern-induction (pattern-fix tr.car-expr))
                                  (pattern-induction (pattern-fix tr.cdr-expr)))
                      :tuple (pattern-list-induction (pattern-list-fix tr.expr-list))))
        :erl-var x
        :erl-unary-op (list b.op (pattern-induction (pattern-fix b.expr)))
        :erl-binary-op (list b.op 
                            (pattern-induction (pattern-fix b.left))
                            (pattern-induction (pattern-fix b.right)))
        :erl-match (list (pattern-induction (pattern-fix b.rhs))
                         (pattern-induction (pattern-fix b.lhs))))))
  (define pattern-list-induction ((x pattern-list-p))
    :measure (pattern-list-count x)
    (if (atom x)
        x 
        (list (pattern-induction (pattern-fix (car x)))
              (pattern-list-induction (pattern-list-fix (cdr x))))))
  
  (define guard-induction ((x erl-guard-p))
    :measure (erl-guard-count x)
    (let ((b (guard-body-fix (erl-guard->body x))))
      (guard-body-case b
        :erl-term (let ((tr (guard-term-fix b.term)))
                    (guard-term-case tr
                      :integer x
                      :atom x
                      :string x
                      :nil x
                      :cons (list (guard-induction (erl-guard-fix tr.car-expr))
                                  (guard-induction (erl-guard-fix tr.cdr-expr)))
                      :tuple (guard-list-induction (erl-guard-list-fix tr.expr-list))))
        :erl-var x
        :erl-unary-op (list b.op (guard-induction (erl-guard-fix b.expr)))
        :erl-binary-op (list b.op 
                            (guard-induction (erl-guard-fix b.left))
                            (guard-induction (erl-guard-fix b.right))))))
  (define guard-list-induction ((x erl-guard-list-p))
    :measure (erl-guard-list-count x)
    (if (atom x)
        x 
        (list (guard-induction (erl-guard-fix (car x)))
              (guard-list-induction (erl-guard-list-fix (cdr x)))))))
(set-well-founded-relation o<)

;; Theorems
(defrule expr-p-of-pattern-p

  (implies (pattern-term-p x)
          (erl-term-p x)))
(defrule expr-p-of-guard-p
  (implies (pattern-p x)
          (expr-p x)))

;; Examples