(in-package "ACL2")
(include-book "centaur/fty/top" :DIR :SYSTEM)
(include-book "std/util/top" :DIR :SYSTEM)
(include-book "erl-ast")
(include-book "erl-value")
(set-induction-depth-limit 1)

(set-well-founded-relation l<)
(fty::deftagsum erl-k ; horrible name, how do we distinguish a single step of the continuation and the list thereof?
    ; (:init ())
    (:expr ((expr expr-p)))  ; added by mrg, 7/14/2025
    (:exprs ((next expr-list-p)))
    ;; cons
    (:cons-cdr ((cdr-expr expr-p) (bindings0 bind-p)))
    (:cons-merge ((car-result erl-value-p) (car-bindings bind-p)))
    ;; tuple
    (:tuple-cdr ((cdr-expr expr-p) (bindings0 bind-p)))
    (:tuple-merge ((car-result erl-value-p) (car-bindings bind-p)))
    ;; match
    (:match ((expr expr-p)))
    ;;
    (:match-cons ((lhs-tl expr-p) (rhs-tl erl-value-p) (bindings0 bind-p)))
    (:match-cons-nil ((nothing any-p)))
    (:match-tuple ((lhs-tl expr-p) (rhs-tl erl-value-p) (bindings0 bind-p)))
    (:match-lhs ((rhs erl-value-p)))
    ;; unary op
    (:unary-op ((op symbolp)))
    ;; binary op
    (:binary-op-expr1 ((op symbolp) (right-expr expr-p) (bindings0 bind-p)))
    (:binary-op-expr2 ((op symbolp) (left-val erl-value-p) (bindings1 bind-p)))
    ;; clauses
    (:guard ((guards erl-guard-list-p) (bindings0 bind-p)))
    (:if ((body expr-list-p) (bindings0 bind-p) (tl-clauses clause-list-p)))
    (:case-value ((clauses clause-list-p)))
    (:case-match ((value erl-value-p) 
                  (guards erl-guard-list-p)
                  (body expr-list-p)
                  (bindings0 bind-p)
                  (tl-clauses clause-list-p)))
    (:case-guards ((value erl-value-p)
                   (body expr-list-p)
                   (mbindings bind-p)
                   (bindings0 bind-p)
                   (tl-clauses clause-list-p)))
    )
; TODO
; call-k
; arg-next-k
; create-lb-k
; remote-call-k
; func-body-k
; func-guards-k
; fun-call-k
; fun-call-return-k
; fun-body-k
; fun-guards-k


(fty::deflist erl-k-list
  :elt-type  erl-k
  :true-listp t)
