(in-package "ACL2")
(include-book "centaur/fty/top" :DIR :SYSTEM)
(include-book "std/util/top" :DIR :SYSTEM)
(set-induction-depth-limit 1)
;; require erl-ast.lisp
;; require erl-value.lisp

(set-well-founded-relation l<)
(fty::deftagsum erl-k
    (:init ())
    (:exprs ((next expr-list-p) (k erl-k-p)))
    ;; cons
    (:cons-cdr ((cdr-expr expr-p) (bindings0 bind-p) (k erl-k-p)))
    (:cons-merge ((car-result erl-value-p) (car-bindings bind-p) (k erl-k-p)))
    ;; tuple
    (:tuple-cdr ((cdr-expr expr-p) (bindings0 bind-p) (k erl-k-p)))
    (:tuple-merge ((car-result erl-value-p) (car-bindings bind-p) (k erl-k-p)))
    ;; match
    (:match ((expr expr-p) (k erl-k-p)))
    (:match-cons ((lhs-tl expr-p) (rhs-tl erl-value-p) (bindings0 bind-p) (k erl-k-p)))
    (:match-cons-nil ((k erl-k-p)))
    (:match-tuple ((lhs-tl expr-p) (rhs-tl erl-value-p) (bindings0 bind-p) (k erl-k-p)))
    (:match-lhs ((rhs erl-value-p) (k erl-k-p)))
    ;; unary op
    (:unary-op ((op symbolp) (k erl-k-p)))
    ;; binary op
    (:binary-op-expr1 ((op symbolp) (expr2 expr-p) (bindings0 bind-p) (k erl-k-p)))
    (:binary-op-expr2 ((op symbolp) (result erl-value-p) (bindings1 bind-p) (k erl-k-p)))
    ;; clauses
    (:guard ((guards erl-guard-list-p) (bindings0 bind-p) (k erl-k-p)))
    (:if ((body expr-list-p) (bindings0 bind-p) (tl-clauses clause-list-p) (k erl-k-p)))
    (:case-value ((clauses clause-list-p) (k erl-k-p)))
    (:case-match ((value erl-value-p) 
                  (guards erl-guard-list-p)
                  (body expr-list-p)
                  (bindings0 bind-p)
                  (tl-clauses clause-list-p)
                  (k erl-k-p)))
    (:case-guards ((value erl-value-p)
                   (body expr-list-p)
                   (mbindings bind-p)
                   (bindings0 bind-p)
                   (tl-clauses clause-list-p)
                   (k erl-k-p))))
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

(set-well-founded-relation o<)