(in-package "ACL2")
(include-book "erl-ast")
(include-book "erl-value")
(include-book "erl-op")

; Erlang World -----------------------------------------------------------------

; Representation of the Erlang modules known by the interpreter. For now, the
; world is static -- it cannot be dynamically modified during interpretation.
; Future work could consider how to reason about changing worlds.

; A function declaration consists of a name and arirty, mappped to a
; sequence of function clauses.
;
; A function clause is an erl-clause-p where the patterns are the parameters,
; guard-lists are the guards, and the body is the function body to be evaluated.
; - Each function clause in the same sequence must have the same 
;   number of parameters.
;
; A function name is an atom. 

(set-well-founded-relation l<)

; Pair of function name and arity
(fty::defprod fn
  ((name symbolp)
   (arity natp)))
(fty::deflist fn-list
  :elt-type fn-p
  :true-listp t)

; A map from function name and arity to function definition
(fty::defomap fn-map
  :key-type fn
  :val-type erl-clause-list)

; A map from fn to module. This is for looking up module imports.
(fty::defomap fn-mod-map
  :key-type fn
  :val-type symbol)

; Module attributes. Currently, only the following three are supported.
(fty::defprod attrs
  ; name of the module
  ((module symbolp :default 'local)
  ; exported functions
   (export fn-list-p :default nil)
  ; imported functions
   (import fn-mod-map :default nil)))

; Erlang code is divided into modules. A module consists of a sequence of 
; attributes and function declarations
(fty::defprod module
  ((attrs attrs-p :default (make-attrs))
   (fn-defns fn-map-p :default nil)))

; World is a map from module name to module
(fty::defomap world
  :key-type symbol
  :val-type module)

(set-well-founded-relation o<)


; Erlang BIFs ------------------------------------------------------------------

; Built-In Functions (BIFs) of Erlang. BIFs are found in multiple packages,
; though mostly in 'erlang'. Most BIFs are auto-imported.
; 
; Since none of the Erlang packages are implemented, the following frequently
; used BIFs are added to the world directly.
;
; Remark: All of these BIFs can be used in guards. If more BIFs are addded in
; the future, a distinction might be needed for guards with side effects which
; are not allowed to be called by guard expressions.
;
(define erl-bif-p ((x acl2::any-p))
  :returns (ok booleanp)
  (and (fn-p x)
       (or 
        (and (equal (fn->name x) 'is_atom) (equal (fn->arity x) 1))
        (and (equal (fn->name x) 'is_boolean) (equal (fn->arity x) 1))
        (and (equal (fn->name x) 'is_function) (equal (fn->arity x) 1))
        (and (equal (fn->name x) 'is_function) (equal (fn->arity x) 2))
        (and (equal (fn->name x) 'is_integer) (equal (fn->arity x) 1))
        (and (equal (fn->name x) 'is_list) (equal (fn->arity x) 1))
        (and (equal (fn->name x) 'is_number) (equal (fn->arity x) 1))
        (and (equal (fn->name x) 'is_tuple) (equal (fn->arity x) 1))
        (and (equal (fn->name x) 'abs) (equal (fn->arity x) 1))
        (and (equal (fn->name x) 'element) (equal (fn->arity x) 2))
        (and (equal (fn->name x) 'hd) (equal (fn->arity x) 1))
        (and (equal (fn->name x) 'length) (equal (fn->arity x) 1))
        (and (equal (fn->name x) 'max) (equal (fn->arity x) 2))
        (and (equal (fn->name x) 'min) (equal (fn->arity x) 2))
        (and (equal (fn->name x) 'tl) (equal (fn->arity x) 1))
        (and (equal (fn->name x) 'tuple_size) (equal (fn->arity x) 1))))
    ///
      (defrule fn-of-erl-bif
        (implies (erl-bif-p x) (fn-p x))))