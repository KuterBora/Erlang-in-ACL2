(in-package "ACL2")
(include-book "centaur/fty/top" :DIR :SYSTEM)

; Erlang Values ----------------------------------------------------------------

(set-induction-depth-limit 1)
(set-well-founded-relation l<)

; Representation of the Erlang values returned by the evaluator.
(fty::deftypes erl-val
  (fty::deftagsum erl-val
    (:integer ((val integerp)))
    (:atom ((val symbolp)))
    (:string ((val stringp)))
    (:nil ())
    (:cons ((lst erl-vlst-p)))
    (:tuple ((tuple erl-vlst-p)))
    (:error ((err symbolp)))
    (:fault ())
    :measure (list (acl2-count x) 1))
  (fty::deflist erl-vlst
    :elt-type erl-val-p
    :true-listp t
    :measure (list (acl2-count x) 0)))

; Reprsentation of Erlang bindings. Maps each variable to a value.
(fty::defomap bind
  :key-type symbol
  :val-type erl-val)

(set-well-founded-relation o<)