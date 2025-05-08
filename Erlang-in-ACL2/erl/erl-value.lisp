(in-package "ACL2")
(include-book "centaur/fty/top" :DIR :SYSTEM)
(include-book "std/util/top" :DIR :SYSTEM)

(set-induction-depth-limit 1)

(set-well-founded-relation l<)
;; Return value of the evaluator
;; TODO: fun, pid
(fty::deftypes erl-value
  (fty::deftagsum erl-value
    (:integer ((val integerp)))
		(:atom ((val symbolp)))
		(:string ((val stringp)))
		(:cons ((lst erl-value-list-p)))
		(:tuple ((tuple erl-value-list-p)))
    (:error ((err symbolp)))
    :measure (list (acl2-count x) 1))
  (fty::deflist erl-value-list
	  :elt-type erl-value-p
		:true-listp t
		:measure (list (acl2-count x) 0)))

;; Bindings of variables to values
(fty::defalist bind
  :key-type symbol
  :val-type erl-value
  :true-listp t)

;; TODO: error types?

(set-well-founded-relation o<)