(in-package "ACL2")
(include-book "centaur/fty/top" :DIR :SYSTEM)

; Erlang Values ----------------------------------------------------------------

(set-induction-depth-limit 1)
(set-well-founded-relation l<)

; Representation of the Erlang values returned by the evaluator.
; Execptions are handled naively, proper exception handling is left as future work.
(fty::deftypes erl-val
  (fty::deftagsum erl-val

    ; Erlang return values
    (:integer ((val integerp)))
    (:atom ((val symbolp)))
    (:string ((val stringp)))
    (:nil ())
    (:cons ((lst erl-vlst-p)))
    (:tuple ((tuple erl-vlst-p)))
    (:excpt ((err symbolp)))

    ; Internal return values
    (:none ())
    (:error ((err stringp)))
    (:flimit ())

    :measure (list (acl2-count x) 1))
  (fty::deflist erl-vlst
    :elt-type erl-val-p
    :true-listp t
    :measure (list (acl2-count x) 0)))

; Reprsentation of Erlang bindings. Maps each variable to a value.
(fty::defomap bind
  :key-type symbol
  :val-type erl-val)

; Representation of the current State of the Erlang program under evaluation
; TODO: World and Out to represent the admitted forms and sent messages
(fty::defprod erl-state
  ((in erl-val-p :default (make-erl-val-none))
   (bind bind-p :default nil)))

(set-well-founded-relation o<)