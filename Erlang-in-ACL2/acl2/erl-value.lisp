(in-package "ACL2")
(include-book "centaur/fty/top" :DIR :SYSTEM)

(set-induction-depth-limit 1)
(set-well-founded-relation l<)

; Erlang Values and Exceptions -------------------------------------------------

; Exceptions are run-time errors or generated errors and are of three different 
; classes, with different origins.
; - error:	Run-time error, for example, 1+a, or the process called error/1
; - exit:   The process called exit/1
; - throw:	The process called throw/1
(fty::deftagsum err-class
  (:error ())
  (:exit ())
  (:throw ()))

; Representation of the Erlang values returned by the evaluator.
(fty::deftypes erl-val
  
  ; Erlang Values
  (fty::deftagsum erl-val
    ; Erlang return values
    (:integer ((val integerp)))
    (:atom ((val symbolp)))
    (:string ((val stringp)))
    (:nil ())
    (:cons ((lst erl-vlst-p)))
    (:tuple ((tuple erl-vlst-p)))
    (:excpt ((err erl-err-p)))

    ; Internal return values
    (:none ())
    (:reject ((err stringp)))
    (:flimit ())

    :measure (list (acl2-count x) 1))
  
  ; List of Erlang Values
  (fty::deflist erl-vlst
    :elt-type erl-val-p
    :true-listp t
    :measure (list (acl2-count x) 0))

  ; Erlang Errors
  (fty::defprod erl-err
    ((class err-class-p :default 'error)
     (reason exit-reason-p)
     (stack true-listp :default nil))
    :measure (list (acl2-count x) 1))

  ; Erlang Exit Reasons
  (fty::deftagsum exit-reason
    (:badarg ())
    (:badarith ())
    (:badmatch ((val erl-val-p)))
    (:function-clause ())
    (:case-clause ((val erl-val-p)))
    (:if-clause ())
    (:try-clause ((val erl-val-p)))
    (:undef ())
    (:badfun ((fun erl-val-p)))
    (:bad-arity ((fun erl-val-p) (args erl-vlst-p)))
    (:timeout-value ())
    (:noproc ())
    (:noconnection ())
    (:nocatch ((val erl-val-p)))
    (:system-limit ())
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

; Erlang Equivalence
; Checks if two Erlang values are equivalent. If one of the values is a rejection,
; the other value is also checked to be a rejection, regardless of its type.
; This is useful for simplifying theorems which have the hypothesis that the 
; given Erlang AST's are well-formed, and thus will not be rejected.
(define erl-equiv ((v1 erl-val-p) (v2 erl-val-p))
  (or (and (equal (erl-val-kind v1) :reject)
           (equal (erl-val-kind v2) :reject))
      (equal v1 v2)))

(defequiv erl-equiv
  :hints (("Goal" :in-theory (enable erl-equiv))))

(set-well-founded-relation o<)