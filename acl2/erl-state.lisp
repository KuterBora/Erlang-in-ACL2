(in-package "ACL2")
(include-book "erl-value")
(include-book "erl-kont")

(set-induction-depth-limit 1)

; Erlang State ----------------------------------------------------------------

; Representation of the current State of the Erlang program under evaluation
; TODO: World and Out to represent the admitted forms and sent messages
(fty::defprod erl-state
  ((in erl-val-p :default (make-erl-val-none))
   (bind bind-p :default nil)))

; Each step of the evaluator returns an erl-s-klst where
; - s is an erl-state that is the result of evaulation.
; - klst is the pair of continuations produced by eval-k.
;   If klst is nil, evaluation for the current expression is complete.
(fty::defprod erl-s-klst
  ((s erl-state-p :default (make-erl-state))
   (klst erl-klst-p :default nil)))
