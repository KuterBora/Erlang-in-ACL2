(in-package "ACL2")
(include-book "erl-value")
(include-book "erl-kont")
(include-book "erl-world")

(set-induction-depth-limit 1)

; Erlang State ----------------------------------------------------------------

; Representation of the current State of the Erlang program under evaluation
; TODO: Outbox, self
(fty::defprod erl-state
  ((in erl-val-p :default (make-erl-val-none))
   (bind bind-p :default nil)
   (world world-p :default (omap::from-lists '(local) (list (make-module))))
   (module symbolp :default 'local)))

; Each step of the evaluator returns an erl-s-klst where
; - s is an erl-state that is the result of evaulation.
; - klst is the pair of continuations produced by eval-k.
;   If klst is nil, evaluation for the current expression is complete.
(fty::defprod erl-s-klst
  ((s erl-state-p :default (make-erl-state))
   (klst erl-klst-p :default nil)))


; Helpers for Setting Fields --------------------------------------------------

; Remark: 
; - fty::change might be good alternate, but defining these accessors 
;   might provide more felixibility -- theorems can be proven and the functions
;   can be disabled. 

(define update-erl-state->in ((s erl-state-p) (in erl-val-p))
  :returns (rs erl-state-p)
  (b* ((s (erl-state-fix s))
       (in (erl-val-fix in)))
      (make-erl-state :in in
                      :bind (erl-state->bind s)
                      :world (erl-state->world s)
                      :module (erl-state->module s)))
  ///
    (defrule update-erl-state->in-fields
      (implies (and (erl-state-p s) (erl-val-p val))
              (equal (erl-state->in (update-erl-state->in s val))
                      val))))

(define update-erl-state->bind ((s erl-state-p) (bind bind-p))
  :returns (rs erl-state-p)
  (b* ((s (erl-state-fix s))
       (bind (bind-fix bind)))
      (make-erl-state :in (erl-state->in s)
                      :bind bind
                      :world (erl-state->world s)
                      :module (erl-state->module s)))
  ///
    (defrule update-erl-state->bind-fields
      (implies (and (erl-state-p s) (bind-p b))
              (equal (erl-state->in (update-erl-state->bind s b))
                      (erl-state->in s)))))

(define update-erl-state->in-bind ((s erl-state-p) (in erl-val-p) (bind bind-p))
  :returns (rs erl-state-p)
  (b* ((s (erl-state-fix s))
       (in (erl-val-fix in))
       (bind (bind-fix bind)))
      (make-erl-state :in in
                      :bind bind
                      :world (erl-state->world s)
                      :module (erl-state->module s))))

(define update-erl-state->mod ((s erl-state-p) (mod symbolp))
  :returns (rs erl-state-p)
  (b* ((s (erl-state-fix s))
       (mod (symbol-fix mod)))
      (make-erl-state :in (erl-state->in s)
                      :bind (erl-state->bind s)
                      :world (erl-state->world s)
                      :module mod)))

(define update-erl-state->bind-mod ((s erl-state-p) (bind bind-p) (mod symbolp))
  :returns (rs erl-state-p)
  (b* ((s (erl-state-fix s))
       (bind (bind-fix bind))
       (mod (symbol-fix mod)))
      (make-erl-state :in (erl-state->in s)
                      :bind bind
                      :world (erl-state->world s)
                      :module mod)))

(define update-erl-state->in-bind-mod ((s erl-state-p) (in erl-val-p) (bind bind-p) (mod symbolp))
  :returns (rs erl-state-p)
  (b* ((s (erl-state-fix s))
       (in (erl-val-fix in))
       (bind (bind-fix bind))
       (mod (symbol-fix mod)))
      (make-erl-state :in in
                      :bind bind
                      :world (erl-state->world s)
                      :module mod)))