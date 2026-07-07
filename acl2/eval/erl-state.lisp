(in-package "ACL2")
(include-book "erl-value")
(include-book "erl-kont")
(include-book "erl-world")

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

(defcong erl-s-klst-equiv equal (erl-s-klst->klst ks) 1)
(defcong erl-s-klst-equiv equal (erl-s-klst->s ks) 1)

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
      (and (equal (erl-state->in (update-erl-state->in s val))
                  (erl-val-fix val))
           (equal (erl-state->bind (update-erl-state->in s val))
                  (erl-state->bind s))
           (equal (erl-state->module (update-erl-state->in s val))
                  (erl-state->module s))
           (equal (erl-state->world (update-erl-state->in s val))
                  (erl-state->world s))))
    
    (defcong erl-state-equiv equal (update-erl-state->in s v) 1))

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
      (and (equal (erl-state->in (update-erl-state->bind s b))
                  (erl-state->in s))
           (equal (erl-state->bind (update-erl-state->bind s b))
                  (bind-fix b))
           (equal (erl-state->module (update-erl-state->bind s b))
                  (erl-state->module s))
           (equal (erl-state->world (update-erl-state->bind s b))
                  (erl-state->world s))))
    
    (defcong erl-state-equiv equal (update-erl-state->bind s b) 1))

(define update-erl-state->in-bind ((s erl-state-p) (in erl-val-p) (bind bind-p))
  :returns (rs erl-state-p)
  (b* ((s (erl-state-fix s))
       (in (erl-val-fix in))
       (bind (bind-fix bind)))
      (make-erl-state :in in
                      :bind bind
                      :world (erl-state->world s)
                      :module (erl-state->module s)))
  ///
    (defrule update-erl-state->in-bind-fields
      (and (equal (erl-state->in (update-erl-state->in-bind s in b))
                  (erl-val-fix in))
           (equal (erl-state->bind (update-erl-state->in-bind s in b))
                  (bind-fix b))
           (equal (erl-state->module (update-erl-state->in-bind s in b)) 
                  (erl-state->module s))
           (equal (erl-state->world (update-erl-state->in-bind s in b)) 
                  (erl-state->world s))))
    
    (defcong erl-state-equiv equal (update-erl-state->in-bind s v b) 1))

(define update-erl-state->mod ((s erl-state-p) (mod symbolp))
  :returns (rs erl-state-p)
  (b* ((s (erl-state-fix s))
       (mod (symbol-fix mod)))
      (make-erl-state :in (erl-state->in s)
                      :bind (erl-state->bind s)
                      :world (erl-state->world s)
                      :module mod))
  ///
    (defrule update-erl-state->mod-fields
      (and (equal (erl-state->module (update-erl-state->mod s mod))
                  (symbol-fix mod))
           (equal (erl-state->in (update-erl-state->mod s mod))
                  (erl-state->in s))
           (equal (erl-state->bind (update-erl-state->mod s mod))
                  (erl-state->bind s))
           (equal (erl-state->world (update-erl-state->mod s mod))
                  (erl-state->world s))))
    
    (defcong erl-state-equiv equal (update-erl-state->mod s m) 1))

(define update-erl-state->bind-mod ((s erl-state-p) (bind bind-p) (mod symbolp))
  :returns (rs erl-state-p)
  (b* ((s (erl-state-fix s))
       (bind (bind-fix bind))
       (mod (symbol-fix mod)))
      (make-erl-state :in (erl-state->in s)
                      :bind bind
                      :world (erl-state->world s)
                      :module mod))
  ///
    (defrule update-erl-state->bind-mod-fields
      (and (equal (erl-state->module (update-erl-state->bind-mod s b mod))
                  (symbol-fix mod))
           (equal (erl-state->bind (update-erl-state->bind-mod s b mod))
                  (bind-fix b))
           (equal (erl-state->in (update-erl-state->bind-mod s b mod))
                  (erl-state->in s))   
           (equal (erl-state->world (update-erl-state->bind-mod s b mod))
                  (erl-state->world s))))
    
    (defcong erl-state-equiv equal (update-erl-state->bind-mod s b m) 1))

(define update-erl-state->in-bind-mod ((s erl-state-p) (in erl-val-p) (bind bind-p) (mod symbolp))
  :returns (rs erl-state-p)
  (b* ((s (erl-state-fix s))
       (in (erl-val-fix in))
       (bind (bind-fix bind))
       (mod (symbol-fix mod)))
      (make-erl-state :in in
                      :bind bind
                      :world (erl-state->world s)
                      :module mod))
  ///
    (defrule update-erl-state->in-bind-mod-fields
      (and (equal (erl-state->in (update-erl-state->in-bind-mod s in b mod))
                  (erl-val-fix in))
           (equal (erl-state->bind (update-erl-state->in-bind-mod s in b mod))
                  (bind-fix b))   
           (equal (erl-state->module (update-erl-state->in-bind-mod s in b mod))
                  (symbol-fix mod))       
           (equal (erl-state->world (update-erl-state->in-bind-mod s in b mod))
                  (erl-state->world s))))
    
    (defcong erl-state-equiv equal (update-erl-state->in-bind-mod s v b m) 1))


; The following rules rewrite chains of erl-state updates to a normalized form 
; which then allows simplifications. For example, updates to erl-state->bind 
; are moved before updates to erl-state->in, and then updates of the same 
; kind are simplified, as the last update will always overwrite the previous.

(defrule update-erl-state-normalize-bind-and-in
  (equal (update-erl-state->in (update-erl-state->bind s b) v)
         (update-erl-state->bind (update-erl-state->in s v) b))
  :enable (update-erl-state->in update-erl-state->bind))

(defrule update-erl-state->in-chain
  (equal (update-erl-state->in (update-erl-state->in s v1) v2)
         (update-erl-state->in s v2))
  :enable update-erl-state->in)

(defrule update-erl-state->bind-chain
  (equal (update-erl-state->bind (update-erl-state->bind s b1) b2)
         (update-erl-state->bind s b2))
  :enable update-erl-state->bind)

(defrule update-erl-state->in-bind-expand
  (equal (update-erl-state->in-bind s v b)
         (update-erl-state->bind (update-erl-state->in s v) b))
  :enable 
    (update-erl-state->in 
     update-erl-state->bind 
     update-erl-state->in-bind))


; Helpers for Utility ---------------------------------------------------------

; Any erl-state that does not contain a rejection, exception, or flimit.
(define wf-state-p ((x erl-state-p))
  :returns (ok booleanp)
  (null (member (erl-val-kind (erl-state->in (erl-state-fix x)))
                '(:flimit :reject :excpt)))
  ///
  (defcong erl-state-equiv equal (wf-state-p x) 1)
  
  (defrule wf-state-p-of-flimit
    (implies (equal (erl-val-kind (erl-state->in s)) :flimit)
             (not (wf-state-p s))))
  
  (defrule wf-state-p-of-reject
    (implies (equal (erl-val-kind (erl-state->in s)) :reject)
             (not (wf-state-p s))))
  
  (defrule wf-state-p-of-excpt
    (implies (equal (erl-val-kind (erl-state->in s)) :excpt)
             (not (wf-state-p s)))))