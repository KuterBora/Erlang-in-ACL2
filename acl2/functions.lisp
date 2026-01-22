(in-package "ACL2")
(include-book "erl-world")

(set-induction-depth-limit-1)

; When a function M:F/N is called, first the module M is located in the World.
; If the call is local, the module key is set to 'LOCAL' -- module names in Erlang
; are atoms which use lowercase letter only, so this name should be unique among
; valid modules.
; 
; If module is not found:
;
; deal with imports
;
; Look for function
;
; if function is not found
; 
; function should have access to iys module
;
; todo 

; If the function cannot be found, an undef runtime error occurs. Notice that the function must be exported to be visible outside the module it is defined in.,
;
;
;


; Evaluate Local Function Calls ------------------------------------------------

(define eval-local-call ((s erl-state-p) (call symbolp) (args erl-vlst-p))
  :returns ((mv rs body))

  (b* ((s (erl-state-fix s))
       (call (symbol-fix call))
       (args (erl-vlst-fix args))
       (s.bind (erl-state->bind s))
       (s.module (erl-state->module s))
       (s.world (erl-state-world s))
       ((unless (omap::assoc s.module s.world))
        (mv (make-erl-state 
              :in (make-erl-value-excpt :class (make-err-class-error)
                                        :reason (make-exit-reason-fun-clause)
                                        :stack TODO)
              TODO)
            nil))
       (module (omap::lookup s.module s.world))
       
       (arity (len args))
       
        
       )
      
    
    
    
    ))















; Evaluate Remote Function Calls -----------------------------------------------