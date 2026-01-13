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

; Evaluate Function Calls ------------------------------------------------------