(in-package "ACL2")
(include-book "erl-world")
(include-book "erl-state")
(include-book "eval-clauses")

(set-induction-depth-limit 1)

; Evaluate Local Function Calls ------------------------------------------------

; TODO: UPDATE desc
;  verify guards

; Evaluate a 'local' function call. This means the call was made to a function
; declared within or imported to the current module. Find the corresponding 
; function, its macthing clause, and return the function body. Otherwise, return
; function_clause exception.
;
; - rs: is used to return exceptions and rejections, in which case body is set 
;   to nil.
; - body: will be set the matching function clause if there is one, and if there
;   is no rejection.
;
; Order of function lookup:
; - First, the local definitions are checked. It is assumed that there should
;   not be duplicate function definitions.
; - If not found locally, then the imported functions are checked for a 
;   match. If there is one, then the module of the imported function is 
;   checked -- wheter it has the said function and also exports it. It is
;   assumed that there are no duplicate imports, or defintions for imports.
; - If there is still no match, it is checked whether the function is a BIF.
;   It is also assumed that no definitions or imports conflict with BIFs.
; - Else, function_clause exception is returned.
;
; Remark: 
;  - The Erlang reference manual states that the exception stack is
;    only for debugging purposes and has no guarantees. The only exception 
;    to this rule is the class 'error' with the reason 'undef' which is 
;    guaranteed to include the Module, Function and Arity of the attempted
;    function as the first stacktrace entry.
;
(define eval-local-call ((s erl-state-p) (call symbolp) (args erl-vlst-p))
  :returns (mv (rs erl-state-p) (body expr-list-p))
  (b* ; Fix the arguments
      ((s (erl-state-fix s))
       (call (symbol-fix call))
       (args (erl-vlst-fix args))

       ; Some useful bindings for simplification 
       (s.module (erl-state->module s))
       (s.world (erl-state->world s))
       (arity (len args))
       (fn (make-fn :name call :arity arity))
       (undef 
        (update-erl-state->in 
          s 
          (make-erl-val-excpt 
            :err
              (make-erl-err
                :class (make-err-class-error)
                :reason (make-exit-reason-undef)
                :stack (list s.module call arity)))))

       ; The module must exist.
       ((unless (omap::assoc s.module s.world)) (mv undef nil))
       
       ; Obtain the module
       (module (omap::lookup s.module s.world))
       (fn-defns (module->fn-defns module))
       (attrs (module->attrs module))
       (imports (attrs->import attrs))
      
       ; Check the module's defintions for the function
       ; The body of the function will not have access to current bindings
       ((if (omap::assoc fn fn-defns))
        (b* (((mv v b body) 
              (eval-clauses 
               args 
               (omap::lookup fn fn-defns)
               nil))
             ((if (equal (erl-val-kind v) :reject)) (mv (update-erl-state->in s v) nil))
             ((if (null body)) 
              (mv (update-erl-state->in
                    s
                    (make-erl-val-excpt 
                      :err 
                        (make-erl-err :class (make-err-class-error)
                                      :reason (make-exit-reason-function-clause))))
                  nil)))
            (mv (update-erl-state->in-bind s v b) body)))
      
       ; Check the module's imports for the function
       ((if (omap::assoc fn imports))
        (b* ((imod-name (omap::lookup fn imports))
             ((unless (omap::assoc imod-name s.world))
              (mv
                (update-erl-state->in
                  s
                  (make-erl-val-reject 
                    :err "eval-local-call: Ill-formed module imports."))
                 nil))
             (imod (omap::lookup imod-name s.world))
             (idefns (module->fn-defns imod))
             (iattrs (module->attrs imod))
             (exports (attrs->export iattrs))

             ; The function must have been exported
             ((unless (member fn exports :test 'equal)) (mv undef nil))
            
             ; If the function was exported, the Erlang compiler
             ; would have ensured that it is defined.
             ((unless (omap::assoc fn idefns)) 
              (mv
                (update-erl-state->in
                  s
                  (make-erl-val-reject 
                    :err "eval-local-call: module exports function, but it is not defined."))
                 nil))
             
             ; The body of the function will not have access to current bindings
             ((mv v b body)
              (eval-clauses
                args
                (omap::lookup fn idefns)
                nil))
              ((if (equal (erl-val-kind v) :reject)) (mv (update-erl-state->in s v) nil))
              ((if (null body)) 
               (mv (update-erl-state->in
                    s
                    (make-erl-val-excpt 
                      :err 
                        (make-erl-err :class (make-err-class-error)
                                      :reason (make-exit-reason-function-clause))))
                   nil)))
            (mv (update-erl-state->in-bind-mod s v b imod-name) body)))

       ; Check if the function is a BIF
       ((if (erl-bif-p fn)) (mv (update-erl-state->in s (eval-bif fn args)) nil)))
    (mv undef nil)))


; Evaluate Remote Function Calls -----------------------------------------------

; TODO:
; - defintion
; - guards
;
; When a function M:F/N is called, first the module M is located in the World.
; If the call is local, the module key is set to 'LOCAL' -- module names in Erlang
; are atoms which use lowercase letter only, so this name should be unique among
; valid modules.
; 

(define eval-remote-call ((s erl-state-p) (module symbolp) (call symbolp) (args erl-vlst-p))
  :returns (mv (rs erl-state-p) (body expr-list-p))
  (b* ; Fix the arguments
      ((s (erl-state-fix s))
       (module (symbol-fix module))
       (call (symbol-fix call))
       (args (erl-vlst-fix args))

       (s.world (erl-state->world s))
       (arity (len args))
       (fn (make-fn :name call :arity arity))
       (undef 
        (update-erl-state->in 
          s 
          (make-erl-val-excpt 
            :err
              (make-erl-err
                :class (make-err-class-error)
                :reason (make-exit-reason-undef)
                :stack (list module call arity)))))

       ; The module must exist.
       ((unless (omap::assoc module s.world)) (mv undef nil))
       
       ; Obtain the module
       (rmod (omap::lookup module s.world))
       (fn-defns (module->fn-defns rmod))
       (attrs (module->attrs rmod))
       (exports (attrs->export attrs))
      
       ; Check the module's defintions for the function
       ; - The function also needs to have been exported
       ; - The function will not have access to local bindings
       ((if (and (omap::assoc fn fn-defns) (member fn exports :test 'equal)))
        (b* (((mv v b body) 
              (eval-clauses 
               args
               (omap::lookup fn fn-defns)
               nil))
             ((if (equal (erl-val-kind v) :reject)) (mv (update-erl-state->in s v) nil))
             ((if (null body)) 
              (mv (update-erl-state->in
                    s
                    (make-erl-val-excpt 
                      :err 
                        (make-erl-err :class (make-err-class-error)
                                      :reason (make-exit-reason-function-clause))))
                  nil)))
            (mv (update-erl-state->in-bind-mod s v b module) body))))
    (mv undef nil)))