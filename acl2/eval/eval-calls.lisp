(in-package "ACL2")
(include-book "erl-world")
(include-book "erl-state")
(include-book "eval-clauses")

(set-induction-depth-limit 1)

; Evaluate Local Function Calls ------------------------------------------------

; Evaluate a 'local' function call. This means the call was made to a function
; declared within or imported to the current module. Find the corresponding 
; function, its macthing clause, and return the function body. Otherwise, return
; function_clause exception.
;
; - rs: is used to return exceptions, rejections, and BIF results, in which case 
;   body is set to nil.
; - body: will be set to the body of the matching function clause if there is one,
;   and if there is no rejection.
;
; Order of function lookup:
; - First, the local definitions are checked. It is assumed that there should
;   not be duplicate function definitions.
; - If not found locally, then the imported functions are checked for a 
;   match. If there is one, then the module of the imported function is 
;   checked -- wheter it has the said function and also exports it. It is
;   assumed that there are no duplicate imports or defintions.
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
;    However, experiments show that local calls to undefined calls are discovered
;    during compilation. This means, for undefined function x,
;    - When x is defined locally, call to x() will return a rejection.
;    - If x is imported, call to x() will return an undef exception. This is 
;      also true if the module x was imported from is undefined.  
;  
(define eval-local-call ((s erl-state-p) (call symbolp) (args erl-vlst-p))
  :returns (mv (rs erl-state-p) (body expr-list-p))
  (b* (((erl-state s) (erl-state-fix s))
       (call (symbol-fix call))
       (args (erl-vlst-fix args))

       ; Some useful bindings for simplification 
       (arity (len args))
       (fn (make-fn :name call :arity arity))
       
       ; Rejection to throw when the function is not defined and would have
       ; caused a compile error.
       (reject 
        (update-erl-state->in 
          s
          (make-erl-val-reject :err "eval-local-call: function is not defined.")))

       ; Exception to throw when a function is defined but there 
       ; are no matching clauses 
       (function-clause 
         (update-erl-state->in 
           s 
           (make-erl-val-excpt 
             :err
               (make-erl-err
                 :class (make-err-class-error)
                 :reason (make-exit-reason-function-clause)))))

       ; The module must exist.
       ((unless (omap::assoc s.module s.world)) (mv reject nil))
       
       ; Obtain the module
       ((module module) (omap::lookup s.module s.world))
       (imports (attrs->import module.attrs))
      
       ; Check the module's defintions for the function
       ; The body of the function will not have access to current bindings
       ((if (omap::assoc fn module.fn-defns))
        (b* (((mv (erl-state rs) body) 
              (eval-clauses 
                args 
                (omap::lookup fn module.fn-defns)
                (update-erl-state->bind s nil)))
             ((if (not (wf-state-p rs))) (mv rs nil))
             ((if (null body)) 
              (mv function-clause nil)))
            (mv rs body)))
      
       ; Check the module's imports for the function
       ((if (omap::assoc fn imports))
        (b* ((imod-name (omap::lookup fn imports))
             
             ; Exception to throw when the function is not defined and would not ahve
             ; caused a compile error.
             (undef
               (update-erl-state->in 
                 s 
                 (make-erl-val-excpt 
                   :err
                     (make-erl-err
                       :class (make-err-class-error)
                       :reason (make-exit-reason-undef)
                       :stack (list imod-name call arity)))))

             ((unless (omap::assoc imod-name s.world)) (mv undef nil))
             ((module imod) (omap::lookup imod-name s.world))
             (exports (attrs->export imod.attrs))

             ; If the function was not exported, throw an undef error
             ((unless (member fn exports :test 'equal)) (mv undef nil))
            
             ; If the function was exported, the Erlang compiler
             ; would have ensured that it is defined.
             ((unless (omap::assoc fn imod.fn-defns)) 
              (mv
                (update-erl-state->in
                  s
                  (make-erl-val-reject 
                    :err "eval-local-call: module exports function, but it is not defined."))
                 nil))
             
             ; The body of the function will not have access to current bindings
             ((mv (erl-state rs) body)
              (eval-clauses
                args
                (omap::lookup fn imod.fn-defns)
                (update-erl-state->bind-mod s nil 'imod-name)))
              ((if (not (wf-state-p rs))) (mv rs nil))
              ((if (null body)) (mv function-clause nil)))
            (mv rs body)))

       ; Check if the function is a BIF
       ((if (erl-bif-p fn)) (mv (update-erl-state->in s (eval-bif fn args s)) nil)))
    (mv reject nil))
  
  ///
    (defcong erl-state-equiv equal (eval-local-call s f args) 1)
    (defcong symbol-equiv equal (eval-local-call s f args) 2)
    (defcong erl-vlst-equiv equal (eval-local-call s f args) 3))


; Evaluate Remote Function Calls -----------------------------------------------

; Evaluate a 'remote' function call. This means the call was made to a function
; declared outisde current module. Find the corresponding function, its macthing 
; clause, and return the function body. Otherwise, return function_clause exception.
;
; - rs: is used to return exceptions and rejections, in which case body is set 
;   to nil.
; - body: will be set to the body of the matching function clause if there is one,
;   and if there is no rejection.
;
; Implementation:
; - First, check that the module exists and has the function in its definitions
;   and also exports it.
; - Evaluate the function clauses with the args. 
;
; Remark: 
;  - The Erlang reference manual states that the exception stack is
;    only for debugging purposes and has no guarantees. The only exception 
;    to this rule is the class 'error' with the reason 'undef' which is 
;    guaranteed to include the Module, Function and Arity of the attempted
;    function as the first stacktrace entry.
;
(define eval-remote-call ((s erl-state-p) (module symbolp) (call symbolp) (args erl-vlst-p))
  :returns (mv (rs erl-state-p) (body expr-list-p))
  (b* (((erl-state s) (erl-state-fix s))
       (module (symbol-fix module))
       (call (symbol-fix call))
       (args (erl-vlst-fix args))
       (arity (len args))
       (fn (make-fn :name call :arity arity))
       
       ; Exception to throw when the function is not defined and would not ahve
       ; caused a compile error.
       (undef
         (update-erl-state->in 
           s 
           (make-erl-val-excpt 
             :err
               (make-erl-err
                 :class (make-err-class-error)
                 :reason (make-exit-reason-undef)
                 :stack (list module call arity)))))
       
       ; Exception to throw when a function is defined but there 
       ; are no matching clauses 
       (function-clause 
         (update-erl-state->in 
           s 
           (make-erl-val-excpt 
             :err
               (make-erl-err
                 :class (make-err-class-error)
                 :reason (make-exit-reason-function-clause)))))

       ; The module must exist.
       ((unless (omap::assoc module s.world)) (mv undef nil))
       
       ; Get the remote module.
       ((module rmod) (omap::lookup module s.world))
       (exports (attrs->export rmod.attrs))
      
       ; Check the module's defintions for the function
       ; - The function also needs to have been exported
       ; - The function will not have access to local bindings
       ((if (and (omap::assoc fn rmod.fn-defns) (member fn exports :test 'equal)))
        (b* (((mv (erl-state rs) body) 
              (eval-clauses
               args
               (omap::lookup fn rmod.fn-defns)
               (update-erl-state->bind-mod s nil module)))
             ((if (not (wf-state-p rs))) (mv rs nil))
             ((if (null body)) (mv function-clause nil)))
            (mv rs body))))
    (mv undef nil))
  ///
    (defcong erl-state-equiv equal (eval-remote-call s m f args) 1)
    (defcong symbol-equiv equal (eval-remote-call s m f args) 2)
    (defcong symbol-equiv equal (eval-remote-call s m f args) 3)
    (defcong erl-vlst-equiv equal (eval-remote-call s m f args) 4))


; Evaluate Anonymous Function Calls --------------------------------------------

; Erlang reference manual defines anonymous functions, 'fun expressions', as:
; 
; - A fun expression begins with the keyword fun and ends with the keyword end. 
;   Between them is to be a function declaration, similar to a regular function 
;   declaration, except that the function name is optional and is to be a 
;   variable, if any.
;
; - Variables in a fun head shadow the function name and both shadow variables in
;   the function clause surrounding the fun expression. Variables bound in a fun
;   body are local to the fun body.
;
; - The return value of the expression is the resulting fun.
;
; Implementation:
; - Any call that is not a local or remote call must be a function call. So, as a 
;   precondition, it assumed that any function that has an expression to be called
;   that is not an Atom or {remote, Atom} where Atom is a symbol, has been parsed as
;   a (:fun-call Expr Args) when converted to ACL2. This makes the control flow a
;   bit easier to follow.
; - If the Expr to be called does not evaluate to a fun expression, then the badfun 
;   exception is thrown.
; - Otherwise, this is treated as a local call. If the fun was defined in a module, 
;   it will be treated as local call within that module, i.e. it will have access to 
;   the functions in that module.
;
; Not Supported:
; - Named funs are currently not supported. However, adding them should be trivial
; - funs of the form 'fun Module:Name/Arity" are not currently supported.

(define eval-fun-call ((s erl-state-p) (fun erl-val-p) (args erl-vlst-p))
  :returns (mv (rs erl-state-p) (body expr-list-p))
  (b* ((s (erl-state-fix s))
       (fun (erl-val-fix fun))
       (args (erl-vlst-fix args))
       (arity (len args))

       ; Throw the badfun exception if the called expression is not a fun.
       ((if (not (erl-fun-p fun)))
        (mv 
          (update-erl-state->in 
            s 
            (make-erl-val-excpt 
                      :err (make-erl-err :class (make-err-class-error)
                                         :reason (make-exit-reason-badfun :fun fun))))
          nil))
        
        ; Throw the badarity exception if the arities of the fun and the
        ; arguments do not match.
        ((if (not (equal (erl-val-fun->arity fun) arity)))
          (mv 
            (update-erl-state->in 
              s 
              (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error)
                                          :reason (make-exit-reason-badarity :fun fun))))
            nil))

       ; Exception to throw when the fun is well-formed but there 
       ; are no matching clauses 
       (function-clause 
         (update-erl-state->in 
           s 
           (make-erl-val-excpt 
             :err
               (make-erl-err
                 :class (make-err-class-error)
                 :reason (make-exit-reason-function-clause)))))

      ((mv (erl-state rs) body)
       (eval-clauses
        args
        (erl-val-fun->cls fun)
        (update-erl-state->bind-mod 
          s 
          (erl-val-fun->bind fun)
          (erl-val-fun->module fun))))
      ((if (not (wf-state-p rs))) (mv rs nil))
      ((if (null body)) (mv function-clause nil))

      ; Remark: Badmatch exceptions are supposed to return the value that failed to 
      ; match. This is currently not supported. Instead, return the whole fun.
      ((unless (omap::compatiblep rs.bind (erl-val-fun->bind fun))) 
       (mv
        (update-erl-state->in 
           s 
           (make-erl-val-excpt 
             :err
               (make-erl-err
                 :class (make-err-class-error)
                 :reason (make-exit-reason-badmatch :val fun))))
        nil)))
    (mv rs body))
  ///
    (defcong erl-state-equiv equal (eval-fun-call s f args) 1)
    (defcong erl-val-equiv equal (eval-fun-call s f args) 2)
    (defcong erl-vlst-equiv equal (eval-fun-call s f args) 3))