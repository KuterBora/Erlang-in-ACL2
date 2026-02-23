(in-package "ACL2")
(include-book "termination")
(include-book "eval-calls")

(set-induction-depth-limit 1)

; Erlang Evaluator -------------------------------------------------------------

; Evaluate the current continuation and return the next erl-val-klst
;
; Unsupported:
; - Badmatch exception are supposed to return the value that failed to 
;   match. However, for certain instances of this, there is no easy way to 
;   find that value.
; - The Erlang compiler can find out of different clauses of the same expression
;   set the same variable to different values. These variables are called
;   'unsafe' and should not allowed.
;
(define eval-k ((k erl-k-p) (s erl-state-p))
  :returns (ks erl-s-klst-p)
  (b* ((k (erl-k-fix k))
       (fuel (erl-k->fuel k))
       (k (erl-k->kont k))
       ((if (zp fuel)) 
        (make-erl-s-klst :s (update-erl-state->in s (make-erl-val-flimit))))
       (s (erl-state-fix s))
       (s.in (erl-state->in s))
       (s.bind (erl-state->bind s))
       (s.module (erl-state->module s)))
    (kont-case k
      ; Evaluate an expression.
      (:expr (let ((x k.expr))
        (node-case x
          ; if x is an atomic term, simply return its value 
          (:integer (make-erl-s-klst :s (update-erl-state->in s (make-erl-val-integer :val x.val))))
          (:atom    (make-erl-s-klst :s (update-erl-state->in s (make-erl-val-atom :val x.val))))
          (:string  (make-erl-s-klst :s (update-erl-state->in s (string=>erl-cons x.val))))
          (:nil     (make-erl-s-klst :s (update-erl-state->in s (make-erl-val-cons :lst nil))))
          ; if x is a fun, create an anonymous function with a unique name
          ; - The unique name is necessariy for comparison operations, i.e. two anonymous 
          ;   functions with the same clauses but different names are not equal
          (:fun
            (b* ((arity (erl-clause-list->arity x.cls))
                 ((if (null arity))
                  (make-erl-s-klst
                    :s (update-erl-state->in
                        s 
                        (make-erl-val-reject :err "erl-eval: ill-formed fun clauses")))))
                (make-erl-s-klst
                  :s (update-erl-state->in 
                        s
                        (make-erl-val-fun
                          :arity arity
                          :cls x.cls
                          :bind s.bind
                          :module s.module)))))
          ; if x is a list, evaluate car and save cdr in a continuation.
          (:cons 
            (make-erl-s-klst
              :s (update-erl-state->in s (make-erl-val-none))
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr x.hd))
                          (make-erl-k :fuel (1- fuel)
                                      :kont (make-kont-cons :cdr-expr x.tl :bind-0 s.bind)))))
          ; if x is a tuple, evaluate the first element and save the rest in a continuation.
          ; if the tuple is empty, return its value.
          (:tuple
            (if (null x.lst)
                (make-erl-s-klst :s (update-erl-state->in s (make-erl-val-tuple :lst nil)))
                (make-erl-s-klst 
                  :s (update-erl-state->in s (make-erl-val-none))
                  :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr (car x.lst)))
                              (make-erl-k :fuel (1- fuel)
                                          :kont (make-kont-tuple :t-rem (make-node-tuple :lst (cdr x.lst)) 
                                                                 :bind-0 s.bind))))))
          ; if x is a var, lookup its value. If the AST is well-formed, x should be bound.
          (:var
            (if (omap::assoc x.id s.bind)
                (make-erl-s-klst :s (update-erl-state->in s (omap::lookup x.id s.bind)))
                (make-erl-s-klst 
                  :s (update-erl-state->in 
                       s
                       (make-erl-val-reject :err "unbound variable")))))
          (:unop
            (make-erl-s-klst
              :s (update-erl-state->in s (make-erl-val-none))
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr x.expr))
                          (make-erl-k :fuel (1- fuel) :kont (make-kont-unop :op x.op)))))
          ; if x is a binop, evaluate the first operand, save the operator and the second operand
          (:binop
            (make-erl-s-klst
              :s (update-erl-state->in s (make-erl-val-none))
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr x.left))
                          (make-erl-k :fuel (1- fuel) 
                                      :kont (make-kont-binop-expr1 :op x.op 
                                                                   :right x.right
                                                                   :bind-0 s.bind)))))
          ; if x is match, evaluate the rhs a, save the lhs in a continuation.
          (:match
            (make-erl-s-klst
              :s (update-erl-state->in s (make-erl-val-none))
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr x.rhs))
                          (make-erl-k :fuel (1- fuel) :kont (make-kont-match :lhs x.lhs)))))
          ; if x is an if clause, invoke the clause evaluator
          (:if
            (b* (((mv (erl-state rs) body) (eval-clauses nil x.clauses s))
                 ((if (equal (erl-val-kind rs.in) :reject))
                  (make-erl-s-klst :s (update-erl-state->in s rs.in)))
                 ((if (null body))
                  (make-erl-s-klst
                    :s (make-erl-state 
                        :in (make-erl-val-excpt 
                              :err (make-erl-err :class (make-err-class-error)
                                                 :reason (make-exit-reason-if-clause)))))))
                (make-erl-s-klst
                  :s (update-erl-state->in s (make-erl-val-none))
                  :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr (car body)))
                              (make-erl-k :fuel (1- fuel) :kont (make-kont-exprs :exprs (cdr body)))))))
          ; if x is a case, evaluate the expression and save the clauses in a continuation.
          (:case-of
            (make-erl-s-klst
              :s (update-erl-state->in s (make-erl-val-none))
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr x.expr))
                          (make-erl-k :fuel (1- fuel) :kont (make-kont-case-of :clauses x.clauses)))))

          ; if x is remote call, first evaluate the arguments and then handle the call
          (:remote-call
            (make-erl-s-klst 
              :s (update-erl-state->in s (make-erl-val-none))
              :klst
                (list (make-erl-k 
                        :fuel (1- fuel) 
                        :kont (make-kont-function-args-start :args x.args))
                      (make-erl-k
                        :fuel (1- fuel)
                        :kont (make-kont-remote-call :module x.module :call x.fn)))))
          
          ; if x is a fun call, first evaluate the fun expr and then arguments
          (:fun-call
            (make-erl-s-klst 
              :s (update-erl-state->in s (make-erl-val-none))
              :klst
                (list (make-erl-k
                        :fuel (1- fuel)
                        :kont (make-kont-expr :expr x.fun))
                      (make-erl-k
                        :fuel (1- fuel) 
                        :kont (make-kont-fun-call-args :args x.args)))))
          ; if x is a local call, first evaluate the arguments and then handle the call
          (:call
            (make-erl-s-klst 
              :s (update-erl-state->in s (make-erl-val-none))
              :klst
                (list (make-erl-k 
                        :fuel (1- fuel) 
                        :kont (make-kont-function-args-start :args x.args))
                      (make-erl-k
                        :fuel (1- fuel)
                        :kont (make-kont-local-call :call x.fn))))))))
      
      ; Evaluate the cdr of the list, save the result of the car in a contunation
      (:cons
        (make-erl-s-klst
          :s (update-erl-state->bind s k.bind-0)
          :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr k.cdr-expr))
                      (make-erl-k :fuel (1- fuel)
                                  :kont (make-kont-cons-merge :car-val s.in 
                                                              :car-bind s.bind)))))
      ; When both the car and cdr of the list are evaluated, merge the results.
      (:cons-merge
        (if (equal (erl-val-kind s.in) :cons)
            (if (omap::compatiblep s.bind k.car-bind)
                (make-erl-s-klst 
                  :s (update-erl-state->in-bind 
                        s 
                        (make-erl-val-cons :lst (cons k.car-val (erl-val-cons->lst s.in)))
                        (omap::update* s.bind k.car-bind)))
                (make-erl-s-klst
                  :s (update-erl-state->in
                       s
                       (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val s.in))))))
            (make-erl-s-klst 
              :s (update-erl-state->in 
                   s 
                   (make-erl-val-reject :err "cons-merge expects list, pairs are not supported")))))
      
      ; Evaluate the rest of the tuple, save the previous element in a continuation. 
      (:tuple
        (make-erl-s-klst
          :s (update-erl-state->bind s k.bind-0)
          :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr k.t-rem))
                      (make-erl-k :fuel (1- fuel)
                                  :kont (make-kont-tuple-merge :t-hd s.in 
                                                               :t-bind s.bind)))))
      ; When every element of a tuple has been evaluated, start merging the results.
      (:tuple-merge
        (if (equal (erl-val-kind s.in) :tuple)
            (if (omap::compatiblep s.bind k.t-bind)
                (make-erl-s-klst 
                  :s (update-erl-state->in-bind 
                        s
                        (make-erl-val-tuple :lst (cons k.t-hd (erl-val-tuple->lst s.in)))
                        (omap::update* s.bind k.t-bind)))
                (make-erl-s-klst
                  :s (update-erl-state->in 
                       s 
                       (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val s.in))))))
            (make-erl-s-klst 
              :s (update-erl-state->in 
                   s 
                   (make-erl-val-reject :err "tuple-merge expects tuple")))))

      ; Apply unop to the evalutaed operand.
      (:unop (make-erl-s-klst :s (update-erl-state->in s (apply-erl-unop k.op s.in))))

      ; Evaluate the second operand of a binop, save the operator and value of the first operand                                                    
      (:binop-expr1 
        (make-erl-s-klst
          :s (update-erl-state->bind s k.bind-0)
          :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr k.right))
                      (make-erl-k :fuel (1- fuel) 
                                  :kont (make-kont-binop-expr2 :op k.op 
                                                               :val s.in
                                                               :left-bind s.bind)))))
      ; Apply the binop to the evaluated operands
      (:binop-expr2
        (if (omap::compatiblep s.bind k.left-bind)
            (make-erl-s-klst 
              :s (update-erl-state->in-bind
                   s
                   (apply-erl-binop k.op k.val s.in)
                   (omap::update* s.bind k.left-bind)))
                (make-erl-s-klst
                  :s (update-erl-state->in
                      s 
                      (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val s.in)))))))
      
      ; Once rhs is evaluated, match it to lhs
      (:match
        (b* (((erl-state ms) (eval-match k.lhs s))
             
             ((if (and (equal (erl-val-kind ms.in) :excpt)
                       (equal (exit-reason-kind (erl-err->reason (erl-val-excpt->err ms.in))) 
                              :badmatch)))
              (make-erl-s-klst
                :s (update-erl-state->in
                    s 
                    (make-erl-val-excpt 
                      :err (make-erl-err :class (make-err-class-error) 
                                         :reason (make-exit-reason-badmatch :val s.in)))))))
            (make-erl-s-klst :s (update-erl-state->in-bind s ms.in ms.bind))))
      
      ; Once the expression is evaluated, invoke the clause-evaluator.
      (:case-of
        (b* (((mv (erl-state rs) body) (eval-clauses (list s.in) k.clauses s))
             ((if (equal (erl-val-kind rs.in) :reject))
              (make-erl-s-klst :s (update-erl-state->in s rs.in)))
             ((if (null body))
              (make-erl-s-klst
                :s (update-erl-state->in
                    s
                    (make-erl-val-excpt 
                      :err (make-erl-err :class (make-err-class-error)
                                         :reason (make-exit-reason-case-clause :val s.in)))))))
            (make-erl-s-klst
              :s (update-erl-state->bind s rs.bind)
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr (car body)))
                          (make-erl-k :fuel (1- fuel) :kont (make-kont-exprs :exprs (cdr body)))))))
      
      ; Move to the next expression to be evaluated.
      (:exprs
        (if (null k.exprs)
            (make-erl-s-klst :s s)
            (make-erl-s-klst 
              :s s 
              :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr (car k.exprs)))
                          (make-erl-k :fuel (1- fuel) :kont (make-kont-exprs :exprs (cdr k.exprs)))))))
      
      ; Start evaluating function arguments. If there are no arguments, return empty list.
      (:function-args-start 
        (if (null k.args)
            (make-erl-s-klst :s (update-erl-state->in s (make-erl-val-cons :lst nil)))
            (make-erl-s-klst 
              :s (update-erl-state->in s (make-erl-val-none))
              :klst (list (make-erl-k 
                            :fuel (1- fuel) 
                            :kont (make-kont-expr :expr (car k.args)))
                          (make-erl-k
                            :fuel (1- fuel) 
                            :kont (make-kont-function-args :done nil :rest (cdr k.args)))))))
                       
      ; If all arguments are evaluated, return the list of argument values.
      ; Otherwise, evaluate the next argument.
      ; - To return the argument values in an erl-state, wrap them in an erl-val-cons
      (:function-args
        (if (null k.rest)
            (make-erl-s-klst 
              :s (update-erl-state->in s (make-erl-val-cons :lst (cons s.in k.done))))
            (make-erl-s-klst 
              :s (update-erl-state->in s (make-erl-val-none))
              :klst (list (make-erl-k 
                            :fuel (1- fuel) 
                            :kont (make-kont-expr :expr (car k.rest)))
                          (make-erl-k 
                            :fuel (1- fuel) 
                            :kont (make-kont-function-args 
                                    :done (cons s.in k.done)
                                    :rest (cdr k.rest)))))))
      
      ; Call a local function after the arguments have been evaluated
      (:local-call
        (b* (((if (not (equal (erl-val-kind s.in) :cons)))
              (make-erl-s-klst 
                :s (update-erl-state->in 
                     s
                     (make-erl-val-reject :err "Local call: invalid arg list."))))
             ; Obtain the args from the state. They are reversed because they are
             ; evaluated in order and accumulated with cons.
             (args (rev (erl-val-cons->lst s.in)))
             ((mv (erl-state rs) body) 
              (eval-local-call
                (update-erl-state->in s (make-erl-val-none))
                k.call 
                args))
             ; if the body is nil, return the value produced by call evaluation.
             ((if (null body)) (make-erl-s-klst :s rs)))
            ; Otherwise, continue with the function body
            (make-erl-s-klst
              :s (update-erl-state->in rs (make-erl-val-none))
              :klst (list (make-erl-k 
                            :fuel (1- fuel)
                            :kont (make-kont-exprs :exprs body))
                          (make-erl-k
                            :fuel (1- fuel) 
                            :kont (make-kont-function-return :bind s.bind :module s.module))))))
      
      ; Call a remote function after the arguments have been evaluated
      (:remote-call
        (b* (((if (not (equal (erl-val-kind s.in) :cons)))
              (make-erl-s-klst 
                :s (update-erl-state->in 
                     s
                     (make-erl-val-reject :err "Remote call: invalid arg list."))))
             ; Obtain the args from the state. They are reversed because they are
             ; evaluated in order and accumulated with cons.
             (args (rev (erl-val-cons->lst s.in)))
             ((mv (erl-state rs) body) 
              (eval-remote-call
                (update-erl-state->in s (make-erl-val-none))
                k.module
                k.call
                args))
             ; if the body is nil, return the value produced by call evaluation.
             ((if (null body)) (make-erl-s-klst :s rs)))
            ; Otherwise, continue with the function body
            (make-erl-s-klst
              :s (update-erl-state->in rs (make-erl-val-none))
              :klst (list (make-erl-k 
                            :fuel (1- fuel)
                            :kont (make-kont-exprs :exprs body))
                          (make-erl-k
                            :fuel (1- fuel) 
                            :kont (make-kont-function-return :bind s.bind :module s.module))))))
      
      ; Evalute the arguments to an anonymous call after the fun expression has been evaluated.
      (:fun-call-args
        (b* (((if (not (equal (erl-val-kind s.in) :fun)))
              (make-erl-s-klst
                :s (update-erl-state->in
                  s
                  (make-erl-val-excpt 
                      :err (make-erl-err :class (make-err-class-error)
                                         :reason (make-exit-reason-badfun :fun s.in)))))))
            (make-erl-s-klst 
              :s (update-erl-state->in s (make-erl-val-none))
              :klst
                (list (make-erl-k 
                        :fuel (1- fuel) 
                        :kont (make-kont-function-args-start :args k.args))
                      (make-erl-k
                        :fuel (1- fuel)
                        :kont (make-kont-fun-call :fun s.in))))))
      
      ; Call an anonymous function after the arguments have been evaluated
      (:fun-call
        (b* (((if (not (equal (erl-val-kind s.in) :cons)))
              (make-erl-s-klst 
                :s (update-erl-state->in 
                     s
                     (make-erl-val-reject :err "Fun call: invalid arg list."))))
             ; Obtain the args from the state. They are reversed because they are
             ; evaluated in order and accumulated with cons.
             (args (rev (erl-val-cons->lst s.in)))
             ((mv (erl-state rs) body) 
              (eval-fun-call (update-erl-state->in s (make-erl-val-none)) k.fun args))
             ; if the body is nil, return the value produced by call evaluation.
             ((if (null body)) (make-erl-s-klst :s rs)))
            ; Otherwise, continue with the function body
            (make-erl-s-klst
              :s (update-erl-state->in rs (make-erl-val-none))
              :klst (list (make-erl-k 
                            :fuel (1- fuel)
                            :kont (make-kont-exprs :exprs body))
                          (make-erl-k
                            :fuel (1- fuel) 
                            :kont (make-kont-function-return :bind s.bind :module s.module))))))


      ; Once a call returns, return to the correct module and scope
      (:function-return (make-erl-s-klst :s (update-erl-state->bind-mod s k.bind k.module))))))


; calls to eval-k either return a tuple of two contunuations, or an empty list
(defrule eval-k-decreases-fuel
  (implies 
    (and (erl-state-p s) (erl-k-p k))
    (or (null (erl-s-klst->klst (eval-k k s)))
        (and (tuplep 2 (erl-s-klst->klst (eval-k k s)))
              (equal (erl-k->fuel (car (erl-s-klst->klst (eval-k k s)))) 
                    (- (erl-k->fuel k) 1))
              (equal (erl-k->fuel (cadr (erl-s-klst->klst (eval-k k s)))) 
                    (- (erl-k->fuel k) 1))
              (equal (cdr (erl-s-klst->klst (eval-k k s))) 
                    (cons (cadr (erl-s-klst->klst (eval-k k s))) nil)))))
  :enable eval-k)


; Eval-op decreases the klst-measure
(defrule eval-k-decreases-klst-measure
  (b* ((klst (erl-klst-fix klst))
        (x (erl-state-fix x))
        ((if (null klst)) t))
    (l< (klst-measure (append (erl-s-klst->klst (eval-k (car klst) x))
                              (cdr klst)))
        (klst-measure klst)))
  :enable eval-k
  :use (:functional-instance eval-op-decreases-klst-measure  
      (eval-op eval-k)
      (eval-result-p erl-s-klst-p)
      (eval-result->klst erl-s-klst->klst)
      (erl-result-p erl-state-p)
      (erl-result-fix erl-state-fix))) 


; Recursively apply the next continuation to the state produced by the previous.
(define apply-k ((s erl-state-p) (klst erl-klst-p))
  :returns (r erl-state-p)
  :well-founded-relation l<
  :measure (klst-measure (erl-klst-fix klst))
  (b* ((s (erl-state-fix s))
       (klst (erl-klst-fix klst))
       (s.in (erl-val-fix (erl-state->in s)))
       ; The evaluator has run out of fuel
       ((if (equal (erl-val-kind s.in) :flimit)) s)
       ; The evaluator has encountered an internal error
       ((if (equal (erl-val-kind s.in) :reject)) s)
       ; TODO: exception handling (catch, try-catch)
       ((if (equal (erl-val-kind s.in) :excpt)) s)
       ((if (endp klst)) s)
       ((cons khd ktl) klst)
       ((erl-s-klst ks) (eval-k khd s)))
    (apply-k ks.s (append ks.klst ktl)))
  :hints (("Goal" :use ((:instance eval-k-decreases-klst-measure (klst klst) (x s)))
                  :in-theory (disable klst-measure eval-k-decreases-klst-measure))))