(in-package "ACL2")
(include-book "../erl-eval")
(include-book "std/testing/assert-equal" :DIR :SYSTEM)

; This file contains some tests for evaluating anonymous function calls.

; TODO: 
; This file probably does not have enough tests. Especially for error conditions.


; Basic Anonymous Function -----------------------------------------------------

(assert-equal
  (apply-k 
    (make-erl-state) 
    (list 
      (make-erl-k 
        :fuel 10000 
        :kont 
          (make-kont-exprs 
            :exprs 
              '((:match 
                  (:var F) 
                  (:fun (((cases (:var X)) 
                          (guards) 
                          (body (:binop + (:var X) (:integer 1)))))))
                (:fun-call (:var F) ((:integer 1))))))))

  (update-erl-state->in-bind
    (make-erl-state)
    '(:integer 2)
    '((F :FUN 1
         (((CASES (:VAR X))
           (GUARDS)
           (BODY (:BINOP + (:VAR X) (:INTEGER 1)))))
         NIL LOCAL))))


; Remote Anonymous Function ----------------------------------------------------

; Test World
(encapsulate nil
  (local
    (define test-world ()
      :returns (w world-p)
      '((funs
          (attrs (module . funs)
                (export ((name . fn1) (arity . 2))
                        ((name . makeFun) (arity . 0)))
                (import))
          (fn-defns
            (((name . fn1) (arity . 2))
            ((cases (:var X) (:var Y))
              (guards)
              (body (:binop > (:var X) (:var Y)))))
            (((name . makeFun) (arity . 0))
            ((cases)
              (guards)
              (body (:fun (((cases (:var X) (:var Y)) 
                            (guards) 
                            (body (:call fn1 ((:var X) (:var Y))))))))))))
        (local
          (attrs (module . local)
                (export)
                (import))
          (fn-defns)))))

  (assert-equal
    (apply-k 
      (make-erl-state
        :world (test-world))
      (list
        (make-erl-k
        :fuel 10000 
        :kont 
          (make-kont-exprs
            :exprs 
              '((:match (:var F) (:remote-call funs makeFun nil))
                (:fun-call (:var F) ((:integer 3) (:integer 1)))
                )))))
    (make-erl-state 
      :in '(:atom true)
      :bind '((F :FUN 2
                (((CASES (:VAR X) (:VAR Y))
                  (GUARDS)
                  (BODY (:CALL FN1 ((:VAR X) (:VAR Y))))))
                NIL FUNS))
      :world (test-world))))