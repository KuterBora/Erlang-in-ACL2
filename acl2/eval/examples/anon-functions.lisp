; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "../top")
(include-book "std/testing/assert-equal" :dir :system)

; Simple Anonymous Function ----------------------------------------------------

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
                (:fun-call (:var F) (:cons (:integer 1) (:nil))))))))

  (update-erl-state->in-bind
    (make-erl-state)
    '(:integer 2)
    '((f :fun 1
         (((cases (:var X))
           (guards)
           (body (:binop + (:var X) (:integer 1)))))
         nil local))))


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
                            (body (:call fn1 (:cons (:var X) (:cons (:var Y) (:nil)))))))))))))
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
              '((:match (:var F) (:remote-call funs makeFun (:nil)))
                (:fun-call (:var F) (:cons (:integer 3) (:cons (:integer 1) (:nil)))))))))
    (make-erl-state 
      :in '(:atom true)
      :bind '((f :fun 2
                (((cases (:var X) (:var Y))
                  (guards)
                  (body (:call fn1 (:cons (:var X) (:cons (:var Y) (:nil)))))))
                nil funs))
      :world (test-world))))