(in-package "ACL2")
(include-book "../erl-eval")
(include-book "std/testing/assert-equal" :dir :system)

; This file contains some tests for evaluating local and remote function calls

; TODO: 
; This file probably does not have enough tests. Especially for error conditions.

; BIFs -------------------------------------------------------------------------

; (make-node-call :fn 'is_integer :args '((:integer 1)))
; (make-node-call 
;   :fn 'element
;   :args '((:integer 2) (:tuple ((:atom one) (:atom two) (:atom three)))))

(assert-equal
  (apply-k 
    (make-erl-state)
    (list 
      (make-erl-k 
      :fuel 10000 
      :kont (make-kont-expr
              :expr '(:call is_integer (:cons (:integer 1) (:nil)))))))
  (make-erl-state :in '(:atom true)))

(assert-equal
  (apply-k
    (make-erl-state)
    (list 
      (make-erl-k 
      :fuel 10000 
      :kont (make-kont-expr
              :expr '(:call element
                            (:cons (:integer 2)
                                   (:cons (:tuple ((:atom one)
                                                   (:atom two)
                                                   (:atom three)))
                                          (:nil))))))))
  (make-erl-state :in '(:atom two)))


; Example World ---------------------------------------------------------------

; add(X, Y) -> X + Y.
; '((name . adder) (arity . 2))

; Clauses of add(X, Y)
; '(((cases (:var X) (:var Y))
;    (guards)
;    (body (:binop + (:var X) (:var Y)))))

; sum(0) -> 0;
; sum(X) when is_integer(X), X > 0 -> X + sum(X - 1).
; '((name . sum) (arity . 1))

; Clauses of sum(X)
; '(((cases (:integer 0))
;    (guards)
;    (body (:integer 0)))
;   ((cases (:var X))
;    (guards ((:call is_integer ((:var X))) (:binop > (:var X) (:integer 0))))
;    (body (:binop + (:var X) (:call sum ((:binop - (:var X) (:integer 1))))))))

; add*([]) -> 0;
; add*([Hd | Tl]) when is_integer(Hd) ->
;   Rest = add*(Tl),
; ;   add(Hd, Rest).
; '((name . add) (arity . 1))

; Clauses of add*([Hd | Tl])
; '(((cases (:nil))
;    (guards)
;    (body (:integer 0)))
;   ((cases (:cons (:var Hd) (:var Tl)))
;    (guards ((:call is_integer ((:var Hd)))))
;    (body (:match (:var Rest) (:call add* ((:var Tl))))
;          (:call add ((:var Hd) (:var Rest))))))

; Example World

(encapsulate nil
  (local
    (define test-world ()
      :returns (w world-p)
      '((arithm-1
          (attrs (module . arithm-1)
                 (export ((name . add) (arity . 2))
                         ((name . sum) (arity . 1)))
                 (import (((name . bogus-fn1) (arity . 0)) . local)
                         (((name . bogus-fn2) (arity . 0)) . bad-mod)))
          (fn-defns
            (((name . add) (arity . 2))
             ((cases (:var X) (:var Y))
              (guards)
              (body (:binop + (:var X) (:var Y)))))
            (((name . sum) (arity . 1))
             ((cases (:integer 0))
              (guards)
              (body (:integer 0)))
             ((cases (:var X))
              (guards ((:call is_integer (:cons (:var X) (:nil))) 
                      (:binop > (:var X) (:integer 0))))
              (body (:binop 
                      + 
                      (:var X) 
                      (:call sum (:cons (:binop - (:var X) (:integer 1)) 
                                        (:nil)))))))))
        (arithm-2
          (attrs (module . arithm-2)
                 (export ((name . add*) (arity . 1)))
                 (import (((name . add) (arity . 2)) . arithm-1)))
          (fn-defns
            (((name . add*) (arity . 1))
             ((cases (:nil))
              (guards)
              (body (:integer 0)))
             ((cases (:cons (:var Hd) (:var Tl)))
              (guards ((:call is_integer (:cons (:var Hd) (:nil)))))
              (body (:match (:var Rest) (:call add* (:cons (:var Tl) (:nil))))
                    (:call add (:cons (:var Hd)
                                      (:cons (:var Rest) (:nil)))))))))
        (local
          (attrs (module . local)
                 (export)
                 (import))
          (fn-defns)))))

  ; Simple Local Function --------------------------------------------------------

  (assert-equal
    (apply-k 
      (make-erl-state
        :world (test-world)
        :module 'arithm-1)
      (list
        (make-erl-k
        :fuel 10000 
        :kont (make-kont-expr
                :expr '(:call add
                              (:cons (:integer 2)
                                     (:cons (:integer 2) (:nil))))))))
    (make-erl-state 
      :in '(:integer 4)
      :world (test-world)
      :module 'arithm-1))


  ; Simple Remote Function -------------------------------------------------------

  (assert-equal
    (apply-k 
      (make-erl-state
        :world (test-world))
      (list
        (make-erl-k
        :fuel 10000 
        :kont (make-kont-expr
                :expr '(:remote-call 
                        arithm-1
                        add
                        (:cons (:integer 2)
                               (:cons (:integer 2) (:nil))))))))
    (make-erl-state 
      :in '(:integer 4)
      :world (test-world)))


  ; Recursive Local Function -----------------------------------------------------

  (assert-equal
    (apply-k 
      (make-erl-state
        :world (test-world)
        :module 'arithm-1)
      (list
        (make-erl-k
        :fuel 10000 
        :kont (make-kont-expr
                :expr '(:call sum (:cons (:integer 2) (:nil)))))))
    (make-erl-state
      :in '(:integer 3)
      :world (test-world)
      :module 'arithm-1))


  ; Recursive Remote Function ----------------------------------------------------

  (assert-equal
    (apply-k 
      (make-erl-state
        :world (test-world))
      (list
        (make-erl-k
        :fuel 10000 
        :kont (make-kont-expr
                :expr '(:remote-call arithm-1 sum (:cons (:integer 5) 
                                                         (:nil)))))))
    (make-erl-state 
      :in '(:integer 15)
      :world (test-world)))

  (assert-equal
    (apply-k 
      (make-erl-state
        :world (test-world))
      (list
        (make-erl-k
        :fuel 10000 
        :kont 
          (make-kont-expr
            :expr 
              '(:remote-call 
                arithm-2 
                add* 
                (:cons (:cons 
                        (:integer 3)
                        (:cons (:integer 6)
                               (:cons (:integer 9)
                                      (:nil))))
                       (:nil)))))))
    (make-erl-state 
      :in '(:integer 18)
      :world (test-world)))


  ; Exceptions -------------------------------------------------------------------

  ; function_clause (local)
  (assert-equal
    (apply-k 
      (make-erl-state
        :world (test-world)
        :module 'arithm-1)
      (list
        (make-erl-k
        :fuel 10000 
        :kont (make-kont-expr
                :expr '(:call sum (:cons (:integer -1) (:nil)))))))
    (make-erl-state 
      :in 
        '(:excpt ((class :error) (reason :function-clause) (stack)))
      :world (test-world)
      :module 'arithm-1))

  ; function_clause (remote)
  (assert-equal
    (apply-k 
      (make-erl-state
        :world (test-world))
      (list
        (make-erl-k
        :fuel 10000 
        :kont (make-kont-expr
                :expr '(:remote-call arithm-1 sum (:cons (:integer -1)
                                                         (:nil)))))))
    (make-erl-state 
      :in '(:excpt ((class :error) (reason :function-clause) (stack)))
      :world (test-world)))

  ; undef (undefined imported module)
  (assert-equal
    (apply-k 
      (make-erl-state
        :world (test-world)
        :module 'arithm-1)
      (list
        (make-erl-k
        :fuel 10000 
        :kont (make-kont-expr
                :expr '(:call bogus-fn1 (:nil))))))
    (make-erl-state 
      :in 
        '(:excpt 
          ((class :error) 
          (reason :undef) 
          (stack local bogus-fn1 0)))
      :world (test-world)
      :module 'arithm-1))

  ; undef (undefined imported function)
  (assert-equal
    (apply-k 
      (make-erl-state
        :world (test-world)
        :module 'arithm-1)
      (list
        (make-erl-k
        :fuel 10000 
        :kont (make-kont-expr
                :expr '(:call bogus-fn2 (:nil))))))
    (make-erl-state 
      :in 
        '(:excpt 
          ((class :error) 
          (reason :undef) 
          (stack bad-mod bogus-fn2 0)))
      :world (test-world)
      :module 'arithm-1))

  ; undef (remote call to undefined module)
  (assert-equal
    (apply-k 
      (make-erl-state
        :world (test-world))
      (list
        (make-erl-k
        :fuel 10000 
        :kont (make-kont-expr
                :expr '(:remote-call crock crock (:nil))))))
    (make-erl-state 
      :in 
        '(:excpt 
          ((class :error) 
          (reason :undef) 
          (stack crock crock 0)))
      :world (test-world)))

  ; undef (remote call to undefined function)
  (assert-equal
    (apply-k 
      (make-erl-state
        :world (test-world))
      (list
        (make-erl-k
        :fuel 10000 
        :kont (make-kont-expr
                :expr '(:remote-call arithm-1 crock (:nil))))))
    (make-erl-state 
      :in 
        '(:excpt 
          ((class :error) 
          (reason :undef) 
          (stack arithm-1 crock 0)))
      :world (test-world))))