(in-package "ACL2")
(include-book "erl-eval")
(include-book "std/testing/assert-equal" :DIR :SYSTEM)

; BIFs -------------------------------------------------------------------------

(make-node-call :fn 'is_integer :args '((:integer 1)))
(make-node-call 
  :fn 'element
  :args '((:integer 2) (:tuple ((:atom one) (:atom two) (:atom three)))))

(assert-equal
  (apply-k 
    (make-erl-state)
    (list 
      (make-erl-k 
      :fuel 10000 
      :kont (make-kont-expr
              :expr '(:call is_integer ((:integer 1)))))))
  (make-erl-state :in '(:atom true)))

(assert-equal
  (apply-k 
    (make-erl-state)
    (list 
      (make-erl-k 
      :fuel 10000 
      :kont (make-kont-expr
              :expr '(:call element
                            ((:integer 2)
                             (:tuple ((:atom one)
                                      (:atom two)
                                      (:atom three)))))))))
  (make-erl-state :in '(:atom two)))


; Simple Local Function --------------------------------------------------------

; Example function: adder(X, Y) -> X + Y.
'((name . adder) (arity . 2))

; body of adder
'(((cases (:var X) (:var Y))
   (guards)
   (body (:binop + (:var X) (:var Y)))))

; Attrs with adder
'((module . shell)
 (export ((name . adder) (arity . 2)))
 (import))


; function map with adder
'((((name . adder) (arity . 2))
  ((cases (:var X) (:var Y))
   (guards)
   (body (:binop + (:var X) (:var Y))))))

; module with adder
'((attrs (module . shell)
         (export ((name . adder) (arity . 2)))
         (import))
  (fn-defns 
    (((name . adder) (arity . 2))
      ((cases (:var X) (:var Y))
       (guards)
       (body (:binop + (:var X) (:var Y)))))))

; Example World
'((shell 
  (attrs (module . shell)
        (export ((name . adder) (arity . 2)))
        (import))
  (fn-defns 
    (((name . adder) (arity . 2))
      ((cases (:var X) (:var Y))
      (guards)
      (body (:binop + (:var X) (:var Y))))))))


; Simple Remote Function -------------------------------------------------------

(assert-equal
  (apply-k 
    (make-erl-state
      :world 
        '((shell 
            (attrs (module . shell)
                  (export)
                  (import))
            (fn-defns 
              (((name . adder) (arity . 2))
                ((cases (:var X) (:var Y))
                 (guards)
                 (body (:binop + (:var X) (:var Y)))))))))
    (list
      (make-erl-k
      :fuel 10000 
      :kont (make-kont-expr
              :expr '(:call adder
                            ((:integer 2)
                             (:integer 2)))))))
  (make-erl-state 
    :in '(:integer 4)
    :world 
        '((shell 
            (attrs (module . shell)
                  (export)
                  (import))
            (fn-defns 
              (((name . adder) (arity . 2))
                ((cases (:var X) (:var Y))
                (guards)
                (body (:binop + (:var X) (:var Y))))))))))


; Recursive Local Function -----------------------------------------------------
; Recursive Remote Function ----------------------------------------------------


; Example function: 
;  sum(0) -> 0;
;  sum(X) -> X + sum(X - 1).
;
'((name . sum) (arity . 1))

; body of sum
'(((cases (:integer 0))
   (guards)
   (body (:integer 0)))
  ((cases (:var X))
   (guards)
   (body (:binop + (:var X) (:call sum ((:binop - (:var X) (:integer 1))))))))

; Attrs with sum
'((module . shell)
  (export)
  (import))

; function map with sum
'((((name . sum) (arity . 1))
   ((cases (:integer 0))
    (guards)
    (body (:integer 0)))
   ((cases (:var X))
    (guards)
    (body (:binop + (:var X) (:call sum ((:binop - (:var X) (:integer 1)))))))))

; module with adder
'((attrs (module . shell)
         (export)
         (import))
  (fn-defns 
    (((name . sum) (arity . 1))
     ((cases (:integer 0))
      (guards)
      (body (:integer 0)))
     ((cases (:var X))
      (guards)
      (body (:binop + (:var X) (:call sum ((:binop - (:var X) (:integer 1))))))))))

; Example World
'((shell 
  (attrs (module . shell)
         (export)
         (import))
  (fn-defns 
    (((name . sum) (arity . 1))
     ((cases (:integer 0))
      (guards)
      (body (:integer 0)))
     ((cases (:var X))
      (guards)
      (body (:binop + (:var X) (:call sum ((:binop - (:var X) (:integer 1)))))))))))


(assert-equal
  (apply-k 
    (make-erl-state
      :world 
        '((shell 
            (attrs (module . shell)
                  (export)
                  (import))
            (fn-defns 
              (((name . sum) (arity . 1))
              ((cases (:integer 0))
                (guards)
                (body (:integer 0)))
              ((cases (:var X))
                (guards)
                (body (:binop + (:var X) (:call sum ((:binop - (:var X) (:integer 1))))))))))))
    (list
      (make-erl-k
      :fuel 10000 
      :kont (make-kont-expr
              :expr '(:call sum
                            ((:integer 5)))))))
  (make-erl-state 
    :in '(:integer 4)
    :world 
        '((shell 
            (attrs (module . shell)
                  (export)
                  (import))
            (fn-defns 
              (((name . sum) (arity . 1))
              ((cases (:integer 0))
                (guards)
                (body (:integer 0)))
              ((cases (:var X))
                (guards)
                (body (:binop + (:var X) (:call sum ((:binop - (:var X) (:integer 1)))))))))))))