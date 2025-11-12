(include-book "erl-eval")
(include-book "std/testing/assert-equal" :DIR :SYSTEM)

; Terms ------------------------------------------------------------------------

; Make atomic term
(assert-equal (make-node-integer :val 1) '(:integer 1))
(assert-equal (make-node-string :val "abc") '(:string "abc"))
(assert-equal (make-node-atom :val 'atom) '(:atom atom))
(assert-equal (make-node-nil) '(:nil))

; Make cons list
(assert-equal 
  (make-node-cons :hd (make-node-integer :val 1) 
                  :tl (make-node-cons :hd (make-node-integer :val 2)
                                      :tl (make-node-cons :hd (make-node-integer :val 3)
                                                          :tl (make-node-nil))))
  '(:cons (:integer 1) (:cons (:integer 2) (:cons (:integer 3) (:nil)))))

; TODO: There is no support for pairs currently.
(assert-equal 
  (make-node-cons :hd (make-node-integer :val 1) 
                  :tl (make-node-integer :val 2))
  '(:cons (:integer 1) (:integer 2)))

; Make tuple
(assert-equal
  (make-node-tuple :lst (list '(:integer 1) '(:string "a") '(:cons (:integer 1) (:cons (:integer 2) (:nil)))))
  '(:tuple ((:integer 1) (:string "a") (:cons (:integer 1) (:cons (:integer 2) (:nil))))))

; Evaluate terms
(assert-equal
  (apply-k 
    (make-erl-state) 
    (list (make-erl-k :fuel 10000 :kont (make-kont-expr :expr '(:integer 1)))))
  (make-erl-state :in (make-erl-val-integer :val 1)))
(assert-equal
  (apply-k 
    (make-erl-state) 
    (list (make-erl-k :fuel 10000 :kont (make-kont-expr :expr '(:string "abc")))))
  (make-erl-state :in (make-erl-val-string :val "abc")))
(assert-equal
  (apply-k 
    (make-erl-state) 
    (list (make-erl-k :fuel 10000 :kont (make-kont-expr :expr '(:atom abc)))))
  (make-erl-state :in (make-erl-val-atom :val 'abc)))
(assert-equal
  (apply-k 
    (make-erl-state) 
    (list (make-erl-k :fuel 10000 :kont (make-kont-expr :expr '(:nil)))))
  (make-erl-state :in (make-erl-val-cons :lst nil)))

; Evaluate lists
(assert-equal
  (apply-k 
    (make-erl-state)
    (list (make-erl-k :fuel 10000 
                      :kont (make-kont-expr 
                        :expr '(:cons (:integer 1) 
                                      (:cons (:integer 2) 
                                             (:cons (:integer 3) (:nil))))))))
  (make-erl-state :in (make-erl-val-cons :lst (list '(:integer 1) '(:integer 2) '(:integer 3)))))

; TODO: Currenlty pairs are not allowed
; (assert-equal
;   (apply-k 
;     (make-erl-state)
;     (list (make-erl-k :fuel 10000 
;                       :kont (make-kont-expr 
;                         :expr '(:cons (:integer 1) (:integer 2))))))
;   (make-erl-state :in (make-erl-val-cons :lst (list '(:integer 1) '(:integer 2)))))

; Evaluate tuples
(assert-equal
  (apply-k 
    (make-erl-state)
    (list (make-erl-k 
            :fuel 10000 
            :kont (make-kont-expr 
                    :expr '(:tuple 
                            ((:integer 1) 
                             (:string "a") 
                             (:cons (:integer 1) (:cons (:integer 2) (:nil)))))))))
  (make-erl-state 
    :in (make-erl-val-tuple 
          :lst (list '(:integer 1)
                       '(:string "a") 
                       '(:cons ((:integer 1) (:integer 2)))))))



; Unop -------------------------------------------------------------------------

(assert-equal (make-node-unop :op '- :expr '(:integer 1))
              '(:unop - (:integer 1)))

(assert-equal
  (apply-k 
    (make-erl-state)
    (list (make-erl-k 
            :fuel 10000 
            :kont (make-kont-expr :expr '(:unop - (:integer 1))))))
  (make-erl-state :in (make-erl-val-integer :val -1)))

(assert-equal
  (apply-k 
    (make-erl-state)
    (list (make-erl-k 
            :fuel 10000 
            :kont (make-kont-expr :expr '(:unop - (:string "a"))))))
  (make-erl-state :in (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error)
                                           :reason (make-exit-reason-badarith)))))


; Binop ------------------------------------------------------------------------

(assert-equal (make-node-binop :op '+ :left '(:integer 2) :right '(:integer 3))
              '(:binop + (:integer 2) (:integer 3)))

(assert-equal
  (apply-k 
    (make-erl-state)
    (list (make-erl-k 
            :fuel 10000 
            :kont (make-kont-expr :expr '(:binop + (:integer 2) (:integer 3))))))
  (make-erl-state :in (make-erl-val-integer :val 5)))

(assert-equal
  (apply-k 
    (make-erl-state)
    (list (make-erl-k 
            :fuel 10000 
            :kont (make-kont-expr :expr '(:binop + (:string "a") (:integer 3))))))
  (make-erl-state :in (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error)
                                           :reason (make-exit-reason-badarith)))))


; Variables --------------------------------------------------------------------

(assert-equal (make-node-var :id 'X) '(:var X))

(assert-equal
  (apply-k 
    (make-erl-state)
    (list (make-erl-k 
            :fuel 10000 
            :kont (make-kont-expr :expr '(:var X)))))
  (make-erl-state :in (make-erl-val-reject :err "unbound variable")))

(assert-equal
  (apply-k 
    (make-erl-state :bind (omap::from-lists (list 'X) (list (make-erl-val-integer :val 4))))
    (list (make-erl-k 
            :fuel 10000 
            :kont (make-kont-expr :expr '(:var X)))))
  (make-erl-state :in '(:integer 4) :bind '((X :integer 4))))

(assert-equal
  (apply-k 
    (make-erl-state 
      :bind (omap::from-lists 
              (list 'X 'Y) 
              (list (make-erl-val-integer :val 4) (make-erl-val-integer :val 5))))
    (list (make-erl-k 
            :fuel 10000 
            :kont (make-kont-expr :expr '(:binop + (:var X) (:var Y))))))
  (make-erl-state :in '(:integer 9) :bind '((X :integer 4) (Y :integer 5))))


; Match ------------------------------------------------------------------------

; Match Coonstructor 

; var = int.
(assert-equal (make-node-match :lhs '(:var X) :rhs '(:integer 1))
              '(:match (:var X) (:integer 1)))                

; [X, Y, Z] = [int,int,int].
(assert-equal 
  (make-node-match 
    :lhs '(:cons (:var X) (:cons (:var Y) (:cons (:var Z) (:nil)))) 
    :rhs '(:cons (:integer 1) (:cons (:integer 2) (:cons (:integer 3) (:nil)))))
  '(:match (:cons (:var X) (:cons (:var Y) (:cons (:var Z) (:nil)))) 
           (:cons (:integer 1) (:cons (:integer 2) (:cons (:integer 3) (:nil)))))) 

; {X, Y, Z} = {int,int,int}.
(assert-equal 
  (make-node-match 
    :lhs '(:tuple ((:var X) (:var Y) (:var Z))) 
    :rhs '(:tuple ((:integer 1) (:integer 2) (:integer 3))))
  '(:match (:tuple ((:var X) (:var Y) (:var Z)))
           (:tuple ((:integer 1) (:integer 2) (:integer 3))))) 

; {int + int, X} = {int, string}.
(assert-equal 
  (make-node-match 
    :lhs '(:tuple ((:binop + (:integer 1) (:integer 2)) (:var X))) 
    :rhs '(:tuple ((:integer 3) (:string "abc"))))
  '(:match (:tuple ((:binop + (:integer 1) (:integer 2)) (:var X)))
           (:tuple ((:integer 3) (:string "abc"))))) 

; {[int, int, X], Y = int} = {Z, int} = {[int, int, int], int}.
(assert-equal 
  (make-node-match 
    :lhs '(:match (:tuple ((:cons (:integer 1) (:cons (:integer 2) (:cons (:var X) (:nil)))) 
                           (:match (:var Y) (:integer 3))))
                  (:tuple ((:var Z) (:integer 3)))) 
    
    :rhs '(:tuple ((:cons (:integer 1) (:cons (:integer 2) (:cons (:integer 3) (:nil)))) 
                   (:integer 3))))
  '(:match (:match (:tuple ((:cons (:integer 1) (:cons (:integer 2) (:cons (:var X) (:nil)))) 
                            (:match (:var Y) (:integer 3))))
                   (:tuple ((:var Z) (:integer 3))))
           (:tuple ((:cons (:integer 1) (:cons (:integer 2) (:cons (:integer 3) (:nil)))) 
                    (:integer 3))))) 


; Match Evaluation

; var = int.
(assert-equal
  (apply-k 
    (make-erl-state)
    (list (make-erl-k 
            :fuel 10000 
            :kont (make-kont-expr :expr '(:match (:var X) (:integer 1))))))
  (make-erl-state :in '(:integer 1) :bind '((X :integer 1))))

; [X, Y, Z] = [int,int,int].
(assert-equal
  (apply-k 
    (make-erl-state)
    (list 
      (make-erl-k 
        :fuel 10000 
        :kont (make-kont-expr 
                :expr '(:match (:cons (:var X) (:cons (:var Y) (:cons (:var Z) (:nil)))) 
                               (:cons (:integer 1) 
                                      (:cons (:integer 2) 
                                             (:cons (:integer 3) (:nil)))))))))
  (make-erl-state :in '(:cons ((:integer 1) (:integer 2) (:integer 3))) 
                  :bind '((X :integer 1) (Y :integer 2) (Z :integer 3))))

; {X, Y, Z} = {int,int,int}.
(assert-equal
  (apply-k 
    (make-erl-state)
    (list 
      (make-erl-k 
        :fuel 10000 
        :kont (make-kont-expr 
                :expr '(:match (:tuple ((:var X) (:var Y) (:var Z)))
                               (:tuple ((:integer 1) (:integer 2) (:integer 3))))))))
  (make-erl-state :in '(:tuple ((:integer 1) (:integer 2) (:integer 3))) 
                  :bind '((X :integer 1) (Y :integer 2) (Z :integer 3))))

; {int + int, X} = {int, string}.
(assert-equal
  (apply-k 
    (make-erl-state)
    (list 
      (make-erl-k 
        :fuel 10000 
        :kont (make-kont-expr 
                :expr '(:match (:tuple ((:binop + (:integer 1) (:integer 2)) (:var X)))
                                (:tuple ((:integer 3) (:string "abc"))))))))
  (make-erl-state :in '(:tuple ((:integer 3) (:string "abc"))) 
                  :bind '((X :string "abc"))))

; {[int, int, X], Y = int} = {Z, int} = {[int, int, int], int}.
(assert-equal
  (apply-k 
    (make-erl-state)
    (list 
      (make-erl-k 
        :fuel 10000 
        :kont 
          (make-kont-expr 
            :expr 
              '(:match 
                  (:match (:tuple ((:cons (:integer 1) (:cons (:integer 2) (:cons (:var X) (:nil)))) 
                                   (:match (:var Y) (:integer 4))))
                                           (:tuple ((:var Z) (:integer 4))))
                  (:tuple ((:cons (:integer 1) (:cons (:integer 2) (:cons (:integer 3) (:nil)))) 
                           (:integer 4))))))))
  (make-erl-state :in '(:tuple ((:cons ((:integer 1) (:integer 2) (:integer 3))) (:integer 4))) 
                  :bind '((X :integer 3) 
                          (Y :integer 4) 
                          (Z :cons ((:integer 1) (:integer 2) (:integer 3))))))



; Series of Match

; X = int, Y = X + int, Y + int.
(assert-equal
  (apply-k 
    (make-erl-state)
    (list 
      (make-erl-k 
        :fuel 10000 
        :kont (make-kont-exprs
                :exprs '((:match (:var X) (:integer 3))
                         (:match (:var Y) (:binop + (:var X) (:integer 2)))
                         (:binop * (:var Y) (:var X)))))))
  (make-erl-state :in '(:integer 15) 
                  :bind '((X :integer 3) (Y :integer 5))))

; TODO: Bad Match
; TODO: Illegal Pattern