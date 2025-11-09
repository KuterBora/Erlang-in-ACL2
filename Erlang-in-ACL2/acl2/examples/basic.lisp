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

(assert-equal (make-node-binop :op '+ :left '(:integer 2) :right (:integer 3))
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

; TODO