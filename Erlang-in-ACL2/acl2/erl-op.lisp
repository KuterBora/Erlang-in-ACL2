(in-package "ACL2")
(include-book "erl-ast")
(include-book "erl-value")

; Erlang Operations ------------------------------------------------------------

(set-induction-depth-limit 1)

; Representation of Erlang addition in ACL2.
; - Returns badarg if arguments are not integers.
(define erl-add ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((unless (equal (erl-val-kind left) :integer)) (make-erl-val-error :err 'badarg))
       ((unless (equal (erl-val-kind right) :integer)) (make-erl-val-error :err 'badarg)))
      (make-erl-val-integer :val (+ (erl-val-integer->val left)
                                    (erl-val-integer->val right))))
  ///
  (defrule commutativity-of-erl-add
    (equal (erl-add x y)
           (erl-add y x)))
  (defrule associativity-of-erl-add
    (equal (erl-add (erl-add x y) z)
           (erl-add x (erl-add y z)))))

; Representation of Erlang substraction in ACL2.
; - Returns badarg if arguments are not integers.
(define erl-sub ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((unless (equal (erl-val-kind left) :integer)) (make-erl-val-error :err 'badarg))
       ((unless (equal (erl-val-kind right) :integer)) (make-erl-val-error :err 'badarg)))
      (make-erl-val-integer :val (- (erl-val-integer->val left)
                                    (erl-val-integer->val right)))))

; Representation of Erlang multiplication in ACL2.
; - Returns badarg if arguments are not integers.
(define erl-mul ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((unless (equal (erl-val-kind left) :integer)) (make-erl-val-error :err 'badarg))
       ((unless (equal (erl-val-kind right) :integer)) (make-erl-val-error :err 'badarg)))
      (make-erl-val-integer :val (* (erl-val-integer->val left)
                                    (erl-val-integer->val right))))
  ///
  (defrule commutativity-of-erl-mul
    (equal (erl-mul x y)
           (erl-mul y x)))
  (defrule associativity-of-erl-mul
    (equal (erl-mul (erl-mul x y) z)
           (erl-mul z (erl-mul y x)))))

; Representation of Erlang integer division (div) in ACL2.
; - The result is rounded down to the largest integer less than the result.
; - Returns badarg if arguments are not integers or if there is division by 0.
(define erl-div ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((unless (equal (erl-val-kind left) :integer)) (make-erl-val-error :err 'badarg))
       ((unless (equal (erl-val-kind right) :integer)) (make-erl-val-error :err 'badarg))
       ((if (equal (erl-val-integer->val right) 0)) (make-erl-val-error :err 'badarg))
       (left-val (erl-val-integer->val left))
       (right-val (erl-val-integer->val right)))
      (make-erl-val-integer :val (floor left-val right-val))))


; Given a binop, apply the corresponding Erlang operation.
(define apply-erl-binop ((op erl-binop-p) (left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((op (erl-binop-fix op))
       (left (erl-val-fix left))
       (right (erl-val-fix right))
       ((if (equal left (make-erl-val-fault))) left)
       ((if (equal right (make-erl-val-fault))) right))
      (case op
        (+ (erl-add left right))
        (- (erl-sub left right))
        (* (erl-mul left right))
        (div (erl-div left right))
        (otherwise (make-erl-val-fault))))
    ///
    (defrule apply-erl-binop-of-fault
      (implies (and (erl-val-p left)
                    (erl-val-p right)
                    (erl-binop-p op)
                    (not (equal (apply-erl-binop op left right) (make-erl-val-fault))))
              (and (not (equal left (make-erl-val-fault)))
                   (not (equal right (make-erl-val-fault)))))
      :enable (erl-add erl-sub erl-mul erl-div)))