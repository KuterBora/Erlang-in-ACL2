(include-book "std/util/top" :DIR :SYSTEM)
(set-induction-depth-limit 1)

;; Erl Addition
;; Returns badarg if arguments are not integers
(define erl-add ((left erl-value-p) (right erl-value-p))
  :returns (v erl-value-p)
  (b* ((left (erl-value-fix left)) 
       (right (erl-value-fix right)))
    (if (and (equal (erl-value-kind left) :integer)
             (equal (erl-value-kind right) :integer))
        (make-erl-value-integer :val (+ (erl-value-integer->val left)
                                        (erl-value-integer->val right)))
        '(:error badarg)))
  ///
  (defrule commutativity-of-erl-add
    (equal (erl-add x y)
           (erl-add y x)))
  (defrule associativity-of-erl-add
    (equal (erl-add (erl-add x y) z)
           (erl-add x (erl-add y z)))))


;; Erl Substraction
;; Returns badarg if arguments are not integers
(define erl-sub ((left erl-value-p) (right erl-value-p))
  :returns (v erl-value-p)
  (b* ((left (erl-value-fix left)) 
       (right (erl-value-fix right)))
    (if (and (equal (erl-value-kind left) :integer)
             (equal (erl-value-kind right) :integer))
        (make-erl-value-integer :val (- (erl-value-integer->val left)
                                        (erl-value-integer->val right)))
        '(:error badarg))))


;; Erl Multiplication
;; Returns badarg if arguments are not integers
(define erl-mul ((left erl-value-p) (right erl-value-p))
  :returns (v erl-value-p)
  (b* ((left (erl-value-fix left)) 
       (right (erl-value-fix right)))
    (if (and (equal (erl-value-kind left) :integer)
             (equal (erl-value-kind right) :integer))
        (make-erl-value-integer :val (* (erl-value-integer->val left)
                                        (erl-value-integer->val right)))
        '(:error badarg)))
  ///
  (defrule commutativity-of-erl-mul
    (equal (erl-mul x y)
           (erl-mul y x)))
  (defrule associativity-of-erl-mul
    (equal (erl-mul (erl-mul x y) z)
           (erl-mul z (erl-mul y x)))))


;; Erl Divison (Div)
;; Returns the result of left / right rounded to the closes integer 
;; or badarg if arguments are not integers, or if the second argument is 0
(define erl-div ((left erl-value-p) (right erl-value-p))
  :returns (v erl-value-p)
  (b* ((left (erl-value-fix left)) 
       (right (erl-value-fix right)))
    (if (and (equal (erl-value-kind left) :integer)
             (equal (erl-value-kind right) :integer)
             (not (equal (erl-value-integer->val right) 0)))
        (b* ((left-val (erl-value-integer->val left))
             (right-val (erl-value-integer->val right))
             (sign (if (and (minusp left-val) (minusp right-val)) 
                       1 
                       (if (or (minusp left-val) (minusp right-val)) -1 1)))
             (val (floor (abs left-val) (abs right-val))))
          (make-erl-value-integer :val (* sign val)))
        '(:error badarg))))


;; Apply Erlang binary operation
(define apply-erl-binop ((op symbolp) (left erl-value-p) (right erl-value-p))
  :returns (v erl-value-p)
  (b* ((op (symbol-fix op))
       (left (erl-value-fix left))
       (right (erl-value-fix right)))
      (case op
            (+ (erl-add left right))
            (- (erl-sub left right))
            (* (erl-mul left right))
            (div (erl-div left right))
            (otherwise '(:fault bad-op)))))