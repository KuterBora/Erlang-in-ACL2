(in-package "ACL2")
(include-book "erl-ast")
(include-book "erl-value")
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

(set-induction-depth-limit 1)

; Erlang Binary Operations -----------------------------------------------------

; Representation of Erlang addition in ACL2.
; - Returns badarith if arguments are not integers.
(define erl-add ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((unless (and (equal (erl-val-kind left) :integer)
                     (equal (erl-val-kind right) :integer)))
        (make-erl-val-excpt 
          :err (make-erl-err :class (make-err-class-error)
                             :reason (make-exit-reason-badarith)))))
      (make-erl-val-integer :val (+ (erl-val-integer->val left)
                                    (erl-val-integer->val right))))
  ///
  (defrule commutativity-of-erl-add
    (erl-equiv (erl-add x y)
               (erl-add y x))
    :enable erl-equiv)
  (defrule associativity-of-erl-add
    (erl-equiv (erl-add (erl-add x y) z)
               (erl-add x (erl-add y z)))))

; Representation of Erlang substraction in ACL2.
; - Returns badarith if arguments are not integers.
(define erl-sub ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((unless (and (equal (erl-val-kind left) :integer) 
                     (equal (erl-val-kind right) :integer)))
        (make-erl-val-excpt 
          :err (make-erl-err :class (make-err-class-error)
                             :reason (make-exit-reason-badarith)))))
      (make-erl-val-integer :val (- (erl-val-integer->val left)
                                    (erl-val-integer->val right)))))

; Representation of Erlang multiplication in ACL2.
; - Returns badarith if arguments are not integers.
(define erl-mul ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((unless (and (equal (erl-val-kind left) :integer) 
                     (equal (erl-val-kind right) :integer)))
        (make-erl-val-excpt 
          :err (make-erl-err :class (make-err-class-error)
                             :reason (make-exit-reason-badarith)))))
      (make-erl-val-integer :val (* (erl-val-integer->val left)
                                    (erl-val-integer->val right))))
  ///
  (defrule commutativity-of-erl-mul
    (erl-equiv (erl-mul x y)
               (erl-mul y x))
      :enable erl-equiv)
  (defrule associativity-of-erl-mul
    (erl-equiv (erl-mul (erl-mul x y) z)
               (erl-mul z (erl-mul y x)))
    :enable erl-equiv))

; Representation of Erlang integer division (div) in ACL2.
; - The result is rounded down to the largest integer less than the result.
; - Returns badarith if arguments are not integers or if there is division by 0.
(define erl-div ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((unless 
          (and (equal (erl-val-kind left) :integer) 
               (equal (erl-val-kind right) :integer)
               (not (equal (erl-val-integer->val right) 0))))
        (make-erl-val-excpt 
          :err (make-erl-err :class (make-err-class-error)
                             :reason (make-exit-reason-badarith))))
       (left-val (erl-val-integer->val left))
       (right-val (erl-val-integer->val right)))
      (make-erl-val-integer :val (floor left-val right-val))))

; Given a binop, apply the corresponding Erlang operation.
(define apply-erl-binop ((op erl-binop-p) (left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((op (erl-binop-fix op))
       (left (erl-val-fix left))
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right))
      (case op
        (+ (erl-add left right))
        (- (erl-sub left right))
        (* (erl-mul left right))
        (div (erl-div left right))
        (otherwise (make-erl-val-reject :err "bad op"))))
  ///
  (defrule apply-erl-binop-of-flimit
    (implies
      (and (erl-val-p left) (erl-val-p right)) 
      (iff (not (equal (apply-erl-binop op left right) (make-erl-val-flimit)))
            (and (not (equal left (make-erl-val-flimit)))
                (not (equal right (make-erl-val-flimit))))))
    :enable (erl-add erl-sub erl-mul erl-div)))


; Erlang Unary Operations ------------------------------------------------------

; Representation of Erlang negation (-) in ACL2.
(define erl-minus ((val erl-val-p))
  :returns (v erl-val-p)
  (b* ((val (erl-val-fix val))
       ((if (equal (erl-val-kind val) :flimit)) val)
       ((if (equal (erl-val-kind val) :reject)) val)
       ((unless (equal (erl-val-kind val) :integer))
        (make-erl-val-excpt 
          :err (make-erl-err :class (make-err-class-error)
                             :reason (make-exit-reason-badarith)))))
      (make-erl-val-integer :val (* -1 (erl-val-integer->val val)))))

; Given an unop, apply the corresponding Erlang operation.
(define apply-erl-unop ((op erl-unop-p) (val erl-val-p))
  :returns (v erl-val-p)
  (b* ((op (erl-unop-fix op))
       (val (erl-val-fix val))
       ((if (equal (erl-val-kind val) :flimit)) val)
       ((if (equal (erl-val-kind val) :reject)) val))
      (case op
        (- (erl-minus val))
        (otherwise (make-erl-val-reject :err "bad op"))))
  ///
  (defrule apply-erl-unop-of-flimit
    (implies
      (erl-val-p val) 
      (iff (not (equal (apply-erl-unop op val) (make-erl-val-flimit)))
           (not (equal val (make-erl-val-flimit)))))
    :enable (erl-minus)))