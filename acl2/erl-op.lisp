(in-package "ACL2")
(include-book "erl-ast")
(include-book "erl-value")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

(set-induction-depth-limit 1)

; Arithemtic Erlang Operations -------------------------------------------------

; Remarks:
; - Floating point operations are not currently supported, so '/' is not implemented.
; - bitwise operations are not supported.

; Representation of Erlang unary + in ACL2.
(define erl-plus ((val erl-val-p))
  :returns (v erl-val-p)
  (b* ((val (erl-val-fix val))
       ((if (equal (erl-val-kind val) :flimit)) val)
       ((if (equal (erl-val-kind val) :reject)) val)
       ((unless (equal (erl-val-kind val) :integer))
        (make-erl-val-excpt 
          :err (make-erl-err :class (make-err-class-error)
                             :reason (make-exit-reason-badarith)))))
      val))

; Representation of Erlang unary - in ACL2.
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

; Representation of Erlang addition in ACL2.
; - Returns badarith if arguments are not integers.
(define erl-add ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
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
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
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
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
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
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
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

; Representation of Erlang integer remainder of X/Y (rem) in ACL2.
; - Returns badarith if arguments are not integers or if there is division by 0.
(define erl-rem ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
       ((unless 
          (and (equal (erl-val-kind left) :integer) 
               (equal (erl-val-kind right) :integer)
               (not (equal (erl-val-integer->val right) 0))))
        (make-erl-val-excpt 
          :err (make-erl-err :class (make-err-class-error)
                             :reason (make-exit-reason-badarith))))
       (left-val (erl-val-integer->val left))
       (right-val (erl-val-integer->val right)))
      (make-erl-val-integer :val (rem left-val right-val))))

; Given an arithmetic binop, apply the corresponding Erlang operation.
(define apply-erl-arithm-binop ((op arithm-binop-p) (left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((op (arithm-binop-fix op))
       (left (erl-val-fix left))
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
       ((unless 
          (and (equal (erl-val-kind left) :integer) 
               (equal (erl-val-kind right) :integer)))
        (make-erl-val-excpt 
          :err (make-erl-err :class (make-err-class-error)
                             :reason (make-exit-reason-badarith)))))
      (case op
        (+ (erl-add left right))
        (- (erl-sub left right))
        (* (erl-mul left right))
        (div (erl-div left right))
        (rem (erl-rem left right))
        (otherwise (make-erl-val-reject :err "bad op"))))
    ///
      (defrule apply-erl-arithm-binop-of-flimit
        (implies
          (and (erl-val-p left) (erl-val-p right) (arithm-binop-p op)) 
          (iff (not (equal (erl-val-kind (apply-erl-arithm-binop op left right)) :flimit))
               (and (not (equal (erl-val-kind left) :flimit))
                    (not (equal (erl-val-kind right) :flimit)))))
        :enable (erl-add erl-sub erl-mul erl-div erl-rem)))

; Erlang Boolean Operations ----------------------------------------------------

; Representation of Erlang boolean operation 'not' in ACl2.
; - Returns badarg if the argument is not a boolean.
(define erl-not ((val erl-val-p))
  :returns (v erl-val-p)
  (b* ((val (erl-val-fix val))
       ((if (equal (erl-val-kind val) :flimit)) val)
       ((if (equal (erl-val-kind val) :reject)) val)
       ((unless (erl-boolean-p val))
        (make-erl-val-excpt 
          :err (make-erl-err :class (make-err-class-error)
                             :reason (make-exit-reason-badarg)))))
      (if (equal (erl-val-atom->val val) 'true)
          (make-erl-val-atom :val 'false)
          (make-erl-val-atom :val 'true)))
  :guard-hints (("Goal" :in-theory (enable erl-boolean-p))))

; Representation of Erlang boolean operation 'and' in ACl2.
; - Returns badarg if arguments are not booleans.
(define erl-and ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
       ((unless (and (erl-boolean-p left) 
                     (erl-boolean-p right)))
        (make-erl-val-excpt 
          :err (make-erl-err :class (make-err-class-error)
                             :reason (make-exit-reason-badarg)))))
      (if (and (equal (erl-val-atom->val left) 'true)
              (equal (erl-val-atom->val right) 'true))
          (make-erl-val-atom :val 'false)
          (make-erl-val-atom :val 'true)))
  :guard-hints (("Goal" :in-theory (enable erl-boolean-p))))

; Representation of Erlang boolean operation 'or' in ACl2.
; - Returns badarg if arguments are not booleans.
(define erl-or ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
       ((unless (and (erl-boolean-p left) 
                     (erl-boolean-p right)))
        (make-erl-val-excpt 
          :err (make-erl-err :class (make-err-class-error)
                             :reason (make-exit-reason-badarg)))))
      (if (or (equal (erl-val-atom->val left) 'true)
              (equal (erl-val-atom->val right) 'true))
          (make-erl-val-atom :val 'false)
          (make-erl-val-atom :val 'true)))
  :guard-hints (("Goal" :in-theory (enable erl-boolean-p))))

; Representation of Erlang boolean operation 'xor' in ACl2.
; - Returns badarg if arguments are not booleans.
(define erl-xor ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
       ((unless (and (erl-boolean-p left) 
                     (erl-boolean-p right)))
        (make-erl-val-excpt 
          :err (make-erl-err :class (make-err-class-error)
                             :reason (make-exit-reason-badarg)))))
      (if (xor (equal (erl-val-atom->val left) 'true)
               (equal (erl-val-atom->val right) 'true))
          (make-erl-val-atom :val 'false)
          (make-erl-val-atom :val 'true)))
  :guard-hints (("Goal" :in-theory (enable erl-boolean-p))))

; Given a boolean binop, apply the corresponding Erlang operation.
(define apply-erl-bool-binop ((op bool-binop-p) (left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((op (bool-binop-fix op))
       (left (erl-val-fix left))
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
       ((unless 
          (and (erl-boolean-p left) (erl-boolean-p right)))
        (make-erl-val-excpt 
          :err (make-erl-err :class (make-err-class-error)
                             :reason (make-exit-reason-badarg)))))
      (case op
        ('and (erl-and left right))
        ('or (erl-or left right))
        ('xor (erl-xor left right))
        (otherwise (make-erl-val-reject :err "bad op"))))
    ///
      (defrule apply-erl-bool-binop-of-flimit
        (implies
          (and (erl-val-p left) (erl-val-p right) (bool-binop-p op)) 
          (iff (not (equal (erl-val-kind (apply-erl-bool-binop op left right)) :flimit))
               (and (not (equal (erl-val-kind left) :flimit))
                    (not (equal (erl-val-kind right) :flimit)))))
        :enable (erl-and erl-or erl-xor)))


; Erlang Term Comparison -------------------------------------------------------

; Remarks:
; - Erl-val represents strings as lists of integers, but this does not change the 
;   Erlang rules for equivalence as "A" =:= [65].
; - 0 and -0 are not considered equivalent by =:= in Erlang. That is currently
;   not the case in this interpreter.


; helper to compare Erlang atoms that have been converted to list of integers
; - Return 0 if they are equal
; - Return 1 if left is greater than right
; - Return -1 if left is smaller than right
(define erl-compare-atom-string ((l integer-listp) (r integer-listp))
  :returns (i integerp)
  :measure (len (integer-list-fix l))
  (b* ((l (integer-list-fix l))
       (r (integer-list-fix r)))
      (cond 
        ((and (null l) (null r)) 0)
        ((null l) -1)
        ((null r) 1)
        ((> (car l) (car r)) 1)
        ((< (car l) (car r)) -1)
        (t (erl-compare-atom-string (cdr l) (cdr r))))))

; Compare Erlang terms
; - Return 0 if they are equal
; - Return 1 if left is greater than right
; - Return -1 if left is smaller than right
; - If an arg is not a valid Erlang value, return 3.
;
; TODO: I need to clean up the multicase. Maybe I should have a guard
; that ensures a list or tuple does not contain error, as that should have been\
; checked by the caller already.
;
; The arguments can be of different data types. The following order is defined
; in the Erlang reference manual:
; number < atom < reference < fun < port < pid < tuple < map < nil < list < bit string
;
; Unsupported: 
; - fun comparisons, though not documented in the Erlang manual, are allowed in Erlang.
; '==' and '=:=' seem obvious to implement, but other operations required experiments
;  to figure out. 
; - When comparing funs, the AST's are compared, including the line numbers assigned to
;   the nodes. 
;   
;   For example,
;   
;   A = fun() -> 1 end, B = fun() -> 1 end, A == B. 
;   
;   returns true, while 
;   
;   A = fun() -> 1 end,
;   B = fun() -> 1 end,
;   A == B.
;   
;   returns false.
;   
; Since this is not a very practical feature of Erlang, it will not be supported
; in the ACL2 evaluator for now. 
;
(defines erl-comparison
  :flag-local nil
  (define erl-compare ((left erl-val-p) (right erl-val-p))
    :returns (i integerp) 
    :measure (erl-val-count left)
    (b* ((left (erl-val-fix left))
         (right (erl-val-fix right)))
        (fty::multicase ((erl-val-case left) (erl-val-case right))
          ((:flimit &) 3)
          ((& :flimit) 3)
          ((:reject &) 3)
          ((& :reject) 3)
          ((:none &) 3)
          ((& :none) 3)
          ((:excpt &) 3)
          ((& :excpt) 3)
          ((:integer :integer) 
           (let ((lv (erl-val-integer->val left))
                 (rv (erl-val-integer->val right)))
            (cond ((> lv rv) 1)
                  ((= lv rv) 0)
                  ((< lv rv) -1))))
          ((:integer &) -1)
          ((:atom :atom) 
           (b* ((lv (erl-val-atom->val left))
                 (rv (erl-val-atom->val right))
                 (l (string=>nats (symbol-name lv)))
                 (r (string=>nats (symbol-name rv))))
                 (erl-compare-atom-string l r)))
          ((:atom :integer) 1)
          ((:atom &) -1)
          ((:tuple :tuple)
           (let ((llst (erl-val-tuple->lst left))
                 (rlst (erl-val-tuple->lst right))) 
             (cond 
               ((> (len llst) (len rlst)) 1)
               ((> (len rlst) (len llst)) -1)
               (t (erl-compare-by-elements llst rlst)))))
          ((:tuple :integer) 1)
          ((:tuple :atom) 1)
          ((:tuple &) -1)
          ((:cons :cons) 
           (let ((llst (erl-val-cons->lst left))
                 (rlst (erl-val-cons->lst right)))
            (erl-compare-by-elements llst rlst)))
          ((:cons :integer) 1)
          ((:cons :atom) 1)
          ((:cons :tuple) 1)
          ((:cons &) -1)
          (:otherwise 3))))

  (define erl-compare-by-elements ((left erl-vlst-p) (right erl-vlst-p))
    :returns (i integerp)
    :measure (erl-vlst-count left)
    (b* ((left (erl-vlst-fix left))
         (right (erl-vlst-fix right)))
        (cond 
          ((and (null left) (null right)) 0)
          ((null left) -1)
          ((null right) 1)
          (t (let ((curr (erl-compare (car left) (car right))))
                  (cond 
                    ((equal curr 1) 1)
                    ((equal curr -1) -1)
                    ((equal curr 0) (erl-compare-by-elements (cdr left) (cdr right)))
                    (t curr))))))))

; Some tests for erl-compare
; (and
;   (equal (erl-compare '(:integer 9) '(:integer 3)) 1)
;   (equal (erl-compare '(:integer 3) '(:integer 3)) 0)
;   (equal (erl-compare '(:integer 1) '(:integer 3)) -1)


;   (equal (erl-compare '(:atom z) '(:atom foo)) 1)
;   (equal (erl-compare '(:atom foo) '(:atom foo)) 0)
;   (equal (erl-compare '(:atom bar) '(:atom foo)) -1)

;   (equal (erl-compare '(:integer 100) '(:atom foo)) -1)
;   (equal (erl-compare '(:integer 100) '(:tuple nil)) -1)
;   (equal (erl-compare '(:tuple nil) '(:cons nil)) -1)

;   (equal (erl-compare '(:tuple ((:integer 1))) '(:tuple ((:integer 0)))) 1)
;   (equal (erl-compare '(:tuple ((:integer 1))) '(:tuple ((:integer 1)))) 0)
;   (equal (erl-compare '(:tuple ((:integer 1))) '(:tuple ((:integer 2)))) -1)
;   (equal (erl-compare '(:tuple ((:integer 1) (:integer 2))) 
;                       '(:tuple ((:integer 1) (:integer 1)))) 
;           1)
;   (equal (erl-compare '(:tuple ((:integer 2))) 
;                       '(:tuple ((:integer 1) (:integer 1)))) 
;           -1)
  
;   (equal (erl-compare '(:cons ((:integer 1))) '(:cons ((:integer 0)))) 1)
;   (equal (erl-compare '(:cons ((:integer 1))) '(:cons ((:integer 1)))) 0)
;   (equal (erl-compare '(:cons ((:integer 1))) '(:cons ((:integer 2)))) -1)
;   (equal (erl-compare '(:cons ((:integer 1) (:integer 2))) 
;                       '(:cons ((:integer 1) (:integer 1)))) 
;           1)
;   (equal (erl-compare '(:cons ((:integer 2))) 
;                       '(:cons ((:integer 1) (:integer 1)))) 
;           1))

; Given a comparison binop, apply the corresponding Erlang operation.
(define apply-erl-comp-binop ((op comp-binop-p) (left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((op (comp-binop-fix op))
       (left (erl-val-fix left))
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
       (comp (erl-compare left right))
       ((if (equal comp 3)) (make-erl-val-reject :err "erl-compare called with inavlid term.")))
      (case op
        (== 
          (if (equal comp 0)
              (make-erl-val-atom :val 'true)
              (make-erl-val-atom :val 'false)))
        (/= 
          (if (not (equal comp 0))
              (make-erl-val-atom :val 'true)
              (make-erl-val-atom :val 'false)))
        (=< 
          (if (or (equal comp 0) (equal comp -1))
              (make-erl-val-atom :val 'true)
              (make-erl-val-atom :val 'false)))
        (< 
          (if (equal comp -1)
              (make-erl-val-atom :val 'true)
              (make-erl-val-atom :val 'false)))
        (>=
          (if (or (equal comp 0) (equal comp 1))
              (make-erl-val-atom :val 'true)
              (make-erl-val-atom :val 'false)))
        (>
          (if (equal comp 1)
              (make-erl-val-atom :val 'true)
              (make-erl-val-atom :val 'false)))
        (=-colon-=
          (if (equal left right)
              (make-erl-val-atom :val 'true)
              (make-erl-val-atom :val 'false)))
        (=/=
          (if (not (equal left right))
              (make-erl-val-atom :val 'true)
              (make-erl-val-atom :val 'false)))
        (otherwise (make-erl-val-reject :err "bad op"))))
    ///
      (defrule apply-erl-comp-binop-of-flimit
        (implies
          (and (erl-val-p left) (erl-val-p right) (comp-binop-p op)) 
          (iff (not (equal (erl-val-kind (apply-erl-comp-binop op left right)) :flimit))
               (and (not (equal (erl-val-kind left) :flimit))
                    (not (equal (erl-val-kind right) :flimit)))))))

; Apply Erlang List Operations -------------------------------------------------

; Representation of Erlang list concatenation (++) in ACL2.
; Since pairs are not supported currently, the arguments must be lists.
; - Returns badarg if the arguments are not lists.
(define erl-concat ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
       ((unless 
          (and (equal (erl-val-kind left) :cons) 
               (equal (erl-val-kind right) :cons)))
        (make-erl-val-excpt 
          :err (make-erl-err :class (make-err-class-error)
                             :reason (make-exit-reason-badarg))))
       (left-lst (erl-val-cons->lst left))
       (right-lst (erl-val-cons->lst right)))
      (make-erl-val-cons :lst (append left-lst right-lst))))

; Representation of Erlang list substraction (--) in ACL2.
; Since pairs are not supported currently, the arguments must be lists.
; - Returns badarg if the arguments are not lists.
(define erl-substract ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
       ((unless 
          (and (equal (erl-val-kind left) :cons) 
               (equal (erl-val-kind right) :cons)))
        (make-erl-val-excpt 
          :err (make-erl-err :class (make-err-class-error)
                             :reason (make-exit-reason-badarg))))
       (left-lst (erl-val-cons->lst left))
       (right-lst (erl-val-cons->lst right)))
      (make-erl-val-cons :lst (remove-first-of-each right-lst left-lst))))

; Given a list-op, apply the corresponding Erlang operation.
(define apply-erl-list-op ((op list-op-p) (left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((op (list-op-fix op))
       (left (erl-val-fix left))
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right)
       ((unless 
          (and (equal (erl-val-kind left) :cons)
               (equal (erl-val-kind right) :cons)))
        (make-erl-val-excpt 
          :err (make-erl-err :class (make-err-class-error)
                             :reason (make-exit-reason-badarg)))))
      (case op
        (++ (erl-concat left right))
        (-- (erl-substract left right))
        (otherwise (make-erl-val-reject :err "bad op"))))
    ///
      (defrule apply-erl-list-op-of-flimit
        (implies
          (and (erl-val-p left) (erl-val-p right) (list-op-p op)) 
          (iff (not (equal (erl-val-kind (apply-erl-list-op op left right)) :flimit))
               (and (not (equal (erl-val-kind left) :flimit))
                    (not (equal (erl-val-kind right) :flimit)))))
        :enable (erl-concat erl-substract)))


; Apply Erlang Binary Operations -----------------------------------------------

; Given a binop, apply the corresponding Erlang operation.
(define apply-erl-binop ((op erl-binop-p) (left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((op (erl-binop-fix op))
       (left (erl-val-fix left))
       (right (erl-val-fix right))
       ((if (equal (erl-val-kind left) :flimit)) left)
       ((if (equal (erl-val-kind right) :flimit)) right)
       ((if (equal (erl-val-kind left) :reject)) left)
       ((if (equal (erl-val-kind right) :reject)) right))
      (cond
        ((arithm-binop-p op) (apply-erl-arithm-binop op left right))
        ((bool-binop-p op) (apply-erl-bool-binop op left right))
        ((comp-binop-p op) (apply-erl-comp-binop op left right))
        ((list-op-p op) (apply-erl-list-op op left right))
        (t (make-erl-val-reject :err "bad op"))))
    ///
      (defrule apply-erl-binop-of-flimit
        (implies
          (and (erl-val-p left) (erl-val-p right) (erl-binop-p op)) 
          (iff (not (equal (erl-val-kind (apply-erl-binop op left right)) :flimit))
               (and (not (equal (erl-val-kind left) :flimit))
                    (not (equal (erl-val-kind right) :flimit)))))
        :use ((:instance apply-erl-arithm-binop-of-flimit)
              (:instance apply-erl-bool-binop-of-flimit)
              (:instance apply-erl-comp-binop-of-flimit)
              (:instance apply-erl-list-op-of-flimit))))


; Apply Erlang Unary Operations ------------------------------------------------

; Given an unop, apply the corresponding Erlang operation.
(define apply-erl-unop ((op erl-unop-p) (val erl-val-p))
  :returns (v erl-val-p)
  (b* ((op (erl-unop-fix op))
       (val (erl-val-fix val))
       ((if (equal (erl-val-kind val) :flimit)) val)
       ((if (equal (erl-val-kind val) :reject)) val))
      (case op
        (+ (erl-plus val))
        (- (erl-minus val))
        (not (erl-not val))
        (otherwise (make-erl-val-reject :err "bad op"))))
    ///
      (defrule apply-erl-unop-of-flimit
        (implies
          (erl-val-p val) 
          (iff (not (equal (erl-val-kind (apply-erl-unop op val)) :flimit))
               (not (equal (erl-val-kind val) :flimit))))
        :enable (erl-minus erl-plus erl-not)))