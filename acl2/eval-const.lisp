(in-package "ACL2")
(include-book "erl-ast")
(include-book "ast-theorems")
(include-book "erl-value")
(include-book "erl-op")

(set-induction-depth-limit 1)

; Evaluate Constant Erlang Expressions -----------------------------------------

(define eval-const ((x const-p))
  :returns (v erl-val-p)
  (b* ((x (const-fix x)))
    (node-case x
      (:integer (make-erl-val-integer :val x.val))
      (:string (make-erl-val-string :val x.val))
      (:atom (make-erl-val-atom :val x.val))
      (:nil (make-erl-val-cons :val nil))
      (:cons 
        ; TODO: there is no support for pairs currently
        (let ((hd (eval-const (node-cons->hd x)))
              (tl (eval-const (node-cons->tl x))))
             (if (equal (erl-val-kind tl) :cons)
                 (make-erl-val-cons :lst (cons hd (erl-val-cons->lst tl)))
                 (make-erl-val-reject :err "Eval-Const: Pairs are not supported."))))
      (:tuple
        (let ((hd (eval-const (car (node-tuple->lst x))))
              (rest (eval-const (make-node-tuple :lst (cdr (node-tuple->lst x))))))
             (if (equal (erl-val-kind tl) :tuple)
                 (make-erl-val-tuple :lst (cons hd (erl-val-tuple->lst rest)))
                 (make-erl-val-reject :err "Eval-Const: wrong type while evaluating tuple."))))
      (:var (make-erl-val-reject :err "Constants cannot have variables."))
      (:unop (apply-erl-unop (node-unop->op x) (eval-const (node-unop->expr x))))
      (:binop
        (let ((op (node-binop->op x))
              (left (eval-const (node-binop->left x)))
              (right (eval-const (node-binop->right x))))
             (apply-erl-binop op left right))))))


; Evaluate Numeric Erlang Expressions ------------------------------------------

(define eval-numeric ((x arithm-expr-p))
  :returns (v erl-val-p)
  (b* ((x (arithm-expr-fix x)))
    (node-case x
      (:integer (make-erl-val-integer :val x.val))
      (:string (make-erl-val-reject :err "Numeric expressions cannot have strings."))
      (:atom (make-erl-val-reject :err "Numeric expressions cannot have atoms."))
      (:nil (make-erl-val-reject :err "Numeric expressions cannot have lists."))
      (:cons (make-erl-val-reject :err "Numeric expressions cannot have lists."))
      (:tuple (make-erl-val-reject :err "Numeric expressions cannot have tuples."))
      (:var (make-erl-val-reject :err "Numeric expressions cannot have variables."))
      (:unop (apply-erl-unop (node-unop->op x) (eval-numeric (node-unop->expr x))))
      (:binop
        (let ((op (node-binop->op x))
              (left (eval-numeric (node-binop->left x)))
              (right (eval-numeric (node-binop->right x))))
             (apply-erl-binop op left right)))))
    
    ///
    (more-returns
      (v (or (equal (erl-val-kind v) :integer) (equal (erl-val-kind v) :reject))
        :rule-classes :type-prescription)))


