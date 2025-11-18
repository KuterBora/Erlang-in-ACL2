(in-package "ACL2")
(include-book "erl-ast")
(include-book "ast-theorems")
(include-book "erl-value")
(include-book "erl-op")

(set-induction-depth-limit 1)

; Erl Guard Count Decreases ----------------------------------------------------
(local (defrule node-count-of-guard-cons->tl
  (implies (equal (node-kind (guard-expr-fix x))
                :cons)
         (< (node-count (node-cons->tl (guard-expr-fix x)))
            (node-count x)))
  :enable guard-expr-fix))

(local (defrule node-count-of-guard-cons->hd
  (implies (equal (node-kind (guard-expr-fix x))
                :cons)
         (< (node-count (node-cons->hd (guard-expr-fix x)))
            (node-count x)))
  :enable guard-expr-fix))

(local (defrule node-count-of-guard-binop->left
  (implies (equal (node-kind (guard-expr-fix x))
                :binop)
         (< (node-count (node-binop->left (guard-expr-fix x)))
            (node-count x)))
  :enable guard-expr-fix))

(local (defrule node-count-of-guard-binop->right
  (implies (equal (node-kind (guard-expr-fix x))
                :binop)
         (< (node-count (node-binop->right (guard-expr-fix x)))
            (node-count x)))
  :enable guard-expr-fix))

(local (defrule node-count-of-guard-unop
  (implies (equal (node-kind (guard-expr-fix x))
                :unop)
         (< (node-count (node-unop->expr (guard-expr-fix x)))
            (node-count x)))
  :enable guard-expr-fix))

(local (defrule node-count-of-guard-tuple-cdr
  (implies
     (and (equal (node-kind (guard-expr-fix x))
                 :tuple)
          (node-tuple->lst (guard-expr-fix x)))
     (< (node-count (node-tuple (cdr (node-tuple->lst (guard-expr-fix x)))))
        (node-count x)))
  :enable (guard-expr-fix node-count node-list-count)))

(local (defrule node-count-of-guard-tuple-car
  (implies (and (equal (node-kind (guard-expr-fix x))
                     :tuple)
              (node-tuple->lst (guard-expr-fix x)))
         (< (node-count (car (node-tuple->lst (guard-expr-fix x))))
            (node-count x)))
  :enable guard-expr-fix))



; Evaluate an Erlang Guard Expression ------------------------------------------

(define eval-guard ((x guard-expr-p) (bind bind-p))
  :returns (v erl-val-p)
  :measure (node-count x)
  :verify-guards nil
  (b* ((x (guard-expr-fix x))
       (bind (bind-fix bind)))
    (node-case x
      (:integer (make-erl-val-integer :val x.val))
      (:string  (make-erl-val-string :val x.val))
      (:atom (make-erl-val-atom :val x.val))
      (:nil (make-erl-val-cons :lst nil))
      ; TODO: pairs can exist, string are lists
      (:cons (b* ((hd (eval-guard x.hd bind))
                  (tl (eval-guard x.tl bind))
                  ((if (equal (erl-val-kind hd) :reject)) hd)
                  ((if (equal (erl-val-kind tl) :reject)) tl)
                  ((if (equal (erl-val-kind hd) :excpt)) hd)
                  ((if (equal (erl-val-kind tl) :excpt)) tl)
                  ((unless (equal (erl-val-kind tl) :cons))
                    (make-erl-val-reject :err "Eval-Guard: cons expects list.")))
                 (make-erl-val-cons :lst (cons hd (erl-val-cons->lst tl)))))
      (:tuple (b* (((if (null x.lst)) (make-erl-val-tuple :lst nil))
                   (hd (eval-guard (car x.lst) bind))
                   (tl (eval-guard (make-node-tuple :lst (cdr x.lst)) bind))
                   ((if (equal (erl-val-kind hd) :reject)) hd)
                   ((if (equal (erl-val-kind tl) :reject)) tl)
                   ((if (equal (erl-val-kind hd) :excpt)) hd)
                   ((if (equal (erl-val-kind tl) :excpt)) tl)
                   ((unless (equal (erl-val-kind tl) :tuple))
                    (make-erl-val-reject :err "Eval-Guard: tuple expects tuple.")))
                 (make-erl-val-tuple :lst (cons hd (erl-val-tuple->lst tl)))))

      (:var 
        (if (omap::assoc x.id bind)
            (omap::lookup x.id bind)
            (make-erl-val-reject :err "unbound variable")))
      (:unop (apply-erl-unop x.op (eval-guard x.expr bind)))
      (:binop
        (b* ((left (eval-guard x.left bind))
             (right (eval-guard x.right bind)))
            (apply-erl-binop x.op left right)))
      (:match (make-erl-val-reject :err "Guard expressions cannot have match."))
      (:if (make-erl-val-reject :err "Guard expressions cannot have if clauses."))
      (:case-of (make-erl-val-reject :err "Guard expressions cannot have case clauses."))))

  ///
    (verify-guards eval-guard))


; Evaluate a Sequence of Guard Expressions -------------------------------------

; Guards evaluation returns '(:atom true) if every guard in the sequence evaluates 
; to '(:atom true). Otherwise, return last evaluated guard.
(define eval-guards ((x guard-expr-list-p) (bind bind-p))
  :returns (bool erl-val-p)
  :measure (len (guard-expr-list-fix x))
  :verify-guards nil
  (b* ((x (guard-expr-list-fix x))
       (bind (bind-fix bind))
       ((if (null x)) (make-erl-val-atom :val 'true))
       (hd (eval-guard (car x) bind))
       ((unless (and (equal (erl-val-kind hd) :atom) 
                     (equal (erl-val-atom->val hd) 'true)))
        hd))
      (eval-guards (cdr x) bind))
    ///
      (verify-guards eval-guards))