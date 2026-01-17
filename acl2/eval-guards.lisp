(in-package "ACL2")
(include-book "erl-ast")
(include-book "ast-theorems")
(include-book "erl-value")
(include-book "erl-op")
(include-book "erl-world")

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


; Evaluate Erlang Guard Expressions --------------------------------------------

; Erlang reference manual explains: The set of valid guard expressions is a 
; subset of the set of valid Erlang expressions. The reason for restricting the 
; set of valid expressions is that evaluation of a guard expression must be 
; guaranteed to be free of side effects.
;
; Supported guard expressions:
; - (Bound) Variables
; - Consntants (atoms, integers, lists, tuples)
; - Expressions that construct atoms, integer, lists and tuples
; - Calls to certain BIFs (defined in world.lisp)
; - Term Comparisons
; - Arithmetic expressions
; - Boolean expressions
; - Short-circuit operations
;
; Remarks:
; - Currently, all operations included in erl-binop and erl-unop are allowed in
;   guard-expressions.
; - Unlike in patterns, arithmetic expressions in guards do not seem to be
;   evaluated at compile time. Thus, they can cause exceptions, and they will
;   not be rejected by the interpreter if they do.
;
; Guards allowed by Erlang that are not supported:
; - Floats, records, maps and binaries
; - Expressions that construct floats, records, maps and binaries
; - Expressions that update a map
; - The record expressions Expr#Name.Field and #Name.Field
(defines erl-guards
  ; Evaluate the guard expressions 'x' with the bindings 'bind'. Return the
  ; erl-value produced.  
  (define eval-guard-expr ((x guard-expr-p) (bind bind-p))
    :returns (v erl-val-p)
    :measure (node-count x)
    :verify-guards nil
    (b* ((x (guard-expr-fix x))
         (bind (bind-fix bind)))
      (node-case x
        (:integer (make-erl-val-integer :val x.val))
        (:atom (make-erl-val-atom :val x.val))
        (:nil (make-erl-val-cons :lst nil))
        (:cons (b* ((hd (eval-guard-expr x.hd bind))
                    (tl (eval-guard-expr x.tl bind))
                    ((if (equal (erl-val-kind hd) :reject)) hd)
                    ((if (equal (erl-val-kind tl) :reject)) tl)
                    ((if (equal (erl-val-kind hd) :excpt)) hd)
                    ((if (equal (erl-val-kind tl) :excpt)) tl)
                    ((unless (equal (erl-val-kind tl) :cons))
                      (make-erl-val-reject :err "Eval-Guard: tl of cons must be a list.")))
                  (make-erl-val-cons :lst (cons hd (erl-val-cons->lst tl)))))
        (:tuple (b* (((if (null x.lst)) (make-erl-val-tuple :lst nil))
                     (hd (eval-guard-expr (car x.lst) bind))
                     (tl (eval-guard-expr (make-node-tuple :lst (cdr x.lst)) bind))
                     ((if (equal (erl-val-kind hd) :reject)) hd)
                     ((if (equal (erl-val-kind tl) :reject)) tl)
                     ((if (equal (erl-val-kind hd) :excpt)) hd)
                     ((if (equal (erl-val-kind tl) :excpt)) tl)
                     ((unless (equal (erl-val-kind tl) :tuple))
                      (make-erl-val-reject :err "Eval-Guard: ill-formed tuple.")))
                    (make-erl-val-tuple :lst (cons hd (erl-val-tuple->lst tl)))))
        (:var
          (if (omap::assoc x.id bind)
              (omap::lookup x.id bind)
              (make-erl-val-reject :err "unbound variable")))
        (:unop (apply-erl-unop x.op (eval-guard-expr x.expr bind)))
        (:binop
          (b* ((left (eval-guard-expr x.left bind))
               (right (eval-guard-expr x.right bind)))
              (apply-erl-binop x.op left right)))
        (:match (make-erl-val-reject :err "Guard expressions cannot have match."))
        (:if (make-erl-val-reject :err "Guard expressions cannot have if clauses."))
        (:case-of (make-erl-val-reject :err "Guard expressions cannot have case clauses."))
        (:remote-call (make-erl-val-reject :err "Guard expressions can only have calls to BIFs."))
        (:call
          (b* ((fn (make-fn :name x.fn :arity (len x.args)))
               ((unless (erl-bif-p fn)) 
                (make-erl-reject :err "Guard expressions can only have calls to BIFs."))
               (vlst (eval-guard-expr-list x.args bind))
               ((if (erl-val-p vlst)) vlst))
              (eval-bif fn args)))))
    ///
      (verify-guards eval-guard-expr))
  
  ; Evaluate each guard expression in the list, return the list of results.
  ; However, if any expression causes a rejecetion, stop evaluation and return its value.
  (define eval-guard-expr-list ((x guard-expr-list-p) (bind bind-p))
    :returns (or (vlst erl-vlst-p) (r erl-val-p))
    :measure (node-list-clause (guard-expr-list-fix x))
    :verify-guards nil
    (b* ((x (guard-expr-list-fix x))
         (bind (bind-fix bind))
         ((if (erl-val-p x)) x)
         ((if (null x)) nil)
         (hd (eval-guard-expr (car x) bind))
         ((if (equal (erl-val-kind hd) :reject)) hd)
         ((if (equal (erl-val-kind hd) :excpt)) hd)
         (tl (eval-guard-expr-list (cdr x) bind)))
        (cons hd tl)))
    ///
      (verify-guards eval-guard-expr-list)
      (more-returns
        (r (implies (erl-val-p r) (or (equal (erl-val-kind r) :reject)
                                      (equal (erl-val-kind r) :excpt)))
          :name val-kind-of-eval-guard-expr-list)))


; Evaluate Guard Sequences -----------------------------------------------------

; Erlang reference manual explains:
; - A guard sequence is true if at least one of the guards is true. 
;   (The remaining guards, if any, are not evaluated.)
; - A guard is a sequence of guard expressions. The guard is true if all guard 
;   expressions evaluate to true.
;
; Remark: Exceptions raised by guards are equivalent to the guard evaluating to
; false, and will not alter the control flow.
;
; These function does not directly follow the Erlang control flow. In Erlang, 
; once a guard from the sequence evaluates to true, the remaining guards, 
; if any, are not evaluated. However, to be able to reject invalid guards that
; would have been discovered during compilation in Erlang, the ACL2 interpreter 
; still needs to go through the rest of the guards and look for rejections.
; This ensures the output is equivalent to that in Erlang. In the future,
; ASTz could be checked for well-formedness before interpretetion to account for
; cases like these. 

; Return '(:atom true) if every guard expression in the sequence evaluates 
; to '(:atom true). If any guard expressions evaluates to a different value,
; including rejection, return that value.
(define eval-guard ((x guard-expr-list-p) (bind bind-p))
  :returns (result erl-val-p)
  :measure (len (guard-expr-list-fix x))
  :verify-guards nil
  (b* ((x (guard-expr-list-fix x))
       (bind (bind-fix bind))
       ((if (null x)) (make-erl-val-atom :val 'true))
       (hd (eval-guard-expr (car x) bind))
       (tl (eval-guard (cdr x) bind))
       ((if (equal (erl-val-kind hd) :reject)) hd)
       ((if (equal (erl-val-kind tl) :reject)) tl)
       ((unless (and (equal (erl-val-kind hd) :atom) 
                     (equal (erl-val-atom->val hd) 'true)))
        hd))
      tl)
    ///
      (verify-guards eval-guard))

; Return '(:atom true) if any guard expression in the sequence evaluates 
; to '(:atom true). If any guard expressions evaluates to a rejection
; return that rejection. Otherwise, return '(:atom false).
(define eval-guard-seq-when-consp ((x guard-expr-lists-p) (bind bindp))
  :returns (result erl-val-p)
  :measure (len (guard-expr-lists-fix x))
  :verify-guards nil
  (b* ((x (guard-expr-lists-fix x))
       (bind (bind-fix bind))
       ((if (null x)) (make-erl-val-atom :val 'false))
       (hd (eval-guard (car x) bind))
       (tl (eval-guard-seq-when-consp (cdr x) bind))
       ((if (equal (erl-val-kind hd) :reject)) hd)
       ((if (equal (erl-val-kind tl) :reject)) tl)
       ((if (and (equal (erl-val-kind hd) :atom) 
                 (equal (erl-val-atom->val hd) 'true)))
        hd))
      tl)
    ///
      (verify-guards eval-guard-seq))

; If x is nil, return '(:atom true), otherwise evaluate the guard sequence.
; This distinction is needed because an empty guard sequence should be evaluted 
; to true, which is not reflected by the base case of eval-guard-seq-when-consp
; which checks if at least one of the guards in a non-empty sequence evaluate 
; to true.
(define eval-guard-seq ((x guard-expr-lists-p) (bind bindp))
  :returns (result erl-val-p)
  :measure (len (guard-expr-lists-fix x))
  :verify-guards nil
  (b* ((x (guard-expr-lists-fix x))
       (bind (bind-fix bind))
       ((if (null x)) (make-erl-val-atom :val 'true)))
      (eval-guard-seq-when-consp x bind))
    ///
      (verify-guards eval-guard-seq))