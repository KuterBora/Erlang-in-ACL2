(in-package "ACL2")
(include-book "erl-ast")
(include-book "ast-theorems")
(include-book "erl-value")
(include-book "erl-op")
; (include-book "erl-world")
; (include-book "functions")

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


(defines erl-guards
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
        (:case-of (make-erl-val-reject :err "Guard expressions cannot have case clauses."))
        (:remote-call (make-erl-val-reject :err "Guard expressions can only have calls to BIFs."))
        (:call
          (b* ((fn (make-fn :name x.fn :arity (len x.args)))
               ((unless (erl-bif-p fn)) 
                (make-erl-reject :err "Call to functions other than BIFs are illegal in guards."))
               (vlst (eval-guard-args x.args bind))
               ((if (erl-val-p vlst)) vlst))
              (eval-bif fn args)))))
    ///
      (verify-guards eval-guard))
  
  (define eval-guard-args ((x guard-expr-list-p) (bind bind-p))
    :returns (or (vlst erl-vlst-p) (r erl-val-p))
    :measure (node-list-clause (guard-expr-list-fix x))
    :verify-guards nil
    (b* ((x (guard-expr-list-fix x))
         (bind (bind-fix bind))
         ((if (erl-val-p x)) x)
         ((if (null x)) nil)
         (hd (eval-guard (car x) bind))
         ((if (equal (erl-val-kind hd) :reject)) hd)
         ((if (equal (erl-val-kind hd) :excpt)) hd)
         (tl (eval-guard-args (cdr x) bind)))
        (cons hd tl)))
    ///
      (verify-guards eval-guard-args)
      (more-returns
        (r (implies (erl-val-p r) (or (equal (erl-val-kind r) :reject)
                                      (equal (erl-val-kind r) :excpt)))
          :name val-kind-of-eval-guard-args)))


; Evaluate a Sequence of Guard Expressions -------------------------------------

; Evaluate a sequence of guard expression
; Returns '(:atom true) if every guard expression in the sequence evaluates 
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

; Evaluate a guard sequence
; Returns '(:atom true) if any of the alternate cases return true
(define eval-guard-seq ((x guard-expr-lists-p) (bind bindp))
  :returns (bool erl-val-p)
  :measure (len (guard-expr-lists-fix x))
  :verify-guards nil
  (b* ((x (guard-expr-lists-fix x))
       (bind (bind-fix bind))
       ((if (null x)) (make-erl-val-atom :val 'false))
       (hd (eval-guards (car x) bind))
       ((if (equal (erl-val-kind hd) :reject)) hd)
       ((if (and (equal (erl-val-kind hd) :atom) 
                 (equal (erl-val-atom->val hd) 'true)))
        hd))
      (eval-guard-seq (cdr x) bind))
    ///
      (verify-guards eval-guard-seq))
