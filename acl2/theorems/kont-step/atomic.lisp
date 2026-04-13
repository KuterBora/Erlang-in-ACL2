(in-package "ACL2")
(include-book "../core/eval-theorems")


; Kont-Step for Atomic Expressions ---------------------------------------------

; The following theorems show the result of evaluating atomic expressions -- 
; integers, atoms, strings, empty lists, anononymous functions and variables.
;
; There are also some rules about excpetions, rejections, etc. 

; Integer
(defrule eval-k-of-expr-integer->klst
  (implies
    (and (erl-state-p s)
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :integer))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-expr-integer->s
  (implies
    (and (erl-state-p s)
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :integer))
    (equal (erl-s-klst->s (eval-k k s))
           (cond
            ((not (wf-state-p s)) s)
            ((not (> (erl-k->fuel k) 0))
             (update-erl-state->in s (make-erl-val-flimit)))
            (t (update-erl-state->in
                 s
                 (make-erl-val-integer
                   :val (node-integer->val
                          (kont-expr->expr (erl-k->kont k)))))))))
  :enable eval-k)


; Atom
; (defrule eval-k-of-expr-atom->klst
;   (implies
;     (and (wf-state-p s)
;          (erl-k-p k)
;          (> (erl-k->fuel k) 0)
;          (equal (kont-kind (erl-k->kont k)) :expr)
;          (equal (node-kind (kont-expr->expr (erl-k->kont k))) :atom))
;     (equal (erl-s-klst->klst (eval-k k s)) nil))
;   :enable eval-k)

; (defrule eval-k-of-expr-atom->s
;   (implies
;     (and (wf-state-p s)
;          (erl-k-p k)
;          (> (erl-k->fuel k) 0)
;          (equal (kont-kind (erl-k->kont k)) :expr)
;          (equal (node-kind (kont-expr->expr (erl-k->kont k))) :atom))
;     (equal (erl-s-klst->s (eval-k k s))
;            (update-erl-state->in
;              s
;              (make-erl-val-atom
;                :val (node-atom->val
;                       (kont-expr->expr (erl-k->kont k)))))))
;   :enable eval-k)


; String
; (defrule eval-k-of-expr-string->klst
;   (implies
;     (and (wf-state-p s)
;          (erl-k-p k)
;          (> (erl-k->fuel k) 0)
;          (equal (kont-kind (erl-k->kont k)) :expr)
;          (equal (node-kind (kont-expr->expr (erl-k->kont k))) :string))
;     (equal (erl-s-klst->klst (eval-k k s)) nil))
;   :enable eval-k)

; (defrule eval-k-of-expr-string->s
;   (implies
;     (and (wf-state-p s)
;          (erl-k-p k)
;          (> (erl-k->fuel k) 0)
;          (equal (kont-kind (erl-k->kont k)) :expr)
;          (equal (node-kind (kont-expr->expr (erl-k->kont k))) :string))
;     (equal (erl-s-klst->s (eval-k k s))
;            (update-erl-state->in
;              s
;              (string=>erl-cons
;                (node-string->val
;                  (kont-expr->expr (erl-k->kont k)))))))
;   :enable eval-k)


; Empty List
(defrule eval-k-of-expr-nil->klst
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :nil))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-expr-nil->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :nil))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->in
             s
             (make-erl-val-cons :lst nil))))
  :enable eval-k)


; Anonymous Function
; (defrule eval-k-of-expr-fun->klst
;   (implies
;     (and (wf-state-p s)
;          (erl-k-p k)
;          (> (erl-k->fuel k) 0)
;          (equal (kont-kind (erl-k->kont k)) :expr)
;          (equal (node-kind (kont-expr->expr (erl-k->kont k))) :fun))
;     (equal (erl-s-klst->klst (eval-k k s)) nil))
;   :enable eval-k)

; (defrule eval-k-of-expr-fun-ok->s
;   (implies
;     (and (wf-state-p s)
;          (erl-k-p k)
;          (> (erl-k->fuel k) 0)
;          (equal (kont-kind (erl-k->kont k)) :expr)
;          (equal (node-kind (kont-expr->expr (erl-k->kont k))) :fun)
;          (erl-clause-list->arity
;            (node-fun->cls (kont-expr->expr (erl-k->kont k)))))
;     (equal (erl-s-klst->s (eval-k k s))
;            (update-erl-state->in
;              s
;              (make-erl-val-fun
;                :arity (erl-clause-list->arity
;                         (node-fun->cls (kont-expr->expr (erl-k->kont k))))
;                :cls (node-fun->cls (kont-expr->expr (erl-k->kont k)))
;                :bind (erl-state->bind s)
;                :module (erl-state->module s)))))
;   :enable eval-k)

; (defrule eval-k-of-expr-fun-illformed->s
;   (implies
;     (and (wf-state-p s)
;          (erl-k-p k)
;          (> (erl-k->fuel k) 0)
;          (equal (kont-kind (erl-k->kont k)) :expr)
;          (equal (node-kind (kont-expr->expr (erl-k->kont k))) :fun)
;          (not (erl-clause-list->arity
;                 (node-fun->cls (kont-expr->expr (erl-k->kont k))))))
;     (equal (erl-s-klst->s (eval-k k s))
;            (update-erl-state->in
;              s
;              (make-erl-val-reject
;                :err "erl-eval: ill-formed fun clauses"))))
;   :enable eval-k)

; (defrule eval-k-of-expr-fun->s
;   (implies
;     (and (wf-state-p s)
;          (erl-k-p k)
;          (> (erl-k->fuel k) 0)
;          (equal (kont-kind (erl-k->kont k)) :expr)
;          (equal (node-kind (kont-expr->expr (erl-k->kont k))) :fun))
;     (equal 
;       (erl-s-klst->s (eval-k k s))
;       (if (erl-clause-list->arity (node-fun->cls (kont-expr->expr (erl-k->kont k))))
;           (update-erl-state->in
;              s
;              (make-erl-val-fun
;                :arity (erl-clause-list->arity
;                         (node-fun->cls (kont-expr->expr (erl-k->kont k))))
;                :cls (node-fun->cls (kont-expr->expr (erl-k->kont k)))
;                :bind (erl-state->bind s)
;                :module (erl-state->module s)))
;           (update-erl-state->in
;             s
;             (make-erl-val-reject :err "erl-eval: ill-formed fun clauses")))))
;   :enable eval-k)

; Variables
(defrule eval-k-of-expr-var->klst
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :var))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

; (defrule eval-k-of-expr-var-bound->s
;   (implies
;     (and (wf-state-p s)
;          (erl-k-p k)
;          (> (erl-k->fuel k) 0)
;          (equal (kont-kind (erl-k->kont k)) :expr)
;          (equal (node-kind (kont-expr->expr (erl-k->kont k))) :var)
;          (omap::assoc
;            (node-var->id (kont-expr->expr (erl-k->kont k)))
;            (erl-state->bind s)))
;     (equal
;       (erl-s-klst->s (eval-k k s))
;       (update-erl-state->in
;         s
;         (omap::lookup
;           (node-var->id (kont-expr->expr (erl-k->kont k)))
;           (erl-state->bind s)))))
;   :enable eval-k)

; (defrule eval-k-of-expr-var-unbound->s
;   (implies
;     (and (wf-state-p s)
;          (erl-k-p k)
;          (> (erl-k->fuel k) 0)
;          (equal (kont-kind (erl-k->kont k)) :expr)
;          (equal (node-kind (kont-expr->expr (erl-k->kont k))) :var)
;          (not (omap::assoc
;                 (node-var->id (kont-expr->expr (erl-k->kont k)))
;                 (erl-state->bind s))))
;     (equal
;       (erl-s-klst->s (eval-k k s))
;       (update-erl-state->in
;         s
;         (make-erl-val-reject :err "unbound variable"))))
;   :enable eval-k)

(defrule eval-k-of-expr-var->s
  (implies
    (and (wf-state-p s)
         (erl-k-p k)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :var))
    (equal
      (erl-s-klst->s (eval-k k s))
      (if (omap::assoc
           (node-var->id (kont-expr->expr (erl-k->kont k)))
           (erl-state->bind s))
          (update-erl-state->in
            s
            (omap::lookup
              (node-var->id (kont-expr->expr (erl-k->kont k)))
              (erl-state->bind s)))
          (update-erl-state->in
            s
            (make-erl-val-reject :err "unbound variable")))))
:enable eval-k)