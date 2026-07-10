(in-package "ACL2")
(include-book "../core/top")

; Kont-Step for Atomic Expressions ---------------------------------------------

; The following theorems show the result of evaluating atomic expressions -- 
; integers, atoms, strings, empty lists, anononymous functions and variables.
;
; There are also some rules about excpetions, rejections, etc. 

; Integer
(defrule eval-k-of-expr-integer->klst
  (implies
    (and (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :integer))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-expr-integer->s
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :integer))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->in
             s
             (make-erl-val-integer
               :val (node-integer->val
                      (kont-expr->expr (erl-k->kont k)))))))
  :enable eval-k)

(defrule apply-k-of-expr-integer
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :integer))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in
             s
             (make-erl-val-integer
               :val (node-integer->val
                      (kont-expr->expr (erl-k->kont k)))))))
  :enable apply-k-of-step)

(defrule apply-k-of-expr-integer-wf
  (implies
    (and (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :integer)
         (wf-state-p (apply-k s (cons k nil))))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in
             s
             (make-erl-val-integer
               :val (node-integer->val
                      (kont-expr->expr (erl-k->kont k))))))))

; Atom
(defrule eval-k-of-expr-atom->klst
  (implies
    (and (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :atom))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-expr-atom->s
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :atom))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->in
                   s
                   (make-erl-val-atom
                     :val (node-atom->val
                       (kont-expr->expr (erl-k->kont k)))))))
  :enable eval-k)

(defrule apply-k-of-expr-atom
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :atom))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in
             s
             (make-erl-val-atom
               :val (node-atom->val
                      (kont-expr->expr (erl-k->kont k)))))))
  :enable apply-k-of-step)

(defrule apply-k-of-expr-atom-wf
  (implies
    (and (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :atom)
         (wf-state-p (apply-k s (cons k nil))))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in
             s
             (make-erl-val-atom
               :val (node-atom->val
                      (kont-expr->expr (erl-k->kont k))))))))


; String
(defrule eval-k-of-expr-string->klst
  (implies
    (and (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :string))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-expr-string->s
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :string))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->in
              s
              (string=>erl-cons
                (node-string->val
                  (kont-expr->expr (erl-k->kont k)))))))
  :enable eval-k)

(defrule apply-k-of-string
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :string))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in
             s
             (string=>erl-cons
               (node-string->val
                 (kont-expr->expr (erl-k->kont k)))))))
  :enable apply-k-of-step)

(defrule apply-k-of-string-wf
  (implies
    (and (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :string)
         (wf-state-p (apply-k s (cons k nil))))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in
             s
             (string=>erl-cons
               (node-string->val
                 (kont-expr->expr (erl-k->kont k))))))))


; Empty List
(defrule eval-k-of-expr-nil->klst
  (implies
    (and (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :nil))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-expr-nil->s
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :nil))
    (equal (erl-s-klst->s (eval-k k s))
           (update-erl-state->in
             s
             (make-erl-val-cons :lst nil))))
  :enable eval-k)

(defrule apply-k-of-expr-nil
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :nil))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in
             s
             (make-erl-val-cons :lst nil))))
  :enable apply-k-of-step)

(defrule apply-k-of-expr-nil-wf
  (implies
    (and (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :nil)
         (wf-state-p (apply-k s (cons k nil))))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in
             s
             (make-erl-val-cons :lst nil)))))


; Anonymous Function
(defrule eval-k-of-expr-fun->klst
  (implies
    (and (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :fun))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-expr-fun->s
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :fun))
    (equal (erl-s-klst->s (eval-k k s))
           (cond
            ((not (erl-clause-list->arity
                    (node-fun->cls (kont-expr->expr (erl-k->kont k)))))
             (update-erl-state->in
               s 
               (make-erl-val-reject :err "erl-eval: ill-formed fun clauses")))
            (t (update-erl-state->in
                 s
                 (make-erl-val-fun
                   :arity (erl-clause-list->arity
                            (node-fun->cls (kont-expr->expr (erl-k->kont k))))
                   :cls (node-fun->cls (kont-expr->expr (erl-k->kont k)))
                   :bind (erl-state->bind s)
                   :module (erl-state->module s)))))))
  :enable eval-k)

(defrule apply-k-of-expr-fun
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :fun))
    (equal (apply-k s (cons k nil))
           (cond
             ((not (erl-clause-list->arity
                     (node-fun->cls (kont-expr->expr (erl-k->kont k)))))
              (update-erl-state->in
                s 
                (make-erl-val-reject :err "erl-eval: ill-formed fun clauses")))
             (t (update-erl-state->in
                  s
                  (make-erl-val-fun
                    :arity (erl-clause-list->arity
                             (node-fun->cls (kont-expr->expr (erl-k->kont k))))
                    :cls (node-fun->cls (kont-expr->expr (erl-k->kont k)))
                    :bind (erl-state->bind s)
                    :module (erl-state->module s)))))))
  :enable apply-k-of-step)

(defrule clause-arity-of-expr-fun-wf
  (implies
    (and (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :fun)
         (wf-state-p (apply-k s (cons k nil))))
    (erl-clause-list->arity (node-fun->cls (kont-expr->expr (erl-k->kont k)))))
  :disable apply-k-of-expr-fun
  :use (:instance apply-k-of-expr-fun (s s) (k k)))

(defrule apply-k-of-expr-fun-wf
  (implies
    (and (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :fun)
         (wf-state-p (apply-k s (cons k nil))))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in
             s
             (make-erl-val-fun
               :arity (erl-clause-list->arity
                        (node-fun->cls (kont-expr->expr (erl-k->kont k))))
               :cls (node-fun->cls (kont-expr->expr (erl-k->kont k)))
               :bind (erl-state->bind s)
               :module (erl-state->module s))))))


; Variables
(defrule eval-k-of-expr-var->klst
  (implies
    (and (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :var))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-k-of-expr-var->s
  (implies
    (and (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :var))
    (equal
      (erl-s-klst->s (eval-k k s))
      (cond
        ((not (omap::assoc (node-var->id (kont-expr->expr (erl-k->kont k)))
                           (erl-state->bind s)))
         (update-erl-state->in 
           s
           (make-erl-val-reject :err "unbound variable")))
        (t (update-erl-state->in
             s
             (omap::lookup
               (node-var->id (kont-expr->expr (erl-k->kont k)))
               (erl-state->bind s)))))))
:enable eval-k)

(defrule apply-k-of-expr-var
  (implies
    (and (wf-state-p s)
         (> (erl-k->fuel k) 0)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :var))
    (equal (apply-k s (cons k nil))
           (cond
             ((not (omap::assoc (node-var->id (kont-expr->expr (erl-k->kont k)))
                                (erl-state->bind s)))
              (update-erl-state->in 
                s
                (make-erl-val-reject :err "unbound variable")))
             (t (update-erl-state->in
                  s
                  (omap::lookup
                    (node-var->id (kont-expr->expr (erl-k->kont k)))
                    (erl-state->bind s)))))))
  :enable apply-k-of-step)

(defrule bind-of-expr-var-wf
  (implies
    (and (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :var)
         (wf-state-p (apply-k s (cons k nil))))
    (omap::assoc (node-var->id (kont-expr->expr (erl-k->kont k)))
                 (erl-state->bind s)))
  :disable apply-k-of-expr-var
  :use (:instance apply-k-of-expr-var (s s) (k k)))

(defrule apply-k-of-expr-var-wf
  (implies
    (and (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :var)
         (wf-state-p (apply-k s (cons k nil))))
    (equal (apply-k s (cons k nil))
           (update-erl-state->in
             s
             (omap::lookup
               (node-var->id (kont-expr->expr (erl-k->kont k)))
               (erl-state->bind s))))))