(in-package "ACL2")
(include-book "../core/eval-theorems")
; (include-book "../kont-step/top")

(set-induction-depth-limit 1)

;; TODO
; rules about wf-state-p
; make rewrite rules fire

(defrule crock-1
  (implies 
    (and (erl-state-p s)
         (not (wf-state-p s)))
    (equal (erl-s-klst->s (eval-k k s)) s))
  :enable eval-k)

(defrule crock-2
  (implies 
    (and (erl-state-p s)
         (not (wf-state-p s)))
    (equal (erl-s-klst->klst (eval-k k s)) nil))
  :enable eval-k)

(defrule eval-match-crock
  (implies
    (erl-state-p s)
    (equal (erl-state->world (eval-match p s))
           (erl-state->world s)))
  :enable eval-match)

(defrule eval-match-crock-2
  (implies
    (erl-state-p s)
    (equal (erl-state->module (eval-match p s))
           (erl-state->module s)))
  :enable eval-match)

(defrule match-args-crock
  (implies
    (erl-state-p s)
    (equal (erl-state->world (match-args cs args s))
           (erl-state->world s)))
  :enable match-args)

(defrule match-args-crock-2
  (implies
    (erl-state-p s)
    (equal (erl-state->module (match-args cs args s))
           (erl-state->module s)))
  :enable match-args)

(defrule eval-clauses-when-consp-crock
  (implies
    (erl-state-p s)
    (equal (erl-state->world (mv-nth 0 (eval-clauses-when-consp args cls s)))
           (erl-state->world s)))
  :enable eval-clauses-when-consp)

(defrule eval-clauses-when-consp-crock-2
  (implies
    (erl-state-p s)
    (equal (erl-state->module (mv-nth 0 (eval-clauses-when-consp args cls s)))
           (erl-state->module s)))
  :enable eval-clauses-when-consp)

(defrule eval-clauses-crock
  (implies
    (erl-state-p s)
    (equal (erl-state->world (mv-nth 0 (eval-clauses args cls s)))
           (erl-state->world s)))
  :enable eval-clauses)

(defrule eval-clauses-crock-2
  (implies
    (erl-state-p s)
    (equal (erl-state->module (mv-nth 0 (eval-clauses args cls s)))
           (erl-state->module s)))
  :enable eval-clauses)

(defrule eval-local-call-crock
  (implies
    (erl-state-p s)
    (equal (erl-state->world (mv-nth 0 (eval-local-call s c args)))
           (erl-state->world s)))
  :enable eval-local-call)

(defrule eval-remote-call-crock
  (implies
    (erl-state-p s)
    (equal (erl-state->world (mv-nth 0 (eval-remote-call s m c args)))
           (erl-state->world s)))
  :enable eval-remote-call)

(defrule eval-fun-call-crock
  (implies
    (erl-state-p s)
    (equal (erl-state->world (mv-nth 0 (eval-fun-call s f args)))
           (erl-state->world s)))
  :enable eval-fun-call)

; State Rules ------------------------------------------------------------------

; The following rules reason about how the erl-state changes during evaluation.

; The world never changes
(defrule apply-k-of-world
  (implies 
    (and (erl-klst-p klst) (erl-state-p s))
    (equal (erl-state->world (apply-k s klst))
           (erl-state->world s)))
  :enable (apply-k)
  :expand (eval-k (car klst) s)
  :disable (apply-k-of-step apply-k-of-consp))

(defrule eval-k-of-world
  (implies 
    (and (erl-k-p k) (erl-state-p s))
    (equal (erl-state->world (erl-s-klst->s (eval-k k s)))
           (erl-state->world s)))
  :enable eval-k)

; (defrule kont-kind-crock
;   (implies (and (erl-k-p k))
;            (equal (car (erl-k->kont k)) (kont-kind (erl-k->kont k))))
;   :enable (kont-kind erl-k-p kont-p erl-k->kont))

(defrule update->in-crock
  (equal (erl-val-kind (erl-state->in (update-erl-state->in s val)))
         (erl-val-kind val)))

(defrule fuel-crock
  (not (wf-state-p (update-erl-state->in s '(:flimit))))
  :enable wf-state-p)

; (defruled expr-expand-crock
;   (implies 
;     (and (erl-klst-p klst) (equal (kont-kind (erl-k->kont (car klst))) :expr))
;     (or (equal (node-kind (kont-expr->expr (erl-k->kont (car klst)))) :integer)
;         (equal (node-kind (kont-expr->expr (erl-k->kont (car klst)))) :atom)
;         (equal (node-kind (kont-expr->expr (erl-k->kont (car klst)))) :string)
;         (equal (node-kind (kont-expr->expr (erl-k->kont (car klst)))) :nil)
;         (equal (node-kind (kont-expr->expr (erl-k->kont (car klst)))) :fun)
;         (equal (node-kind (kont-expr->expr (erl-k->kont (car klst)))) :cons)
;         (equal (node-kind (kont-expr->expr (erl-k->kont (car klst)))) :tuple)
;         (equal (node-kind (kont-expr->expr (erl-k->kont (car klst)))) :var)
;         (equal (node-kind (kont-expr->expr (erl-k->kont (car klst)))) :unop)
;         (equal (node-kind (kont-expr->expr (erl-k->kont (car klst)))) :binop)
;         (equal (node-kind (kont-expr->expr (erl-k->kont (car klst)))) :match)
;         (equal (node-kind (kont-expr->expr (erl-k->kont (car klst)))) :if)
;         (equal (node-kind (kont-expr->expr (erl-k->kont (car klst)))) :case-of)
;         (equal (node-kind (kont-expr->expr (erl-k->kont (car klst)))) :remote-call)
;         (equal (node-kind (kont-expr->expr (erl-k->kont (car klst)))) :fun-call)
;         (equal (node-kind (kont-expr->expr (erl-k->kont (car klst)))) :call)))
;   :rule-classes :forward-chaining)

; (defruled kont-expand-crock
;   (implies 
;     (erl-k-p k)
;     (or (equal (kont-kind (erl-k->kont k)) :expr)
;         (equal (kont-kind (erl-k->kont k)) :cons)
;         (equal (kont-kind (erl-k->kont k)) :cons-merge)
;         (equal (kont-kind (erl-k->kont k)) :tuple)
;         (equal (kont-kind (erl-k->kont k)) :tuple-merge)
;         (equal (kont-kind (erl-k->kont k)) :unop)
;         (equal (kont-kind (erl-k->kont k)) :binop-expr1)
;         (equal (kont-kind (erl-k->kont k)) :binop-expr2)
;         (equal (kont-kind (erl-k->kont k)) :match)
;         (equal (kont-kind (erl-k->kont k)) :case-of)
;         (equal (kont-kind (erl-k->kont k)) :exprs)
;         (equal (kont-kind (erl-k->kont k)) :local-call)
;         (equal (kont-kind (erl-k->kont k)) :remote-call)
;         (equal (kont-kind (erl-k->kont k)) :fun-call-args)
;         (equal (kont-kind (erl-k->kont k)) :fun-call)
;         (equal (kont-kind (erl-k->kont k)) :function-return)))
;   :rule-classes :forward-chaining)

; (set-induction-depth-limit 1)

(defrule no-body-of-eval-remote-call-crock
  (implies (not (mv-nth 1 (eval-remote-call s m c args)))
           (or (equal (erl-val-kind (erl-state->in (mv-nth 0 (eval-remote-call s m c args)))) 
                      :reject)
               (equal (erl-val-kind (erl-state->in (mv-nth 0 (eval-remote-call s m c args))))
                      :excpt)))
  :enable eval-remote-call)

(defrule no-body-of-eval-fun-call-crock
  (implies (not (mv-nth 1 (eval-fun-call s f args)))
           (or (equal (erl-val-kind (erl-state->in (mv-nth 0 (eval-fun-call s f args)))) 
                      :reject)
               (equal (erl-val-kind (erl-state->in (mv-nth 0 (eval-fun-call s f args))))
                      :excpt)))
  :enable eval-fun-call)

(defrule no-body-of-eval-local-call-crock
  (implies (not (mv-nth 1 (eval-local-call s c args)))
           (or (equal (erl-val-kind (erl-state->in (mv-nth 0 (eval-local-call s c args)))) 
                      :reject)
               (equal (erl-val-kind (erl-state->in (mv-nth 0 (eval-local-call s c args))))
                      :excpt)
               (equal (erl-state->module (mv-nth 0 (eval-local-call s c args)))
                      (erl-state->module s))))
  :enable eval-local-call)

(defrule function-return-as-car-crock
  (not 
    (equal
      (kont-kind (erl-k->kont (car (erl-s-klst->klst (eval-k k s)))))
      :function-return))
  :enable eval-k)

; (defruled apply-k-of-pair
;   (implies 
;     (and (erl-state-p s)
;          (erl-k-p k1)
;          (erl-k-p k2))
;     (equal (apply-k s (list k1 k2))
;            (apply-k (apply-k s (list k1)) (list k2))))
;   :use (:instance apply-k-of-append
;         (s s)
;         (klst1 (list k1))
;         (klst2 (list k2))
;         (klst (list k1 k2))))

(defruled apply-k-of-consp-wf
  (implies 
    (and (erl-klst-p klst)
         (erl-state-p s)
         (consp klst)
         (wf-state-p (apply-k s klst)))
    (wf-state-p (apply-k s (list (car klst))))))

(defrule whyyyy
  (implies (and (erl-klst-p klst) (consp klst))
           (erl-k-p (car klst))))

; (define not-contains-return ((klst erl-klst-p))
;   :measure (len (erl-klst-fix klst))
;   (b* ((klst (erl-klst-fix klst))
;        ((unless klst) t))
;        (and (not (equal (kont-kind (erl-k->kont (car klst))) :function-return))
;             (not-contains-return (cdr klst)))))

; (defrule apply-k-of-module
;   (implies 
;     (and (erl-klst-p klst)
;          (wf-state-p s)
;          (> (erl-k->fuel (car klst)) 0)
;          (not-contains-return klst)
;          (not (consp (cdr klst)))
;          (wf-state-p (apply-k s klst)))
;     (equal (erl-state->module (apply-k s klst))
;            (erl-state->module s)))
;   :enable (apply-k not-contains-return)
;   :hints (
;     ("Subgoal *1/5.17''" :use (:instance kont-expand-crock (k (car klst))))
;     ("Subgoal *1/5.17.4" :use (:instance expr-expand-crock))
;     ("Subgoal *1/5.17.3" :by nil) ; remote
;     ("Subgoal *1/5.17.2" :by nil) ; fun
;     ("Subgoal *1/5.17.1" :by nil) ; local

;     ("Subgoal *1/5.13'''" :use (:instance kont-expand-crock (k (car klst))))
;     ("Subgoal *1/5.13.4" :use (:instance expr-expand-crock))
;     ("Subgoal *1/5.13.3" :by nil) ; remote
;     ("Subgoal *1/5.13.2" :by nil) ; fun
;     ("Subgoal *1/5.13.1" :by nil) ; local
    
;     ("Subgoal *1/5.12'''" :use (:instance kont-expand-crock (k (car klst))))
;     ("Subgoal *1/5.12.4" :use (:instance expr-expand-crock))
;     ("Subgoal *1/5.12.3" :by nil) ; remote
;     ("Subgoal *1/5.12.2" :by nil) ; fun
;     ("Subgoal *1/5.12.1" :by nil) ; local
    
;     ("Subgoal *1/5.3" :use (:instance kont-expand-crock (k (car klst))))
;     ("Subgoal *1/5.3.13" :use (:instance expr-expand-crock))
;     ("Subgoal *1/5.3.12'" :by nil) ; remote
;     ("Subgoal *1/5.3.8'" :by nil)  ; fun
;     ("Subgoal *1/5.3.3'" :by nil)  ; local
    
;     ("Subgoal *1/5.2'" :use (:instance kont-expand-crock (k (car klst))))
;     ("Subgoal *1/5.2.7" :use (:instance expr-expand-crock))
;     ("Subgoal *1/5.2.6''" :by nil) ; local?
;     ("Subgoal *1/5.2.5'" :by nil) ; remote 
;     ("Subgoal *1/5.2.4''" :by nil) ; fun
;     ("Subgoal *1/5.2.3'" :by nil) ; some call
;     ("Subgoal *1/5.2.2''" :by nil) ; some call
;     ("Subgoal *1/5.2.1'" :by nil) ; local call
    
;     ("Subgoal *1/5.1" :use (:instance kont-expand-crock (k (car klst))))
;     ("Subgoal *1/5.1.12" :use (:instance expr-expand-crock))
;     ("Subgoal *1/5.2.1'" :by nil)
;     ("Subgoal *1/5.1.12.11'" :by nil)


;     )
;   )



  ; :hints (
  ;    ("Subgoal *1/5.13'" :by nil) ;expct
  ;    ("Subgoal *1/5.12'" :by nil) ;reject
  ;    ("Subgoal *1/5.11'" :by nil) ;flimit
  ;    ("Subgoal *1/5.10''" :use (:instance kont-expand-crock (k (car klst))))
  ;    ("Subgoal *1/5.10.4" :use (:instance expr-expand-crock))
  ;    ("Subgoal *1/5.10.3" :by nil) ;remote-call
  ;    ("Subgoal *1/5.10.2" :by nil) ;fun-call
  ;    ("Subgoal *1/5.10.1" :by nil) ;local-call
  ;    ("Subgoal *1/5.9'''" :use (:instance kont-expand-crock (k (car klst))))
  ;    ("Subgoal *1/5.9.4" :use (:instance expr-expand-crock))
  ;    ("Subgoal *1/5.9.3" :by nil) ;remote-call
  ;    ("Subgoal *1/5.9.2" :by nil) ;fun-call
  ;    ("Subgoal *1/5.9.1" :by nil) ;local-call
  ;    ("Subgoal *1/5.7'''" :use (:instance kont-expand-crock (k (car klst))))
  ;    ("Subgoal *1/5.7.4" :use (:instance expr-expand-crock))
  ;    ("Subgoal *1/5.7.3" :by nil)
  ;    ("Subgoal *1/5.7.2" :by nil)
  ;    ("Subgoal *1/5.7.1" :by nil)
  ;    ("Subgoal *1/5.6" :use (:instance kont-expand-crock (k (car klst))))
  ;    ("Subgoal *1/5.6.4" :use (:instance expr-expand-crock))
  ;    ("Subgoal *1/5.6.3" :by nil)
  ;    ("Subgoal *1/5.6.2" :by nil)
  ;    ("Subgoal *1/5.6.1" :by nil)

  ;    ;; same as previous
  ;    ("Subgoal *1/5.5" :by nil)

  ;    ;; trivial
  ;    ("Subgoal *1/5.3'" :by nil)
  ;    )
  ; )


  ; :expand ((kont-kind (erl-k->kont (car klst)))) 
  ; :disable (apply-k-of-step apply-k-of-consp)
  ; :hints (("Subgoal *1/5.77"
  ;           :use (:instance expr-expand-crock))
  ;         ("Subgoal *1/5.74'" 
  ;           :use (:instance no-body-of-eval-remote-call-crock
  ;                  (s (update-erl-state->in s '(:none)))
  ;                  (m (kont-remote-call->module (erl-k->kont (car klst))))
  ;                  (c  (kont-remote-call->call (erl-k->kont (car klst))))
  ;                  (args (erl-val-cons->lst (erl-state->in s)))))
  ;         ("Subgoal *1/5.70'" 
  ;           :use (:instance no-body-of-eval-fun-call-crock
  ;                  (s (update-erl-state->in s '(:none)))
  ;                  (f (kont-fun-call->fun (erl-k->kont (car klst))))
  ;                  (args (erl-val-cons->lst (erl-state->in s)))))
  ;         ("Subgoal *1/5.67'" 
  ;           :use (:instance no-body-of-eval-local-call-crock
  ;                  (s (update-erl-state->in s '(:none)))
  ;                  (c  (kont-local-call->call (erl-k->kont (car klst))))
  ;                  (args (erl-val-cons->lst (erl-state->in s)))))
  ;         ("Subgoal *1/5.52''"
  ;           :use (:instance expr-expand-crock))
  ;         ("Subgoal *1/5.51'''"
  ;           :use (:instance expr-expand-crock))
  ;         ("Subgoal *1/5.49'''"
  ;           :use (:instance expr-expand-crock))
  ;         ("Subgoal *1/5.45''" 
  ;           :use (:instance no-body-of-eval-remote-call-crock
  ;                  (s (update-erl-state->in s '(:none)))
  ;                  (m (kont-remote-call->module (erl-k->kont (car klst))))
  ;                  (c  (kont-remote-call->call (erl-k->kont (car klst))))
  ;                  (args (erl-val-cons->lst (erl-state->in s)))))
  ;         ("Subgoal *1/5.42'''" 
  ;           :use (:instance no-body-of-eval-remote-call-crock
  ;                  (s (update-erl-state->in s '(:none)))
  ;                  (m (kont-remote-call->module (erl-k->kont (car klst))))
  ;                  (c  (kont-remote-call->call (erl-k->kont (car klst))))
  ;                  (args (erl-val-cons->lst (erl-state->in s)))))
  ;         ("Subgoal *1/5.37''" 
  ;           :use (:instance no-body-of-eval-fun-call-crock
  ;                  (s (update-erl-state->in s '(:none)))
  ;                  (f (kont-fun-call->fun (erl-k->kont (car klst))))
  ;                  (args (erl-val-cons->lst (erl-state->in s)))))
  ;         ("Subgoal *1/5.34'''" 
  ;           :use (:instance no-body-of-eval-fun-call-crock
  ;                  (s (update-erl-state->in s '(:none)))
  ;                  (f (kont-fun-call->fun (erl-k->kont (car klst))))
  ;                  (args (erl-val-cons->lst (erl-state->in s)))))
  ;         ("Subgoal *1/5.30'" 
  ;           :use (:instance no-body-of-eval-local-call-crock
  ;                  (s (update-erl-state->in s '(:none)))
  ;                  (c  (kont-local-call->call (erl-k->kont (car klst))))
  ;                  (args (erl-val-cons->lst (erl-state->in s)))))
  ;         ("Subgoal *1/5.27'''" 
  ;           :use (:instance no-body-of-eval-local-call-crock
  ;                  (s (update-erl-state->in s '(:none)))
  ;                  (c  (kont-local-call->call (erl-k->kont (car klst))))
  ;                  (args (erl-val-cons->lst (erl-state->in s)))))
  ;         ("Subgoal *1/5.25'"
  ;           :use (:instance expr-expand-crock))
  ;         ("Subgoal *1/5.25.10"
  ;           :use (:instance apply-k-of-pair
  ;                  (s (update-erl-state->in s '(:none)))
  ;                  (k1 (erl-k
  ;                         (+ -1 (erl-k->fuel (car klst)))
  ;                         (kont-expr
  ;                             (node-match->rhs (kont-expr->expr (erl-k->kont (car klst)))))))
  ;                  (k2
  ;                   (erl-k
  ;                       (+ -1 (erl-k->fuel (car klst)))
  ;                       (kont-match
  ;                             (node-match->lhs (kont-expr->expr (erl-k->kont (car klst)))))))))
  ;         ))