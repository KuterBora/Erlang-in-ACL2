(in-package "ACL2")
(include-book "../core/top")

(set-induction-depth-limit 1)

; Erl-State Module Theorems ----------------------------------------------------

; The theorems below reason about what happens to the module field of an
; erl-state after various operations.

(defrule erl-state->module-of-eval-match
  (equal (erl-state->module (eval-match p s))
         (erl-state->module s))
  :enable eval-match)

(defrule erl-state->module-of-match-args
  (equal (erl-state->module (match-args cs args s))
         (erl-state->module s))
  :enable match-args)

(defrule erl-state->module-of-eval-clauses-when-consp
  (equal (erl-state->module (mv-nth 0 (eval-clauses-when-consp args cls s)))
         (erl-state->module s))
  :enable eval-clauses-when-consp)

(defrule erl-state->module-of-eval-clauses
  (equal (erl-state->module (mv-nth 0 (eval-clauses args cls s)))
         (erl-state->module s))
  :enable eval-clauses)

(defrule eval-k-of-module
  (implies 
    (equal (kont-kind (erl-k->kont k)) :expr)
    (equal (erl-state->module (erl-s-klst->s (eval-k k s)))
           (erl-state->module s)))
  :enable eval-k)


(defrule eval-k-of-module-general
  (implies 
    (not (or (equal (kont-kind (erl-k->kont k)) :local-call)
             (equal (kont-kind (erl-k->kont k)) :remote-call)
             (equal (kont-kind (erl-k->kont k)) :fun-call)
             (equal (kont-kind (erl-k->kont k)) :function-return)))
    (equal (erl-state->module (erl-s-klst->s (eval-k k s)))
           (erl-state->module s)))
  :enable eval-k)

; (defrule eval-k-of-module-cons-merge
;   (implies 
;     (equal (kont-kind (erl-k->kont k)) :cons-merge)
;     (equal (erl-state->module (erl-s-klst->s (eval-k k s)))
;            (erl-state->module s)))
;   :enable eval-k)

(defrule apply-k-of-cons-merge
  (implies 
    (equal (kont-kind (erl-k->kont k)) :cons-merge)
    (equal (erl-state->module (apply-k s (list k)))
           (erl-state->module s)))
  :expand (apply-k s (list k))
  :enable eval-k)

(defrule apply-k-of-module-general
  (implies 
    (not (or (equal (kont-kind (erl-k->kont k)) :expr)
             (equal (kont-kind (erl-k->kont k)) :exprs)
             (equal (kont-kind (erl-k->kont k)) :cons)
             (equal (kont-kind (erl-k->kont k)) :case-of)
             (equal (kont-kind (erl-k->kont k)) :binop-expr1)
             (equal (kont-kind (erl-k->kont k)) :local-call)
             (equal (kont-kind (erl-k->kont k)) :remote-call)
             (equal (kont-kind (erl-k->kont k)) :fun-call)
             (equal (kont-kind (erl-k->kont k)) :fun-call-args)
             (equal (kont-kind (erl-k->kont k)) :function-return)))
    (equal (erl-state->module (apply-k s (list k)))
           (erl-state->module s)))
  :expand (apply-k s (list k))
  :enable eval-k)



; (define k-induct (s k)
;   (let ((x (kont-expr-> (erl-k->kont k))))
;         (node-case x

;   )



(defrule attempt
  (implies
    (and (wf-state-p (apply-k s (list k1 k2)))
         (equal (kont-kind (erl-k->kont k2)) :function-return))
    (equal (erl-state->module (apply-k s (list k1 k2)))
           (kont-function-return->module (erl-k->kont k2))))
  :expand (:free (x) (apply-k x (list k2)))
  :enable eval-k)

(defrule attempt-2
  (implies
    (and (wf-state-p (apply-k s (list k)))
         (equal (kont-kind (erl-k->kont k)) :function-return))
    (equal (erl-state->module (apply-k s (list k)))
           (kont-function-return->module (erl-k->kont k))))
  :expand (:free (x) (apply-k x (list k)))
  :enable eval-k)


;;; SOME LEMMAS


;; TODO: make this disabled? or maybe forward chaining
(defrule wf-state-implies-next-wf-state
  (implies (and (consp klst) (wf-state-p (apply-k s klst)))
           (wf-state-p (apply-k (erl-s-klst->s (eval-k (car klst) s))
                                (erl-s-klst->klst (eval-k (car klst) s)))))
  :expand (apply-k s klst)
  :enable apply-k-of-append
  :rule-classes :forward-chaining)

(defrule wf-state-implies-next-wf-state-2
  (implies (and (consp klst) (wf-state-p (apply-k s klst)) (null (erl-s-klst->klst (eval-k (car klst) s))))
           (wf-state-p (apply-k (erl-s-klst->s (eval-k (car klst) s)) (cdr klst))))
  :expand (apply-k s klst)
  :enable apply-k-of-append
  :rule-classes :forward-chaining)

(defrule wf-state-implies-next-wf-state-3
  (implies (and (consp klst) (wf-state-p (apply-k s klst)))
           (wf-state-p (apply-k (apply-k (erl-s-klst->s (eval-k (car klst) s))
                                         (erl-s-klst->klst (eval-k (car klst) s)))
                                (cdr klst))))
  :expand (apply-k s klst)
  :enable apply-k-of-append
  :rule-classes :forward-chaining)

; (defruled step-it-please
;   (implies (and (consp klst) (wf-state-p (apply-k s klst)))
;            (equal (apply-k s klst)
;                   (apply-k (apply-k (erl-s-klst->s (eval-k (car klst) s))
;                                          (erl-s-klst->klst (eval-k (car klst) s)))
;                                 (cdr klst))))
;   :expand (apply-k s klst)
;   :enable apply-k-of-append)

(defrule eval-k-that-return-null-klst
  (implies (and (not (erl-s-klst->klst (eval-k k s)))
                (not (equal (kont-kind (erl-k->kont k)) :function-return))
                (wf-state-p (erl-s-klst->s (eval-k k s))))
           (equal (erl-state->module (erl-s-klst->s (eval-k k s)))
                  (erl-state->module s)))
  :enable (eval-k eval-remote-call eval-local-call eval-fun-call))



(include call-stuff)

(defrule eval-k-does-not-return-function-call-first-0
 (implies 
  (erl-s-klst->klst (eval-k k s))
  (or (equal (kont-kind (erl-k->kont (car (erl-s-klst->klst (eval-k k s))))) :expr)
      (equal (kont-kind (erl-k->kont (car (erl-s-klst->klst (eval-k k s))))) :exprs)))
  :enable eval-k)

(defrule fuel-of-1-is-not-enough
  (implies
    (and (EQUAL (ERL-K->FUEL (CAR KLST)) 1)
         (CONSP KLST)
         (ERL-S-KLST->KLST (EVAL-K (CAR KLST) S)))
    (not (wf-state-p (apply-k s klst))))
  :enable apply-k)

; keeping this around
; (defrule attempt-2
;   (implies
;     (and (wf-state-p (apply-k s (list k)))
;          (equal (kont-kind (erl-k->kont k)) :function-return))
;     (equal (erl-state->module (apply-k s (list k)))
;            (kont-function-return->module (erl-k->kont k))))
;   :expand (:free (x) (apply-k x (list k)))
;   :enable eval-k)

(defrule module-of-kont-call
  (implies
    (and
      (consp klst)
      (erl-s-klst->klst (eval-k (car klst) s))
      (or (equal (kont-kind (erl-k->kont (car klst))) :local-call)
          (equal (kont-kind (erl-k->kont (car klst))) :remote-call)
          (equal (kont-kind (erl-k->kont (car klst))) :fun-call))
      
      (wf-state-p (apply-k s klst)))

    (equal (erl-state->module
             (apply-k (erl-s-klst->s (eval-k (car klst) s))
                      (erl-s-klst->klst (eval-k (car klst) s))))
            (erl-state->module s)))
    :expand ((eval-k (car klst) s))
    :disable wf-state-implies-next-wf-state
    :use ((:instance wf-state-implies-next-wf-state)))



;;;; HELPER

(defun no-return (klst)
  (if (consp klst)
      (and
        (not (equal (kont-kind (erl-k->kont (car klst))) :function-return))
        (no-return (cdr klst)))
      t))

; (defrule no-return-help
;   (implies (no-return klst)
;            (not (equal (kont-kind (erl-k->kont (car klst))) :function-return))))

(defrule append-of-no-return
  (implies (and (no-return l1) (no-return l2)) (no-return (append l1 l2))))

(defrule expr-causes-no-return
  (implies 
    (and (consp klst)
         (equal (kont-kind (erl-k->kont (car klst))) :expr)
         (no-return klst))
    (no-return (erl-s-klst->klst (eval-k (car klst) s))))
  :enable eval-k)
; (defrule exprs-causes-no-return
;   (implies 
;     (and (consp klst)
;          (equal (kont-kind (erl-k->kont (car klst))) :exprs)
;          (no-return klst))
;     (no-return (erl-s-klst->klst (eval-k (car klst) s))))
;   :enable eval-k)

(defrule no-return-of-kind
  (implies 
    (and (consp klst)
         (not (or (equal (kont-kind (erl-k->kont (car klst))) :local-call)
                  (equal (kont-kind (erl-k->kont (car klst))) :remote-call)
                  (equal (kont-kind (erl-k->kont (car klst))) :fun-call)))
         (no-return klst))
    (no-return (erl-s-klst->klst (eval-k (car klst) s))))
  :enable eval-k)



;;;;; HELPER DONE



;;;; TERMINATION
(defrule termination-lemma-1a
  (> (expt 3 x) 0))

(defrule termination-lemma-1b
  (implies (natp a) (> (+ a (expt 3 x)) 0))
  :use (:instance termination-lemma-1a))

(defrule termination-lemma-1
  (implies (consp klst) (< (klst-measure nil) (klst-measure klst)))
  :enable klst-measure
  :use (:instance termination-lemma-1a))

(defrule termination-lemma-2
  (implies (consp klst) (< 0 (klst-measure klst)))
  :enable klst-measure
  :use (:instance termination-lemma-1a))

(defrule termination-lemma-3
  (implies (consp klst) 
           (< (klst-measure (cdr klst)) (klst-measure klst))))

(include-book "arithmetic/top" :dir :system)

(defrule termination-lemma-4
  (implies (and (natp a) (natp b) (natp c) (< (+ a b) c))  (< a c)))

(defrule dum (natp (klst-measure klst)))

(defrule termination-lemma-5
  (implies (and (consp klst) (natp a)
                      (< (+ a (klst-measure (cdr klst))) (klst-measure klst)))
           (< a (klst-measure klst)))
  :use (:instance termination-lemma-4 (a a) (b (klst-measure (cdr klst))) (c (klst-measure klst))))

(defrule termination-lemma-6
  (implies
    (and (consp klst) (consp (cdr klst)))
    (< (klst-measure (list (car klst))) (klst-measure klst)))
  :enable klst-measure)

(defrule termination-lemma-7
  (implies
    (and (natp a) (natp b) (natp c))  
      (< a (+  b (expt 3 c) a))))

; (defrule termination-lemma-8
;   (implies
;     (and (consp klst) (consp (cdr klst)))
;     (< (klst-measure (list (cadr klst))) (klst-measure klst)))
;   :expand ((klst-measure klst) (KLST-MEASURE (list (CADR KLST))) (KLST-MEASURE (CDR KLST)))
;   :use (:instance termination-lemma-7
;         (a (EXPT 3 (ERL-K->FUEL (CADR KLST))))
;         (b (KLST-MEASURE (CDDR KLST)))
;         (c (ERL-K->FUEL (CAR KLST)))
;         ))


(defrule termination-lemma-9
  (implies
    (and (consp klst) (consp (cdr klst)))
    (< (klst-measure (append (ERL-S-KLST->KLST (EVAL-K (CAR KLST) S)) 
                             (cdr klst)))
       (klst-measure klst)))
  :use (:instance eval-k-decreases-klst-measure (k (car klst)) (s s) (kl (cdr klst))))

(defrule termination-lemma-new
  (implies
    (and (posp a) (posp b) (posp c) (< (+ b c a) d)) 
      (< a d)))

(defrule positive-please
  (implies (>= x 0) (posp (expt 3 x))))

; (defrule positive-please
;   (implies (= x 0) (posp (expt 3 x))))


(defrule termination-lemma-10
  (implies
    (and (consp klst) (ERL-S-KLST->KLST (EVAL-K (CAR KLST) S)) (> (erl-k->fuel (car klst)) 0))
    
    (< (klst-measure (list (cadr (ERL-S-KLST->KLST (EVAL-K (CAR KLST) S)))))
       (klst-measure klst)))

  :disable (termination-lemma-9 )
  :expand ((KLST-MEASURE (CDR (ERL-S-KLST->KLST (EVAL-K (CAR KLST) S))))
           (KLST-MEASURE (LIST (CADR (ERL-S-KLST->KLST (EVAL-K (CAR KLST) S)))))
           (KLST-MEASURE (ERL-S-KLST->KLST (EVAL-K (CAR KLST) S))))
  :use ((:instance termination-lemma-9)
        (:instance termination-lemma-new
          (a (EXPT 3 (+ -1 (ERL-K->FUEL (CAR KLST)))))
          (b (KLST-MEASURE (CDR KLST)))
          (c (EXPT 3 (+ -1 (ERL-K->FUEL (CAR KLST)))))
          (d (KLST-MEASURE KLST)))
        )
  :hints (
          ("Subgoal 2" :expand (klst-measure klst))
          ("Subgoal 1" :expand (klst-measure klst))))

(defrule termination-and-more
  (implies (ERL-S-KLST->KLST (EVAL-K (CAR KLST) S))
          (consp (cdr (ERL-S-KLST->KLST (EVAL-K (CAR KLST) S)))))
  :enable eval-k)



;;;; TERMINATION END

; rename to return induct or something
(define expr-induct (s klst)
  :measure (klst-measure klst)
  :verify-guards nil
  :enabled t
  (if (endp klst)
      t
      (b* ((k (car klst))
           (ks (eval-k k s))
           (r (erl-s-klst->s ks))
           (rklst (erl-s-klst->klst ks))
           ((if (null rklst)) (expr-induct r (cdr klst)))
           (rk1 (car rklst))
           (kont (erl-k->kont k))
           ((if (not (> (erl-k->fuel rk1) 0))) t))
          ; (expr-induct r rklst)
          (kont-case kont
            (:expr (expr-induct r (append rklst (cdr klst))))
            (:exprs (expr-induct r (append rklst (cdr klst))))
            (:cons (expr-induct r (append rklst (cdr klst))))
            (:cons-merge (expr-induct r (append rklst (cdr klst))))
            (:tuple (expr-induct r (append rklst (cdr klst))))
            (:unop (expr-induct r (append rklst (cdr klst))))
            (:binop-expr1 (expr-induct r (append rklst (cdr klst))))
            (:binop-expr2 (expr-induct r (append rklst (cdr klst))))
            (:match (expr-induct r (append rklst (cdr klst))))
            (:case-of (expr-induct r (append rklst (cdr klst))))

            (:local-call (expr-induct (apply-k r rklst) (cdr klst)))

            (:remote-call  (expr-induct (apply-k r rklst) (cdr klst)))
            (:fun-call-args (expr-induct r (append rklst (cdr klst))))
            (:fun-call  (expr-induct (apply-k r rklst) (cdr klst)))
            (:function-return t))))
  
  ; for termination proof
  :hints (("Goal" :in-theory (disable eval-k-decreases-klst-measure)
                  :use ((:instance eval-k-decreases-klst-measure
                          (k (car klst)) (kl (cdr klst)))))
          ("Subgoal 2" 
            :in-theory (disable termination-and-more LEN-OF-EVAL-K->KLST termination-lemma-6)
            :use ((:instance termination-and-more (s s) (klst klst))
                  (:instance termination-lemma-6 
                    (klst (ERL-S-KLST->KLST (EVAL-K (CAR KLST) S))))))
          ("Subgoal 1"
            :expand
              ((KLST-MEASURE (CONS (CADR (ERL-S-KLST->KLST (EVAL-K (CAR KLST) S)))
                        (CDR KLST)))
                (klst-measure klst)))
          ))


; 42912 steps


(defrule apply-k-of-module
  (implies
    (and (no-return klst) (wf-state-p (apply-k s klst)))
    (equal (erl-state->module (apply-k s klst))
           (erl-state->module s)))
  :induct (expr-induct s klst)


  :hints (("Subgoal *1/20" 
            :in-theory (disable eval-k-does-not-return-function-call-first-0)
            :use (:instance eval-k-does-not-return-function-call-first-0 (s s) (k (car klst))))
          
          ("Subgoal *1/19" :expand ((apply-k s klst)))
          ("Subgoal *1/18" :expand ((apply-k s klst)))
          
          ("Subgoal *1/17"
            :expand ((apply-k s klst))
            :in-theory (enable apply-k-of-append))
          
          ("Subgoal *1/16" :expand ((apply-k s klst)))
          
          ("Subgoal *1/15"
            :expand ((apply-k s klst))
            :in-theory (enable apply-k-of-append))

          ("Subgoal *1/14"
            :expand ((apply-k s klst))
            :in-theory (enable apply-k-of-append))

          
          ; solved by no-return-of-kind
          ("Subgoal *1/13" :expand ((apply-k s klst)))
          ("Subgoal *1/12" :expand ((apply-k s klst)))
          ("Subgoal *1/11" :expand ((apply-k s klst)))
          ("Subgoal *1/10'" :expand ((apply-k s klst)))
          ("Subgoal *1/9" :expand ((apply-k s klst)))
          ("Subgoal *1/8'" :expand ((apply-k s klst)))
          ("Subgoal *1/7" :expand ((apply-k s klst)))
          ("Subgoal *1/6" :expand ((apply-k s klst)))
          ("Subgoal *1/5" :expand ((apply-k s klst)))
          ("Subgoal *1/4" :expand ((apply-k s klst)))

          ; ("Subgoal *1/3''" ) solved by lemma: fuel-of-1-is-not-enough

          ("Subgoal *1/2''" :expand ((apply-k s klst)))))



(defrule apply-k-of-module-1
  (implies 
    (and (wf-state-p (apply-k s (cons k nil)))
         (not (equal (kont-kind (erl-k->kont k)) :function-return)))
    (equal (erl-state->module (apply-k s (cons k nil)))
           (erl-state->module s)))
  :use (:instance apply-k-of-module (s s) (klst (cons k nil))))

; IDEA:

; what if, eval-k ignores error conditions? Then, stepping does not require wf-state-p


; disable apply-k of step
; rules for stepping apply-k directly
; define induction