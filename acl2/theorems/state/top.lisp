(in-package "ACL2")

(include-book "world")
(include-book "module")




(defruled some-rule-1
  (implies
    (and (equal (erl-state->module s1) (erl-state->module s2))
         (equal (erl-state->bind s1) (erl-state->bind s2))
         (equal (erl-state->world s1) (erl-state->world s2)))
    (equal (update-erl-state->in s1 v) (update-erl-state->in s2 v)))
  :enable update-erl-state->in)

(defruled some-rule
  (implies
    (and (wf-state-p s1)
         (wf-state-p s2)
         (equal (erl-state->module s1) (erl-state->module s2))
         (equal (erl-state->bind s1) (erl-state->bind s2))
         (equal (erl-state->world s1) (erl-state->world s2))
         (equal (kont-kind (erl-k->kont k)) :expr))
      
    (equal (erl-state->in (apply-k s1 (cons k nil)))
           (erl-state->in (apply-k s2 (cons k nil)))))
  :expand
    ((apply-k s1 (cons k nil))
     (apply-k s2 (cons k nil))
     (eval-k k s1)
     (eval-k k s2))
  :use ((:instance some-rule-1 (s1 s1) (s2 s2) (v '(:none)))
        (:instance some-rule-1 (s1 s1) (s2 s2) (v (make-erl-val-excpt  :err (make-erl-err :class (make-err-class-error) :reason (make-exit-reason-if-clause)))))))


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
           (rkont (erl-k->kont rk1))
           ;(rk2 (cadr rklst))
           ((if (not (> (erl-k->fuel rk1) 0))) t))
          ; (expr-induct r rklst)
          (kont-case rkont
            (:expr
               ; (and
              ;   ; (expr-induct s (list rk1))
              ;   ; (expr-induct (apply-k s (list rk1)) (cons rk2 (cdr klst)))
              ;   ; (expr-induct (apply-k (apply-k r (list rk1)) (list rk2)) (cdr klst))
              ;   ; (expr-induct (apply-k r (list rk1)) (append (list rk1) (cdr klst)))
              ;   (expr-induct r (append rklst (cdr klst)))))
            (:exprs t
              ; (and
              ;   ; (expr-induct s (list rk1))
              ;   ; (expr-induct (apply-k s (list rk1)) (cons rk2 (cdr klst)))
              ;   ; (expr-induct (apply-k (apply-k r (list rk1)) (list rk2)) (cdr klst))
              ;   ; (expr-induct (apply-k r (list rk1)) (append (list rk1) (cdr klst)))
              ;   (expr-induct r (append rklst (cdr klst))))
                
                )
            (:cons t)
            (:cons-merge t)
            (:tuple t)
            (:unop t)
            (:binop-expr1 t)
            (:binop-expr2 t)
            (:match t)
            (:case-of (expr-induct (apply-k r rklst) (cdr klst)))
            (:local-call t)
            (:remote-call t)
            (:fun-call-args t)
            (:fun-call t)
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




;;;;; SOME CALL STUFF



(defrule local-call-crock
  (implies
    (and (not (mv-nth 1 (eval-local-call s c args)))
         (wf-state-p (mv-nth 0 (eval-local-call s c args))))
    (equal (erl-state->module s)
           (erl-state->module (mv-nth 0 (eval-local-call s c args)))))
  :enable (eval-local-call))

(defrule apply-k-of-local-call-wf
  (implies (and (equal (kont-kind (erl-k->kont (car klst))) :local-call)
                (not (MV-NTH 1
                        (EVAL-LOCAL-CALL (UPDATE-ERL-STATE->IN S '(:NONE))
                                        (KONT-LOCAL-CALL->CALL (ERL-K->KONT (CAR KLST)))
                                        (ERL-VAL-CONS->LST (ERL-STATE->IN S)))))
                (wf-state-p (apply-k s klst)))
           (wf-state-p
            (MV-NTH 0
              (EVAL-LOCAL-CALL (UPDATE-ERL-STATE->IN S '(:NONE))
                               (KONT-LOCAL-CALL->CALL (ERL-K->KONT (CAR KLST)))
                               (ERL-VAL-CONS->LST (ERL-STATE->IN S))))))
  :expand (apply-k s klst)
  :enable (eval-k))

(defrule apply-k-of-local-call-wf1
  (implies (and (equal (kont-kind (erl-k->kont (car klst))) :local-call)
                (not (MV-NTH 1
                        (EVAL-LOCAL-CALL (UPDATE-ERL-STATE->IN S '(:NONE))
                                        (KONT-LOCAL-CALL->CALL (ERL-K->KONT (CAR KLST)))
                                        (ERL-VAL-CONS->LST (ERL-STATE->IN S)))))
                (wf-state-p (apply-k s klst)))
           (equal
            (erl-state->module (MV-NTH 0
                    (EVAL-LOCAL-CALL (UPDATE-ERL-STATE->IN S '(:NONE))
                                    (KONT-LOCAL-CALL->CALL (ERL-K->KONT (CAR KLST)))
                                    (ERL-VAL-CONS->LST (ERL-STATE->IN S)))))
            (erl-state->module s)))
  :disable apply-k-of-local-call-wf
  :use ((:instance apply-k-of-local-call-wf)
        (:instance local-call-crock
          (s (UPDATE-ERL-STATE->IN S '(:NONE)))
          (c (KONT-LOCAL-CALL->CALL (ERL-K->KONT (CAR KLST))))
          (args (ERL-VAL-CONS->LST (ERL-STATE->IN S)))
          )))

(defrule remote-call-crock
  (implies
    (and (not (mv-nth 1 (eval-remote-call s m c args)))
         (wf-state-p (mv-nth 0 (eval-remote-call s m c args))))
    (equal (erl-state->module s)
           (erl-state->module (mv-nth 0 (eval-remote-call s m c args)))))
  :enable (eval-remote-call))

(defrule apply-k-of-remote-call-wf
  (implies (and (equal (kont-kind (erl-k->kont (car klst))) :remote-call)
                (not (MV-NTH 1
                        (EVAL-remote-CALL (UPDATE-ERL-STATE->IN S '(:NONE))
                                        (KONT-REMOTE-CALL->MODULE (ERL-K->KONT (CAR KLST)))
                                        (KONT-remote-CALL->CALL (ERL-K->KONT (CAR KLST)))
                                        (ERL-VAL-CONS->LST (ERL-STATE->IN S)))))
                (wf-state-p (apply-k s klst)))
           (wf-state-p
            (MV-NTH 0
              (EVAL-remote-CALL (UPDATE-ERL-STATE->IN S '(:NONE))
                                (KONT-REMOTE-CALL->MODULE (ERL-K->KONT (CAR KLST)))
                               (KONT-remote-CALL->CALL (ERL-K->KONT (CAR KLST)))
                               (ERL-VAL-CONS->LST (ERL-STATE->IN S))))))
  :expand (apply-k s klst)
  :enable (eval-k))

(defrule apply-k-of-remote-call-wf1
  (implies (and (equal (kont-kind (erl-k->kont (car klst))) :remote-call)
                (not (MV-NTH 1
                        (EVAL-remote-CALL (UPDATE-ERL-STATE->IN S '(:NONE))
                                        (KONT-REMOTE-CALL->MODULE (ERL-K->KONT (CAR KLST)))
                                        (KONT-remote-CALL->CALL (ERL-K->KONT (CAR KLST)))
                                        (ERL-VAL-CONS->LST (ERL-STATE->IN S)))))
                (wf-state-p (apply-k s klst)))
           (equal
            (erl-state->module (MV-NTH 0
                    (EVAL-remote-CALL (UPDATE-ERL-STATE->IN S '(:NONE))
                                    (KONT-REMOTE-CALL->MODULE (ERL-K->KONT (CAR KLST)))
                                    (KONT-remote-CALL->CALL (ERL-K->KONT (CAR KLST)))
                                    (ERL-VAL-CONS->LST (ERL-STATE->IN S)))))
            (erl-state->module s)))
  :disable apply-k-of-remote-call-wf
  :use ((:instance apply-k-of-remote-call-wf)
        (:instance remote-call-crock
          (s (UPDATE-ERL-STATE->IN S '(:NONE)))
          (m (KONT-REMOTE-CALL->MODULE (ERL-K->KONT (CAR KLST))))
          (c (KONT-remote-CALL->CALL (ERL-K->KONT (CAR KLST))))
          (args (ERL-VAL-CONS->LST (ERL-STATE->IN S)))
          )))




(defrule fun-call-crock
  (implies
    (and (not (mv-nth 1 (eval-fun-call s c args)))
         (wf-state-p (mv-nth 0 (eval-fun-call s c args))))
    (equal (erl-state->module s)
           (erl-state->module (mv-nth 0 (eval-fun-call s c args)))))
  :enable (eval-fun-call))

(defrule apply-k-of-fun-call-wf
  (implies (and (equal (kont-kind (erl-k->kont (car klst))) :fun-call)
                (not (MV-NTH 1
                        (EVAL-fun-CALL (UPDATE-ERL-STATE->IN S '(:NONE))
                                        (KONT-fun-CALL->FUN (ERL-K->KONT (CAR KLST)))
                                        (ERL-VAL-CONS->LST (ERL-STATE->IN S)))))
                (wf-state-p (apply-k s klst)))
           (wf-state-p
            (MV-NTH 0
              (EVAL-fun-CALL (UPDATE-ERL-STATE->IN S '(:NONE))
                               (KONT-fun-CALL->FUN (ERL-K->KONT (CAR KLST)))
                               (ERL-VAL-CONS->LST (ERL-STATE->IN S))))))
  :expand (apply-k s klst)
  :enable (eval-k))

(defrule apply-k-of-fun-call-wf1
  (implies (and (equal (kont-kind (erl-k->kont (car klst))) :fun-call)
                (not (MV-NTH 1
                        (EVAL-fun-CALL (UPDATE-ERL-STATE->IN S '(:NONE))
                                        (KONT-fun-CALL->FUN (ERL-K->KONT (CAR KLST)))
                                        (ERL-VAL-CONS->LST (ERL-STATE->IN S)))))
                (wf-state-p (apply-k s klst)))
           (equal
            (erl-state->module (MV-NTH 0
                    (EVAL-fun-CALL (UPDATE-ERL-STATE->IN S '(:NONE))
                                    (KONT-fun-CALL->fun (ERL-K->KONT (CAR KLST)))
                                    (ERL-VAL-CONS->LST (ERL-STATE->IN S)))))
            (erl-state->module s)))
  :disable apply-k-of-fun-call-wf
  :use ((:instance apply-k-of-fun-call-wf)
        (:instance fun-call-crock
          (s (UPDATE-ERL-STATE->IN S '(:NONE)))
          (c (KONT-fun-CALL->fun (ERL-K->KONT (CAR KLST))))
          (args (ERL-VAL-CONS->LST (ERL-STATE->IN S)))
          )))