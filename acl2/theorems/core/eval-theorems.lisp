(in-package "ACL2")
(include-book "../../erl-eval")

(set-induction-depth-limit 1)

; apply-k Rules ----------------------------------------------------------------

(encapsulate nil
  (local (in-theory (enable apply-k)))

  (defrule apply-k-of-nil
    (implies (erl-state-p s)
            (equal (apply-k s nil) s)))
  
  (defrule apply-k-of-flimit
    (implies (and (erl-state-p s)
                  (equal (erl-val-kind (erl-state->in s)) :flimit))
            (equal (apply-k s klst) s)))
  
  (defrule apply-k-of-reject
    (implies 
      (and (erl-state-p s) 
           (equal (erl-val-kind (erl-state->in s)) :reject))
      (equal (apply-k s klst) s)))
  
  (defrule apply-k-of-excpt
    (implies 
      (and (erl-state-p s) 
           (equal (erl-val-kind (erl-state->in s)) :excpt))
      (equal (apply-k s klst) s))))


; evak-k Rules -----------------------------------------------------------------

(encapsulate nil
  (local (in-theory (enable eval-k)))

  (defrule eval-k-of-flimit
    (implies 
      (and (erl-state-p s) 
           (equal (erl-val-kind (erl-state->in s)) :flimit))
      (equal (erl-s-klst->s (eval-k k s)) s)))

  (defrule eval-k-of-reject
    (implies 
      (and (erl-state-p s) 
           (equal (erl-val-kind (erl-state->in s)) :reject))
      (equal (erl-s-klst->s (eval-k k s)) s)))

  (defrule eval-k-of-excpt
    (implies
      (and (erl-state-p s) 
           (equal (erl-val-kind (erl-state->in s)) :excpt))
      (equal (erl-s-klst->s (eval-k k s)) s))))


; Stepping Rules ---------------------------------------------------------------

; Stepping rules for apply-k
; Remark: This theorem is only used in :use hints, so it is disabled.
(defruled apply-k-of-append
  (implies
    (and (erl-klst-p klst1)
         (erl-klst-p klst2)
         (erl-state-p s)
         (equal klst (append klst1 klst2)))
    (equal
      (apply-k s klst)
      (apply-k (apply-k s klst1) klst2)))
  :enable apply-k)

; Given a list continuations, evaluate the first in isolation.
(defrule apply-k-of-consp
  (implies 
    (and (erl-klst-p klst)
         (erl-state-p s)
         (consp klst))
    (equal (apply-k s klst)
           (apply-k (apply-k s (list (car klst))) (cdr klst))))
  :use (:instance apply-k-of-append
        (s s)
        (klst1 (list (car klst)))
        (klst2 (cdr klst))
        (klst klst)))

; Expand apply-k once, given a single continuation.
(defrule apply-k-of-step
  (implies 
    (and (erl-k-p k) (erl-state-p s))  
    (equal (apply-k s (cons k nil))
           (apply-k
            (erl-s-klst->s (eval-k k s))
            (erl-s-klst->klst (eval-k k s)))))
  :expand (apply-k s (cons k nil))
  :disable apply-k-of-consp)
