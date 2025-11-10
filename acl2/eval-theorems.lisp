(in-package "ACL2")
(include-book "erl-eval")

(set-induction-depth-limit 1)

; Core Theorems of the Evaluator -----------------------------------------------

; Applying a concatenated continuation list equals applying each sublist in sequence.
(defrule apply-k-of-append
  (implies
    (and (erl-klst-p klst1)
         (erl-klst-p klst2)
         (erl-state-p s)
         (equal klst (append klst1 klst2)))
    (equal
      (apply-k s klst)
      (apply-k (apply-k s klst1) klst2)))
  :in-theory (enable apply-k))

; When no continuations are left, apply-k returns the state
(defrule apply-k-of-nil
  (implies (erl-state-p s)
           (equal (apply-k s nil) s))
  :enable apply-k)

; If the state is flimit, apply-k terminates and returns the state.
(defrule apply-k-of-flimit
  (implies (and (erl-state-p s) (erl-klst-p klst)
                (equal (erl-val-kind (erl-state->in s)) :flimit))
           (equal (apply-k s klst) s))
  :enable apply-k)

; If apply-k did not return flimit, then s was not an flimit either.
(defrule apply-k-of-not-flimit
  (implies (and (erl-state-p s) (erl-klst-p klst)
                (not (equal (erl-val-kind (erl-state->in (apply-k s klst))) :flimit)))
           (not (equal (erl-val-kind (erl-state->in s)) :flimit)))
  :enable apply-k)

; If the state is rejected, apply-k terminates and returns the state.
(defrule apply-k-of-reject
  (implies (and (erl-state-p s) (erl-klst-p klst)
                (equal (erl-val-kind (erl-state->in s)) :reject))
           (equal (apply-k s klst) s))
  :enable apply-k)

; If apply-k did not get rejected, then s was not rejected either.
(defrule apply-k-of-not-reject
  (implies (and (erl-state-p s) (erl-klst-p klst)
                (not (equal (erl-val-kind (erl-state->in (apply-k s klst))) :reject)))
           (not (equal (erl-val-kind (erl-state->in s)) :reject)))
  :enable apply-k)

; If the state is excpt, and the exception is not caught, 
; apply-k terminates and returns the state.
(defrule apply-k-of-excpt
  (implies (and (erl-state-p s) (erl-klst-p klst)
                (equal (erl-val-kind (erl-state->in s)) :excpt))
           (equal (apply-k s klst) s))
  :enable apply-k)

; If apply-k did not return excpt, then s was not an excpt either,
; or the exception was caught.
(defrule apply-k-of-not-excpt
  (implies (and (erl-state-p s) (erl-klst-p klst)
                (not (equal (erl-val-kind (erl-state->in (apply-k s klst))) :excpt)))
           (not (equal (erl-val-kind (erl-state->in s)) :excpt)))
  :enable apply-k)


; Fuel Theorems ----------------------------------------------------------------

; The following theorems show that if evaluating a value and klst terminates
; without fault, then increasing the fuel of the continuations will not change the result.
; It is easier, and more elegant, for ACL2 to prove this for the more general case where 
; each k in the klst is given more fuel, rather than, for example, increasing the fuel of
; only the first k. This is why increase-fuel and the corresponding theorems are defined.

; Increase the fuel of each continuation in klst by n.
(define increase-fuel ((klst erl-klst-p) (n natp))
  :measure (len klst)
  :returns (ks erl-klst-p)
  (b* ((klst (erl-klst-fix klst))
       (n (nfix n))
       ((if (endp klst)) nil))
      (cons (make-erl-k :kont (erl-k->kont (car klst))
                        :fuel (+ n (erl-k->fuel (car klst))))
            (increase-fuel (cdr klst) n))))

; increase-fuel is distributive over append
(defrule increase-fuel-is-distributive-over-append
  (implies
    (and (erl-state-p s)
         (erl-klst-p rest)
         (erl-k-p k)
         (natp n)
         (not (equal (erl-val-kind (erl-state->in (erl-s-klst->s (eval-k k s)))) :flimit)))
    (equal (increase-fuel (append (erl-s-klst->klst (eval-k k s)) rest) n)
           (append (erl-s-klst->klst (eval-k (erl-k (+ n (erl-k->fuel k))
                                                    (erl-k->kont k))
                                             s))
                   (increase-fuel rest n))))
  :in-theory (enable increase-fuel eval-k))

; A continuation that did not cause an error in eval-k will produce the same result
; if its fuel is increased.
(defrule more-fuel-is-good-for-eval
  (implies 
    (and (erl-state-p s)
         (erl-k-p k)
         (natp n)
         (not (equal (erl-val-kind (erl-state->in (erl-s-klst->s (eval-k k s)))) :flimit)))
    (equal (erl-s-klst->s (eval-k (erl-k (+ n (erl-k->fuel k))
                                         (erl-k->kont k)) 
                                  s))
           (erl-s-klst->s (eval-k k s))))
  :enable eval-k)

; A continuation that did not cause an error in apply-k will produce the same result
; if its fuel is increased.
(defrule more-fuel-is-good-for-apply
  (implies
    (and (erl-state-p s)
         (erl-klst-p klst)
         (not (equal (erl-val-kind (erl-state->in (apply-k s klst))) :flimit))
         (natp n))
    (equal (apply-k s (increase-fuel klst n))
           (apply-k s klst)))
  :enable (apply-k increase-fuel)
  :disable (apply-k-of-not-flimit  increase-fuel-is-distributive-over-append more-fuel-is-good-for-eval)
  :expand (apply-k s (cons (erl-k (+ n (erl-k->fuel (car klst)))
                                   (erl-k->kont (car klst)))
                            (increase-fuel (cdr klst) n)))
  :hints (("Subgoal *1/8'''"
      :use ((:instance apply-k-of-not-flimit (s s) (klst klst))
            (:instance increase-fuel-is-distributive-over-append
              (s s)
              (rest (cdr klst))
              (k (car klst))
              (n n))
            (:instance more-fuel-is-good-for-eval
              (s s)
              (k (car klst))
              (n n))))))


; Erl-State Theorems -----------------------------------------------------------

; Erl-states are equal if their field are equal
(defruled erl-states-are-equal-if-fields-are-equal
  (implies 
    (and (erl-state-p x)
         (erl-state-p y)
         (erl-klst-p klst)
         (equal (erl-state->in x) (erl-state->in y))
         (equal (erl-state->bind x) (erl-state->bind y)))
    (equal (apply-k x klst) (apply-k y klst)))
  :expand ((apply-k x klst) (apply-k y klst))
  :enable (erl-state->in erl-state->bind erl-state-p))