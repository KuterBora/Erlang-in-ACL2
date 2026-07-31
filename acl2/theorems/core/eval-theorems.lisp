(in-package "ACL2")
(include-book "../../eval/top")

(set-induction-depth-limit 1)

; Stepping Rules ---------------------------------------------------------------

(defruled apply-k-of-append
    (equal
      (apply-k s (append kl1 kl2))
      (apply-k (apply-k s kl1) kl2))
  :enable apply-k
  :prep-lemmas
    ((defrule lemma-1
    	(b* (((cons k kl) kl1)
	         (ks (eval-k k s))
           (r (erl-s-klst->s ks))
           (ks (erl-s-klst->klst ks)))
	        (implies
	          (and (wf-state-p s)
                 (equal (apply-k r (append ks kl kl2))
	                      (apply-k (apply-k r (append ks kl)) kl2)))
	          (equal
              (apply-k s (cons k (append kl kl2)))
		          (apply-k (apply-k r (append ks kl)) kl2))))
      :prep-lemmas
        ((defrule lemma-1a
          (implies
            (wf-state-p s)
            (equal (apply-k s (cons k kl))
                   (apply-k (erl-s-klst->s (eval-k k s))
                            (append (erl-s-klst->klst (eval-k k s)) kl))))
          :expand ((apply-k s (cons k kl))))))))

(defrule apply-k-of-append-bad
  (b* ((s1 (apply-k s0 kl1))
       (s2 (apply-k s0 (append kl1 kl2)))
       ((if (wf-state-p s1)) t))
      (null (wf-state-p s2)))
  :use ((:instance apply-k-of-append (s s0))))

(defruled apply-k-of-step
  (implies
    (wf-state-p s)
    (equal (apply-k s (cons k nil))
	         (apply-k (erl-s-klst->s (eval-k k s))
	                  (erl-s-klst->klst (eval-k k s)))))
    :expand (apply-k s (cons k nil)))

(defrule apply-k-of-kont-pair
  (equal (apply-k s (list k1 k2))
         (apply-k (apply-k s (list k1)) (list k2)))
  :enable apply-k-of-step
  :use ((:instance apply-k (klst (list k1 k2)))
        (:instance apply-k-of-append
          (s (erl-s-klst->s (eval-k k1 s)))
          (kl1 (erl-s-klst->klst (eval-k k1 s)))
          (kl2 (list k2)))))

(defrule erl-state-of-wf-apply-k
  (implies (wf-state-p (apply-k s klst))
           (wf-state-p s)))

(defrule fuel-of-wf-apply-k
  (implies (wf-state-p (apply-k s (cons k nil)))
           (> (erl-k->fuel k) 0))
  :enable apply-k)


; Lemmas about Stepping ---------------------------------------------------------

(defrule insuffucient-fuel-for-step
  (implies
    (and (< (erl-k->fuel (car klst)) 2)
         (consp klst)
         (erl-s-klst->klst (eval-k (car klst) s)))
    (not (wf-state-p (apply-k (erl-s-klst->s (eval-k (car klst) s))
                              (append (erl-s-klst->klst (eval-k (car klst) s))
                                      (cdr klst))))))
  :enable apply-k)

(defrule wf-state-implies-next-wf-state
  (implies (and (consp klst) (wf-state-p (apply-k s klst)))
           (wf-state-p (apply-k (erl-s-klst->s (eval-k (car klst) s))
                                (erl-s-klst->klst (eval-k (car klst) s)))))
  :expand (apply-k s klst)
  :enable apply-k-of-append
  :rule-classes :forward-chaining)