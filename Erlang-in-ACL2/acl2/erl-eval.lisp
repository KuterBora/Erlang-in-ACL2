(in-package "ACL2")
(include-book "centaur/fty/top" :DIR :SYSTEM)
(include-book "std/util/top" :DIR :SYSTEM)
(include-book "erl-op")
(include-book "eval-theorems")

(set-induction-depth-limit 1)

;; ------------------------------- Erlang Evaluator ----------------------------------------------

(fty::defprod erl-val-klst
  ((v erl-value-p :default (make-erl-value-nil))
   (k erl-k-list-p :default nil)))

; eval-k is non-recursive.  I could embed eval-k in the boddy of apply-k.
; I'm guessing that making a separate function for eval-k may be handy because we will
; be able to prove lemmas that apply regardless of the kind of k.  Likewise, proofs
; about apply-k are less likely to split into a large number of redundant cases.
(define eval-k ((k erl-k-p) (val erl-value-p))
  :returns (kv erl-val-klst-p)
  (erl-k-case k
    (:expr
     (let ((x k.expr))
       (node-case x
        (:integer (make-erl-val-klst :v (make-erl-value-integer :val x.val)))
        (:atom    (make-erl-val-klst :v (make-erl-value-atom :val x.val)))
        (:string  (make-erl-val-klst :v (make-erl-value-string :val x.val)))
        (:binary-op
          (make-erl-val-klst
            :k (list (make-erl-k-expr :expr x.left)
              (make-erl-k-binary-op-expr1 :op x.op :right-expr x.right))))
        (:fault (make-erl-val-klst :v (make-erl-value-fault :err 'bad-ast)))
        (otherwise (make-erl-val-klst :v (make-erl-value-fault :err 'not-implemented))))))
    (:binary-op-expr1
      (make-erl-val-klst
        :k (list (make-erl-k-expr :expr k.right-expr)
      (make-erl-k-binary-op-expr2 :op k.op :left-val val))))
    (:binary-op-expr2
      (make-erl-val-klst :v (apply-erl-binop k.op k.left-val val)))
    (otherwise (make-erl-val-klst :v (make-erl-value-fault :err 'bad-kont)))))

(define apply-k ((val erl-value-p) (klst erl-k-list-p) (fuel natp))
  :returns (v erl-value-p)
  :well-founded-relation l<
  :measure (list (nfix fuel) (len klst))
  (b* ((val (erl-value-fix val))
       (klst (erl-k-list-fix klst))
       ((if (zp fuel)) '(:fault out-of-fuel))
       ((if (equal (erl-value-kind val) :fault)) val)
       ((if (endp klst)) val)
       ((cons khd ktl) klst)
       ((erl-val-klst kv) (eval-k khd val))
       ((if (equal (erl-value-kind kv.v) :fault)) kv.v))
    (apply-k kv.v (append kv.k ktl) (- fuel (if kv.v 1 0)))))


;;-------------------------------------- Theorems --------------------------------------------------

(defrule more-fuel-is-good
  (implies 
    (and (erl-value-p val)
         (erl-k-list-p klst)
         (natp fuel)
         (natp z)
         (not (equal (erl-value-kind (apply-k val klst fuel)) :fault)))
    (equal (apply-k val klst (+ fuel z))
           (apply-k val klst fuel)))
  :in-theory (enable apply-k))


;; This might be dangerous in some contexts - where fuel is known to be much greater than 0.
(defrule a-little-more-fuel-is-good
  (implies 
    (and (erl-value-p val)
         (erl-k-list-p klst)
         (natp fuel)
         (not (equal (erl-value-kind (apply-k val klst (+ -1 fuel))) :fault)))
    (equal (apply-k val klst fuel)
           (apply-k val klst (+ -1 fuel))))
  :in-theory (enable apply-k))


(defrule apply-k-of-append
  (implies
    (and (erl-k-list-p klst1)
         (erl-k-list-p klst2)
         (erl-value-p val)
         (equal klst (append klst1 klst2))
         (natp fuel)
	       (not (equal (erl-value-kind (apply-k val klst fuel)) :fault)))
    (equal
      (apply-k val klst fuel)
      (apply-k (apply-k val klst1 fuel) klst2 fuel)))
  :in-theory (enable apply-k))


(defrule apply-k-of-car
  (implies
    (and (erl-k-list-p klst)
         (not (endp klst))
         (erl-value-p val)
         (natp fuel)
	       (not (equal (erl-value-kind (apply-k val klst fuel)) :fault)))
    (equal
      (apply-k val klst fuel)
      (apply-k (apply-k val (list (car klst)) fuel) (cdr klst) fuel)))
  :use (:instance apply-k-of-append
          (klst1 (list (car klst)))
          (klst2 (cdr klst))
          (fuel fuel)
          (val val)))


(defrule apply-k-of-binop
  (implies
    (and (erl-k-list-p klst)
         (erl-value-p val)
         (natp fuel)
	       (not (equal (erl-value-kind (apply-k val klst fuel)) :fault))
         (car (erl-)))
    (equal
      (apply-k val klst fuel)
      (apply-k (apply-k val (list (car klst)) fuel) (cdr klst) fuel)))
  :use (:instance apply-k-of-append
          (klst1 (list (car klst)))
          (klst2 (cdr klst))
          (fuel fuel)
          (val val)))





