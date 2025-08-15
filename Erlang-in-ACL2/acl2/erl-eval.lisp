(in-package "ACL2")
(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/top" :dir :system)
(include-book "erl-op")
(include-book "eval-theorems")

(set-induction-depth-limit 1)

;; ------------------------------- erlang evaluator ----------------------------------------------

(fty::defprod erl-val-klst
  ((v erl-value-p :default (make-erl-value-nil))
   (k erl-k-list-p :default nil)))

; eval-k is non-recursive.  i could embed eval-k in the boddy of apply-k.
; i'm guessing that making a separate function for eval-k may be handy because we will
; be able to prove lemmas that apply regardless of the kind of k.  likewise, proofs
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
      (make-erl-val-klst :k (list (make-erl-k-expr :expr k.right-expr)
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


;;-------------------------------------- theorems --------------------------------------------------

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


;; this might be dangerous in some contexts - where fuel is known to be much greater than 0.
(defrule a-little-more-fuel-is-good
  (implies 
    (and (erl-value-p val)
         (erl-k-list-p klst)
         (natp fuel)
         (not (equal (erl-value-kind (apply-k val klst (+ -1 fuel))) :fault)))
    (equal (apply-k val klst fuel)
           (apply-k val klst (+ -1 fuel))))
  :in-theory (enable apply-k))


(defruled apply-k-of-append
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


(defrule apply-k-val-is-not-fault
  (implies
    (and (erl-value-p val)
	       (not (equal (erl-value-kind (apply-k val klst fuel)) :fault)))
    (not (equal (erl-value-kind val) :fault)))
  :expand (apply-k val klst fuel))


(defrule apply-k-of-nil
  (implies (and (erl-value-p val)
                (posp fuel))
           (equal (apply-k val nil fuel)
                  val))
  :expand (apply-k val nil fuel))




;;; APPLY-K of BINOP

(defruled reveal-apply-k-of-binary-op-step-1
  (implies
    (and (erl-k-list-p klst)
         (not (endp klst))
         (erl-value-p val)
         (natp fuel)
	       (not (equal (erl-value-kind (apply-k val klst fuel)) :fault))
         (equal (erl-k-kind (car klst)) :expr)
         (equal (node-kind (erl-k-expr->expr (car klst))) :binary-op))
    (and  (> fuel 1)
          (equal (apply-k val klst fuel)
                 (apply-k '(:nil)
                          (append (list (erl-k-expr (node-binary-op->left (erl-k-expr->expr (car klst))))
                                        (erl-k-binary-op-expr1 (node-binary-op->op (erl-k-expr->expr (car klst)))
                                                                                (node-binary-op->right (erl-k-expr->expr (car klst)))
                                                                                nil))
                                  (cdr klst))
                          fuel))))
  :in-theory (enable apply-k eval-k))

(defruled reveal-apply-k-of-binary-op-step-1.5
  (implies
    (and (erl-k-list-p klst)
         (not (endp klst))
         (erl-value-p val)
         (natp fuel)
	       (not (equal (erl-value-kind (apply-k val klst fuel)) :fault))
         (equal (erl-k-kind (car klst)) :expr)
         (equal (node-kind (erl-k-expr->expr (car klst))) :binary-op))
    (equal  (apply-k val klst fuel)
            (apply-k val
                    (append (list (erl-k-expr (node-binary-op->left (erl-k-expr->expr (car klst))))
                                  (erl-k-binary-op-expr1 (node-binary-op->op (erl-k-expr->expr (car klst)))
                                                                          (node-binary-op->right (erl-k-expr->expr (car klst)))
                                                                          nil))
                            (cdr klst))
                    fuel)))
  :use (:instance reveal-apply-k-of-binary-op-step-1
          (klst klst) (val val) (fuel fuel))
  :expand (:free (v) (apply-k v
                          (LIST* (ERL-K-EXPR (NODE-BINARY-OP->LEFT (ERL-K-EXPR->EXPR (CAR KLST))))
            (ERL-K-BINARY-OP-EXPR1
                 (NODE-BINARY-OP->OP (ERL-K-EXPR->EXPR (CAR KLST)))
                 (NODE-BINARY-OP->RIGHT (ERL-K-EXPR->EXPR (CAR KLST)))
                 NIL)
            (CDR KLST))
                          fuel))
  :enable (eval-k))



(defruled reveal-apply-k-of-binary-op-step-2
  (implies
    (and (erl-k-list-p klst)
         (not (endp klst))
         (erl-value-p val)
         (natp fuel)
	       (not (equal (erl-value-kind (apply-k val klst fuel)) :fault))
         (equal (erl-k-kind (car klst)) :expr)
         (equal (node-kind (erl-k-expr->expr (car klst))) :binary-op))
    (equal  (apply-k val klst fuel)
            (apply-k (apply-k val (list (erl-k-expr (node-binary-op->left (erl-k-expr->expr (car klst))))) fuel)
                    (cons (erl-k-binary-op-expr1 (node-binary-op->op (erl-k-expr->expr (car klst)))
                                                  (node-binary-op->right (erl-k-expr->expr (car klst)))
                                                  nil)
                          (cdr klst)) 
                    fuel)))
  :use  ((:instance reveal-apply-k-of-binary-op-step-1.5
          (klst klst) (val val) (fuel fuel))   
          (:instance apply-k-of-append 
          (klst (list* (erl-k-expr (node-binary-op->left (erl-k-expr->expr (car klst))))
                       (erl-k-binary-op-expr1
                          (node-binary-op->op (erl-k-expr->expr (car klst)))
                          (node-binary-op->right (erl-k-expr->expr (car klst)))
                          nil)
                       (cdr klst))) 
          (klst1 (list (erl-k-expr (node-binary-op->left (erl-k-expr->expr (car klst))))))
          (klst2 (cons (erl-k-binary-op-expr1 (node-binary-op->op (erl-k-expr->expr (car klst)))
                                              (node-binary-op->right (erl-k-expr->expr (car klst)))
                                              nil)
                        (cdr klst)))
          (val val)
          (fuel fuel))))


(defruled reveal-apply-k-of-binary-op-step-3
  (implies
    (and (erl-k-list-p klst)
         (not (endp klst))
         (erl-value-p val)
         (natp fuel)
	       (not (equal (erl-value-kind (apply-k val klst fuel)) :fault))
         (equal (erl-k-kind (car klst)) :expr)
         (equal (node-kind (erl-k-expr->expr (car klst))) :binary-op))
    (equal (apply-k val klst fuel)
           (apply-k '(:nil)
                    (append (list (erl-k-expr (node-binary-op->right (erl-k-expr->expr (car klst))))
                                  (erl-k-binary-op-expr2 (node-binary-op->op (erl-k-expr->expr (car klst)))
                                                        (apply-k val (list (erl-k-expr (node-binary-op->left (erl-k-expr->expr (car klst))))) fuel)
                                                        nil))
                            (cdr klst))
                      fuel)))
    :use ((:instance reveal-apply-k-of-binary-op-step-2
          (klst klst) (val val) (fuel fuel)))
    :expand 
      (:free (v) (apply-k v 
                          (cons (erl-k-binary-op-expr1 (node-binary-op->op (erl-k-expr->expr (car klst)))
                                                       (node-binary-op->right (erl-k-expr->expr (car klst)))
                                                        nil)
                                (cdr klst))
                          fuel))
    :enable (eval-k))


(defruled reveal-apply-k-of-binary-op-step-3.5
  (implies
    (and (erl-k-list-p klst)
         (not (endp klst))
         (erl-value-p val)
         (natp fuel)
	       (not (equal (erl-value-kind (apply-k val klst fuel)) :fault))
         (equal (erl-k-kind (car klst)) :expr)
         (equal (node-kind (erl-k-expr->expr (car klst))) :binary-op))
    (equal  (apply-k val klst fuel)
            (apply-k  val
                      (append (list (erl-k-expr (node-binary-op->right (erl-k-expr->expr (car klst))))
                                    (erl-k-binary-op-expr2 (node-binary-op->op (erl-k-expr->expr (car klst)))
                                                          (apply-k val (list (erl-k-expr (node-binary-op->left (erl-k-expr->expr (car klst))))) fuel)
                                                          nil))
                              (cdr klst))
                        fuel)))
    :use (:instance reveal-apply-k-of-binary-op-step-3
          (klst klst) (val val) (fuel fuel))
    :expand (:free (v) (apply-k 
                          v
                          (list*  (erl-k-expr (node-binary-op->right (erl-k-expr->expr (car klst))))
                                  (erl-k-binary-op-expr2 (node-binary-op->op (erl-k-expr->expr (car klst)))
                                                        (apply-k val (list (erl-k-expr (node-binary-op->left (erl-k-expr->expr (car klst))))) fuel)
                                                        nil)
                                  (cdr klst))
                           fuel))
    :enable (eval-k))

(defruled reveal-apply-k-of-binary-op-step-4
  (implies
    (and (erl-k-list-p klst)
         (not (endp klst))
         (erl-value-p val)
         (natp fuel)
	       (not (equal (erl-value-kind (apply-k val klst fuel)) :fault))
         (equal (erl-k-kind (car klst)) :expr)
         (equal (node-kind (erl-k-expr->expr (car klst))) :binary-op))
    (equal  (apply-k val klst fuel)
            (apply-k (apply-k val (list (erl-k-expr (node-binary-op->right (erl-k-expr->expr (car klst))))) fuel)
                     (cons (erl-k-binary-op-expr2 (node-binary-op->op (erl-k-expr->expr (car klst)))
                                                        (apply-k val (list (erl-k-expr (node-binary-op->left (erl-k-expr->expr (car klst))))) fuel)
                                                        nil)
                          (cdr klst)) 
                    fuel)))

  :use  ((:instance reveal-apply-k-of-binary-op-step-3.5
          (klst klst) (val val) (fuel fuel))   
          (:instance apply-k-of-append 
          (klst (list* (erl-k-expr (node-binary-op->right (erl-k-expr->expr (car klst))))
                       (erl-k-binary-op-expr2 (node-binary-op->op (erl-k-expr->expr (car klst)))
                                              (apply-k val (list (erl-k-expr (node-binary-op->left (erl-k-expr->expr (car klst))))) fuel)
                                              nil)
                       (cdr klst))) 
          (klst1 (list (erl-k-expr (node-binary-op->right (erl-k-expr->expr (car klst))))))
          (klst2 (cons (erl-k-binary-op-expr2 (node-binary-op->op (erl-k-expr->expr (car klst)))
                                              (apply-k val (list (erl-k-expr (node-binary-op->left (erl-k-expr->expr (car klst))))) fuel)
                                              nil)
                        (cdr klst)))
          (val val)
          (fuel fuel))))

(defrule apply-k-of-binary-op
  (implies
    (and (erl-k-list-p klst)
         (not (endp klst))
         (erl-value-p val)
         (natp fuel)
	       (not (equal (erl-value-kind (apply-k val klst fuel)) :fault))
         (equal (erl-k-kind (car klst)) :expr)
         (equal (node-kind (erl-k-expr->expr (car klst))) :binary-op))
    (equal (apply-k val klst fuel)
           (apply-k 
            (apply-erl-binop
              (node-binary-op->op (erl-k-expr->expr (car klst)))
              (apply-k val (list (erl-k-expr (node-binary-op->left (erl-k-expr->expr (car klst))))) fuel)
              (apply-k val (list (erl-k-expr (node-binary-op->right (erl-k-expr->expr (car klst))))) fuel))
            (cdr klst) fuel)))

    :use ((:instance reveal-apply-k-of-binary-op-step-4
          (klst klst) (val val) (fuel fuel)))
    :expand 
      (:free (v) (apply-k v 
                          (cons (erl-k-binary-op-expr2 (node-binary-op->op (erl-k-expr->expr (car klst)))
                                                       (apply-k val (list (erl-k-expr (node-binary-op->left (erl-k-expr->expr (car klst))))) fuel)
                                                       nil)
                                (cdr klst)) 
                          fuel))
    :enable (eval-k))

;; This is of course trivial to prove, but it is painful to try to do this for the
;; corresponding expression itself. The question is: would that even be useful?
(defrule apply-k-of-binary-op-comm
  (implies
    (and (erl-k-list-p klst)
         (not (endp klst))
         (erl-value-p val)
         (natp fuel)
	       (not (equal (erl-value-kind (apply-k val klst fuel)) :fault))
         (equal (erl-k-kind (car klst)) :expr)
         (equal (node-kind (erl-k-expr->expr (car klst))) :binary-op)
         (equal (node-binary-op->op (erl-k-expr->expr (car klst))) '+))
    (equal (apply-k val klst fuel)
           (apply-k 
            (apply-erl-binop
              (node-binary-op->op (erl-k-expr->expr (car klst)))
              (apply-k val (list (erl-k-expr (node-binary-op->right (erl-k-expr->expr (car klst))))) fuel)
              (apply-k val (list (erl-k-expr (node-binary-op->left (erl-k-expr->expr (car klst))))) fuel))
            (cdr klst) fuel)))
  :enable apply-erl-binop)