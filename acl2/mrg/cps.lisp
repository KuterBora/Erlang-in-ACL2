(in-package "ACL2")

(include-book "std/util/top" :dir :system)
(include-book "centaur/fty/top" :DIR :SYSTEM)
(include-book "kestrel/fty/defsubtype" :DIR :SYSTEM)

(include-book "transitivity")

(local (deflabel pre-arith-5))
(local (include-book "arithmetic-5/top" :dir :system))
(local (deftheory arith-5
		  (set-difference-theories
		    (universal-theory :here)
		    (universal-theory 'pre-arith-5))))

(set-induction-depth-limit 1)
(set-warnings-as-errors t '("Use" "Equiv") state)


(local (encapsulate nil
  (defrule nfix-when-natp
    (implies (natp n) (equal (nfix n) n)))

  (defrule natp-of-posp-minus-1
    (implies (and (natp n) (< 0 n))
	     (natp (1- n))))
  (deftheory nat-theory '(natp nfix nat-equiv))))
(local (in-theory (disable nat-theory)))




; AST Types -------------------------------------------------------------
(fty::defsubtype binop
  :supertype symbolp
  :restriction 
    (lambda (x) 
      (not (null (member x '(+ - *)))))
  :fix-value '+)

(fty::deftagsum ast
  (:integer ((v integerp)))
  (:binop ((op binop-p)
	   (left ast-p)
	   (right ast-p))))

; values
(fty::deftagsum val
  ; Erlang return values
  (:integer ((v integerp)))
  (:none ())
  (:excpt ((why symbolp)))
  (:flimit ()))

;; (wf-val-p x): true if x is "well-formed", i.e. if (val-kind x) is :integer or :none.
;; We val-fix x before checking kind.  This means that wf-val-p is preserved by val-fix
;; which works nicely with functions that fix there argument (which the should).  It
;; also means that (wf-val-p x) does not necessarily imply (val-p x).  For example,
;;  (wf-val-p '(:integer 'cow)) = (wf-val-p (val-fix (list :integer 'cow)))
;;                              = (wf-val-p (list :integer (ifix 'cow)))
;;                              = (wf-val-p (list :integer 0)
;;                              = t
;; whereas (val-p '(:integer 'cow)) = nil
(define wf-val-p ((x val-p))
  :returns (ok booleanp)
  (consp (member (val-kind (val-fix x)) '(:integer :none)))
  ///
  (defcong val-equiv equal (wf-val-p x) 1))

; Continuation Types -------------------------------------------------------------
(fty::deftagsum kont0
    ; Erlang expression to be evaluated.
    (:expr ((expr ast-p)))

    ; Continue after the first operand of a binop has been evaluated.
    (:binop-expr1
      ((op binop-p)
       (right ast-p)))
    ; Continue after the second operand of a binop has been evaluated.
    (:binop-expr2 
      ((op binop-p)
       (left val-p))))

(fty::defprod kont
    ((fuel natp)
     (k kont0-p)))

(fty::deflist klst
  :elt-type kont
  :true-listp t)


(defcong klst-equiv equal (consp kl) 1
  :hints(("Goal" :in-theory (enable klst-fix))))

(defsection klst-measure
  (encapsulate ;; showing that evaluating a continuation decreases fuel
    (((eval-op * *) => (mv * *))) ; evaluation function

    ; Witness function
    (local (defun eval-op (v k)
      (mv (val-fix v)
	(and (> (kont->fuel k) 0)
	     (list (change-kont k :fuel (1- (kont->fuel k)))
		   (change-kont k :fuel (1- (kont->fuel k))))))))

    ; Constraints
    (defrule val-p-of-eval-op-0
      (val-p (mv-nth 0 (eval-op v k))))
    (defrule klst-p-of-eval-op-1
      (klst-p (mv-nth 1 (eval-op v k))))
    (defcong val-equiv equal (eval-op v k) 1)
    (defcong kont-equiv equal (eval-op v k) 2)

    ; (len (mv-nth 1 (eval-op v k))) is either 0 or 2
    (defrule len-of-eval-op-1
      (let ((ks (mv-nth 1 (eval-op v k))))
	(implies ks
		 (and (consp ks) (consp (cdr ks)) (not (cddr ks))))))

    (defrule eval-op-decreases-fuel
      (let ((ks (mv-nth 1 (eval-op v k))))
	(implies
	  ks
	  (and (equal (kont->fuel (car ks)) (- (kont->fuel k) 1))
	       (equal (kont->fuel (cadr ks)) (- (kont->fuel k) 1)))))
      :enable nat-theory))

  (define klst-measure ((kl klst-p))
    :returns m
    :measure (len kl)
    (let ((kl (klst-fix kl)))
      (if (consp kl)
	  (+ (expt 3 (kont->fuel (car kl)))
	     (klst-measure (cdr kl)))
	  0))
    ///
    (defcong klst-equiv equal (klst-measure kl) 1)

    (local (encapsulate nil ; some lemmas for subsequent theorems about klst-measure
      (defrule integerp-of-expt3
	(implies (natp i) (integerp (expt 3 i)))
	:rule-classes ((:forward-chaining :trigger-terms ((expt 3 i)))))

      (defrule pos-of-expt3
	(implies (natp i) (< 0 (expt 3 i)))
	:rule-classes :linear)

      (defrule klst-measure-of-cons-lemma
	(equal (klst-measure (cons k kl))
	       (+ (expt 3 (kont->fuel k)) (klst-measure kl)))
	:disable klst-measure
	:expand ((klst-measure (cons k kl))))))

    (defrule natp-of-klst-measure
      (natp (klst-measure kl))
      :enable nat-theory)

    (defrule klst-measure-of-nil
      (implies (not (consp kl))
	       (equal (klst-measure kl) 0)))

    (defrule klst-measure-of-cons
      (< (klst-measure kl)
	 (klst-measure (cons k kl)))
      :in-theory (disable klst-measure))

    (defrule klst-measure-of-append
      (equal (klst-measure (append kl1 kl2))
	     (+ (klst-measure kl1) (klst-measure kl2))))

    (defrule eval-op-decreases-klst-measure
      (< (klst-measure (append (mv-nth 1 (eval-op v k)) kl))
	 (klst-measure (cons k kl)))
      :disable len-of-eval-op-1
      :use ((:instance len-of-eval-op-1)))))


; Our evaluator
(define apply-binop ((op binop-p) (v1 val-p) (v2 val-p))
  :returns (v val-p)
  (b* ((op (binop-fix op))
       (v1 (val-fix v1))
       (v2 (val-fix v2))
       ((unless (wf-val-p v1)) v1)
       ((unless (wf-val-p v2)) v2)
       ((unless (and (equal (val-kind v1) :integer)
		     (equal (val-kind v2) :integer)))
	(make-val-excpt :why 'badarg))
       (i1 (val-integer->v v1))
       (i2 (val-integer->v v2))
       (i (case-match op
	    ('+ (+ i1 i2))
	    ('- (- i1 i2))
	    ('* (- i1 i2))))
       ((unless (natp i)) (make-val-excpt :why 'badval)))
    (make-val-integer :v i))
  ///
  (defcong binop-equiv equal (apply-binop op v1 v2) 1)
  (defcong val-equiv equal   (apply-binop op v1 v2) 2)
  (defcong val-equiv equal   (apply-binop op v1 v2) 3)
  (more-returns
    (v :name apply-binop-when-bad-v1
      (implies (not (wf-val-p v1))
	       (equal v (val-fix v1))))

    (v :name apply-binop-when-bad-v2
      (implies (and (wf-val-p v1) (not (wf-val-p v2)))
	       (equal v (val-fix v2))))))

; eval-k: evaluate a single continuation
(define eval-k ((v val-p) (k kont-p) )
  :returns (mv (r val-p) (ks klst-p))
  :guard (wf-val-p v)
  (b* (((kont k) (kont-fix k))
       (fuel k.fuel)
       (k0 k.k)
       (v (val-fix v))

       ; We check (wf-val-p v) in apply-k which ensures the guard
       ; Here we mbt it to make proofs succeed.
       ((unless (mbt (wf-val-p v))) (mv v nil))

       ; Return flimit if fuel has run out.
       ((if (zp fuel)) (mv (make-val-flimit) nil)))
    (kont0-case k0
      ; Evaluate an expression.
      (:expr (let ((x k0.expr))
        (ast-case x
          ; if x is an atomic term, simply return its value 
          (:integer (mv (make-val-integer :v x.v) nil))
          ; if x is a binop, evaluate the first operand, save the operator and the second operand
          (:binop
            (mv (make-val-none)
		(list (make-kont :fuel (1- fuel)
				 :k (make-kont0-expr :expr x.left))
		      (make-kont :fuel (1- fuel) 
				 :k (make-kont0-binop-expr1 :op x.op 
							    :right x.right))))))))

      ; Evaluate the second operand of a binop, save the operator and value of the first operand
      (:binop-expr1 
	(mv (make-val-none)
	    (list (make-kont :fuel (1- fuel)
			     :k (make-kont0-expr :expr k0.right))
		  (make-kont :fuel (1- fuel) 
			     :k (make-kont0-binop-expr2 :op k0.op 
							:left v)))))

      ; Apply the binop to the evaluated operands
      (:binop-expr2
	(mv (apply-binop k0.op k0.left v)
	    nil))))
  ///
  (defcong val-equiv equal (eval-k v k) 1)
  (defcong kont-equiv equal (eval-k v k) 2)


  (more-returns
    (ks :name len-of-eval-k-1
      (implies ks
	      (and (consp ks) (consp (cdr ks)) (not (cddr ks)))))

    (ks :name eval-k-decreases-fuel
      (implies ks
        (and (equal (kont->fuel (car ks)) (- (kont->fuel k) 1))
            (equal (kont->fuel (cadr ks)) (- (kont->fuel k) 1)))))

    (ks :name eval-k-decreases-klst-measure
      (< (klst-measure (append ks kl))
         (klst-measure (cons k kl)))
    :hints(("Goal"
             :in-theory (disable eval-k)
             :use (:functional-instance
                    eval-op-decreases-klst-measure 
                      (eval-op eval-k))))))

    (defrule eval-k-when-exception
      (implies (not (wf-val-p v))
	       (equal (eval-k v k) (mv (val-fix v) nil))))

    (defrule eval-k-when-out-of-fuel
      (implies (and (wf-val-p v) (zp (kont->fuel k)))
	       (equal (eval-k v k) (mv (make-val-flimit) nil)))))

(define apply-k ((v val-p) (kl klst-p))
  :returns (r val-p)
  :measure (klst-measure kl)
  :hints(("Goal" ; for termination proof
    :in-theory (disable eval-k-decreases-klst-measure)
    :use ((:instance eval-k-decreases-klst-measure (k (car kl)) (kl (cdr kl))))))

  (b* ((v (val-fix v))
       (kl (klst-fix kl))
       ((unless (wf-val-p v)) v)
       ((unless (consp kl)) v)
       ((cons (kont khd) ktl) kl)
       ((mv new-v new-kl) (eval-k v khd)))
    (apply-k new-v (append new-kl ktl)))
  ///
  (local (in-theory (disable apply-k)))
  (defcong val-equiv equal (apply-k v kl) 1
    :hints(("Goal" :expand ((apply-k v kl) (apply-k v-equiv kl)))))
  (defcong klst-equiv equal (apply-k v kl) 2
    :hints(("Goal" :expand ((apply-k v kl) (apply-k v kl-equiv)))))
  (defrule apply-k-of-nil (equal (apply-k v nil) (val-fix v))
    :hints(("Goal" :expand ((apply-k v nil) (apply-k v kl-equiv)))))
	   
  (local (in-theory (enable apply-k)))
  (defrule apply-k-when-bad-v
    (implies (not (wf-val-p v))
	     (equal (apply-k v kl) (val-fix v))))

  (defrule apply-k-when-out-of-fuel
    (implies (and (wf-val-p v) (consp kl) (zp (kont->fuel (car kl))))
	     (equal (apply-k v kl) (make-val-flimit))))


  (defruled apply-k-of-append
    (equal
      (apply-k v (append kl1 kl2))
      (apply-k (apply-k v kl1) kl2))
    :prep-lemmas (
      (defrule lemma-1
	(b* (((cons k kl) kl1)
	     ((mv r ks) (eval-k v k)))
	  (implies
	    (equal
	      (apply-k r (append ks kl kl2))
	      (apply-k (apply-k r (append ks kl)) kl2))
	    (equal (apply-k v (cons k (append kl kl2)))
		   (apply-k (apply-k r (append ks kl)) kl2))))
	:prep-lemmas (
	  (defrule lemma-1a
	    (equal (apply-k v (cons k kl))
		   (apply-k (mv-nth 0 (eval-k v k))
			    (append (mv-nth 1 (eval-k v k)) kl)))
	    :expand ((apply-k v (cons k kl))))))))


  (local (in-theory (disable apply-k)))
  ; (mrg) I'm keeping this because it was in Kuter's code.  I never enable or
  ;   use it.  The rule seems very prone to causing rewrite loops.
  (defruled apply-k-of-cons
    (equal (apply-k v (cons k kl))
	   (apply-k (apply-k v (list k)) kl))
    :use (:instance apply-k-of-append
	  (v v) (kl1 (list k)) (kl2 kl)))


  (defrule apply-k-of-step
    (equal (apply-k v (cons k nil))
	   (apply-k
	     (mv-nth 0 (eval-k v k))
	     (mv-nth 1 (eval-k v k))))
    :expand (apply-k v (cons k nil))))


  (defrule apply-k-of-append-bad
    (b* ((v1 (apply-k v0 kl1))
	 (v2 (apply-k v0 (append kl1 kl2)))
	 ((if (wf-val-p v1)) t))
      (null (wf-val-p v2)))
    :use((:instance apply-k-of-append (v v0))))

;; Let a be the AST for X op Y where X and Y are arbitrary AST nodes.
;;   Let k =  (make-kont :fuel fuel :k (make-kont0-expr :expr a))
;;       kx = (make-kont :fuel tbd  :k (make-kont0-expr :expr X))
;;       ky = (make-kont :fuel tbd  :k (make-kont0-expr :expr Y))
;;   The theorems below show that if v satisfies wf-val-p, then
;;   occur, then
;;     (equal (apply-k v (list* k k_rest))
;;       (apply-k
;;         (apply-binop op (apply-k (list kx) nil)
;;                         (apply-k (list ky) nil))
;;         k_rest))
;;   In the case that (wf-val-p (apply-k v (list k))), this lets us
;;   transform arguments about evaluation of continuation into arguments
;;   about the corresponding list expressions, e.g.
;;     (make-val-integer
;;       :v (+ (val-integer->v (apply-k (list kx) nil))
;;             (val-integer->v (apply-k (list ky) nil))))
;;   By the constructor/destructor theorems for val, these rewrites
;;   should compose nicely.  I'll try to demonstrate that.
;;
;; The main part of the construction is to show that
;;     (equal (apply-k v (list k))
;;            (apply-binop op (apply-k (list kx) nil)
;;                            (apply-k (list ky) nil)))
;; The claim above is then obtained by invoking apply-k-of-append.
;;
;; The continuation passing evaluation does roughly the following.
;; For brevity, writing (make-kont-kind :fuel f &rest) as an abbrevation for
;;   (make-kont :fuel f :k (make-kont-kind &rest))
;; 
;; (apply-k v (list k)) ->  unless (not wf-val-p v)
;;   (apply-k (make-val-none)
;;       (list (make-kont-expr :fuel (- fuel 1) :expr X)
;;             (make-kont-binop-expr1 :fuel (- fuel 1) :op op :right Y)
;;     -> unless (zp (- fuel 1)), (not (wf-val-p (apply-k kx nil)))
;; (apply-k (apply-k kx nil)
;;          (make-kont-binop-expr1 :fuel (- fuel 1) :op op :right Y))
;;     ->
;; (apply-k (make-val-none)
;;          (list (make-kont-expr :fuel (- fuel 2) :expr k0.right = Y)
;;                (make-kont-binop-expr2  :fuel (- fuel 2) :op k0.op = op
;;                                        :left (apply-k kx nil))))
;;     -> unless (zp (- fuel 2)), (not (wf-val-p (apply-k kx nil)
;; (apply-k (list ky nil))
;;          (list (make-kont-binop-expr2  :fuel (- fuel 2) :op k0.op = op
;;                                        :left (apply-k kx nil))))
;;     -> (apply-binop op (apply-k kx nil) (apply-k ky nil))
;;
;; The proof works by verifying each of step of this derivation, working
;;   from the last to the first.

;(defrule eval-k-of-binop-expr2
;  (b* (((kont k) k)
;       ((kont0-binop-expr2 k0) k.k)
;       ((unless (wf-val-p v)) t)
;       ((if (zp k.fuel)) t)
;       ((unless (equal (kont0-kind k0) :binop-expr2)) t))
;    (equal (eval-k v k)
;	   (mv (apply-binop k0.op k0.left v) nil)))
;  :use((:instance eval-k)))

; Seems to be a challenge to figure out the right rule for expressing how continuations compose.
; apply-k-of-append and apply-k-of-cons are disabled by default.
; Here, I'm trying a more restrictive rule, apply-k-of-kont-pair.
; Seems to work, at least for one example.
(defrule apply-k-of-kont-pair
  (equal (apply-k v (list k1 k2))
         (apply-k (apply-k v (list k1)) (list k2)))
  :use((:instance apply-k (kl (list k1 k2)))
       (:instance apply-k-of-append
		    (v (mv-nth 0 (eval-k v k1)))
		    (kl1 (mv-nth 1 (eval-k v k1)))
		    (kl2 (list k2)))))

(defrule apply-k-of-binop-expr2
  (implies
    (and
	 (not (zp (kont->fuel k)))
	 (equal (kont0-kind (kont->k k)) :binop-expr2)
	 (wf-val-p (kont0-binop-expr2->left (kont->k k))))
    (equal (apply-k v (list k))
	   (apply-binop (kont0-binop-expr2->op (kont->k k))
			(kont0-binop-expr2->left (kont->k k))
			v)))
  :use((:instance eval-k)))

(defrule apply-k-of-pair2
  (implies
    (and (wf-val-p v)
	 (equal (kont->fuel k1) (kont->fuel k2))
	 (equal (kont0-kind (kont->k k1)) :expr)
	 (equal (kont0-kind (kont->k k2)) :binop-expr2)
	 (wf-val-p (kont0-binop-expr2->left (kont->k k2))))
    (equal (apply-k v (list k1 k2))
	   (apply-binop
	     (kont0-binop-expr2->op (kont->k k2))
	     (kont0-binop-expr2->left (kont->k k2))
	     (apply-k v (list k1)))))
  :cases ((zp (kont->fuel k1))))

(defrule apply-k-of-binop-expr1
  (implies
    (equal (kont0-kind (kont->k k)) :binop-expr1)
    (equal (apply-k v (list k))
	   (apply-binop
	     (kont0-binop-expr1->op (kont->k k))
	     v
	     (apply-k
	       (make-val-none)
	       (list (make-kont
		       :fuel (1- (kont->fuel k))
		       :k (make-kont0-expr
			    :expr (kont0-binop-expr1->right (kont->k k)))))))))
  :use((:instance eval-k)))


(defrule apply-k-of-pair1
  (implies
    (and (equal (kont->fuel k1) (kont->fuel k2))
	 (equal (kont0-kind (kont->k k1)) :expr)
	 (equal (kont0-kind (kont->k k2)) :binop-expr1))
    (equal (apply-k v (list k1 k2))
	   (apply-binop
	     (kont0-binop-expr1->op (kont->k k2))
	     (apply-k v (list k1))
	     (apply-k
	       (make-val-none)
	       (list (make-kont
		       :fuel (1- (kont->fuel k2))
		       :k (make-kont0-expr
			    :expr (kont0-binop-expr1->right (kont->k k2))))))))))

(defrule apply-k-of-binop-expr
  (implies
    (and (wf-val-p v)
	 (equal (kont0-kind (kont->k k)) :expr)
	 (equal (ast-kind (kont0-expr->expr (kont->k k))) :binop))
    (equal (apply-k v (list k))
	   (apply-binop
	     (ast-binop->op (kont0-expr->expr (kont->k k)))
	     (apply-k
	       (make-val-none)
	       (list
		 (make-kont
		   :fuel (- (kont->fuel k) 1)
		   :k (make-kont0-expr
			:expr (ast-binop->left (kont0-expr->expr (kont->k k)))))))
	     (apply-k
	       (make-val-none)
	       (list
		 (make-kont
		   :fuel (- (kont->fuel k) 2)
		   :k (make-kont0-expr
			:expr (ast-binop->right (kont0-expr->expr (kont->k k))))))))))
  :use((:instance eval-k)))


;; more fuel is good.

(define <=-kont->fuel ((k1 kont-p) (k2 kont-p))
  :returns (ok booleanp)
  (b* (((kont k1) (kont-fix k1))
       ((kont k2) (kont-fix k2)))
    (and (<= k1.fuel k2.fuel)
	     (equal k1.k k2.k)))
  ///
  (defcong kont-equiv equal (<=-kont->fuel k1 k2) 1)
  (defcong kont-equiv equal (<=-kont->fuel k1 k2) 2)

  (defrule reflexivity-of-<=-kont->fuel
    (implies (kont-equiv k1 k2)
	     (and (<=-kont->fuel k1 k2)
		  (<=-kont->fuel k2 k1)))
    :rule-classes ((:forward-chaining :trigger-terms ((<=-kont->fuel k1 k2)))))

  (defrule transitivity-of-<=-kont->fuel
    (implies (and (<=-kont->fuel k1 k2)
                  (<=-kont->fuel k2 k3))
	     (<=-kont->fuel k1 k3))
    :rule-classes ((:rewrite :match-free :all))))


(define <=-klst->fuel ((kl1 klst-p) (kl2 klst-p))
  :measure (len kl1)
  :returns (ok booleanp)
  (if (consp kl1)
    (if (consp kl2)
      (and (<=-kont->fuel (car kl1) (car kl2))
	   (<=-klst->fuel (cdr kl1) (cdr kl2)))
      nil)
    (not (consp kl2)))
  ///
  (defcong klst-equiv equal (<=-klst->fuel kl1 kl2) 1)
  (defcong klst-equiv equal (<=-klst->fuel kl1 kl2) 2)

  (defrule reflexivity-of-<=-klst->fuel
    (implies (klst-equiv kl1 kl2)
	     (and (<=-klst->fuel kl1 kl2)
		  (<=-klst->fuel kl2 kl1)))
    :rule-classes ((:forward-chaining :trigger-terms ((<=-kont->fuel k1 k2))))
    :use((:functional-instance reflexivity-of-transitive-reflexive-list-relation
			       (transitive-reflexive-list-relation <=-klst->fuel))))

  (defrule transitivity-of-<=-klst->fuel
    (implies (and (<=-klst->fuel kl1 kl2)
                  (<=-klst->fuel kl2 kl3))
	     (<=-klst->fuel kl1 kl3))
    :rule-classes ((:rewrite :match-free :all))
    :use((:functional-instance transitivity-of-transitive-reflexive-list-relation
			       (transitive-reflexive-list-relation <=-klst->fuel)))))


(defruled eval-k-with-more-fuel-0
  (implies (and (not (equal (mv-nth 0 (eval-k v k1)) (make-val-flimit)))
		(<=-kont->fuel k1 k2))
	   (equal (mv-nth 0 (eval-k v k2))
		  (mv-nth 0 (eval-k v k1))))
  :enable (eval-k <=-kont->fuel))

(defrule eval-k-with-more-fuel-1
  (implies (and (not (equal (mv-nth 0 (eval-k v k1)) '(:flimit)))
		(<=-kont->fuel k1 k2))
	   (<=-klst->fuel
	     (mv-nth 1 (eval-k v k1))
	     (mv-nth 1 (eval-k v k2))))
  :enable (eval-k <=-kont->fuel <=-klst->fuel))

(defrule <=-klst->fuel-of-append
  (implies (and (<=-klst->fuel kl1a kl2a)
                (<=-klst->fuel kl1b kl2b))
	   (<=-klst->fuel (append kl1a kl1b) (append kl2a kl2b)))
  :induct (<=-klst->fuel kl1a kl2a)
  :enable <=-klst->fuel)


(defrule apply-k-with-more-fuel
  (implies (and (not (equal (apply-k v kl1) (make-val-flimit)))
		(<=-klst->fuel kl1 kl2))
	   (equal (apply-k v kl2) (apply-k v kl1)))
  :induct (induct-fn v v kl1 kl2)
  :enable (<=-klst->fuel apply-k)
  :prep-lemmas (
    (defrule lemma-1
      (implies (and (consp kl1)
		    (equal (apply-k (mv-nth 0 (eval-k v (car kl1)))
				    (append (mv-nth 1 (eval-k v (car kl1)))
					  (cdr kl1)))
			   (make-val-flimit)))
	       (equal (apply-k v kl1) (make-val-flimit)))
      :expand((apply-k v kl1)))

    (defrule lemma-2
      (implies (and (consp kl1)
		(equal (apply-k (mv-nth 0 (eval-k v (car kl1)))
				(append (mv-nth 1 (eval-k v (car kl2)))
					(cdr kl2)))
		       (apply-k (mv-nth 0 (eval-k v (car kl1)))
				(append (mv-nth 1 (eval-k v (car kl1)))
					(cdr kl1))))
		(not (equal (apply-k v kl1) (make-val-flimit)))
		(consp kl2)
		(<=-kont->fuel (car kl1) (car kl2))
		(<=-klst->fuel (cdr kl1) (cdr kl2)))
	   (equal (apply-k v kl2) (apply-k v kl1)))
      :expand ((apply-k v kl1) (apply-k v kl2))
      :use((:instance lemma-2.1
		      (v (mv-nth 0 (eval-k v (car kl))))
		      (kl (append (mv-nth 1 (eval-k v (car kl))) (cdr kl))))
	   (:instance eval-k-with-more-fuel-0
		      (v v) (k1 (car kl1)) (k2 (car kl2))))
      :prep-lemmas (
	(defruled lemma-2.1
	  (implies (not (equal (apply-k v kl) (make-val-flimit)))
		   (not (equal v (make-val-flimit))))
	  :expand ((apply-k v kl)))))

    (defrule lemma-3
      (implies (and (consp kl1)
		    (not (equal (apply-k v kl1) (make-val-flimit)))
		    (consp kl2)
		    (<=-kont->fuel (car kl1) (car kl2))
		    (<=-klst->fuel (cdr kl1) (cdr kl2)))
	       (<=-klst->fuel (append (mv-nth 1 (eval-k v (car kl1)))
				       (cdr kl1))
			       (append (mv-nth 1 (eval-k v (car kl2)))
				       (cdr kl2))))
      :disable eval-k-with-more-fuel-1
      :use((:instance eval-k-with-more-fuel-1 (k1 (car kl1)) (k2 (car kl2)))))

      (defun induct-fn (v1 v2 kl1 kl2)
	(declare (xargs :measure (klst-measure kl1)
			:hints(("goal" ; for termination proof
			  :in-theory (disable eval-k-decreases-klst-measure)
			  :use ((:instance eval-k-decreases-klst-measure
					   (v v1) (k (car kl1)) (kl (cdr kl1))))))))
	(if (consp kl1)
	  (induct-fn
	    (mv-nth 0 (mv-list 2 (eval-k v1 (car kl1))))
	    (mv-nth 0 (mv-list 2 (eval-k v2 (car kl2))))
	    (append (mv-nth 1 (mv-list 2 (eval-k v1 (car kl1)))) (cdr kl1))
	    (append (mv-nth 1 (mv-list 2 (eval-k v2 (car kl2)))) (cdr kl2)))
	  kl2))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                    ;;
;; Let's show that addition is associative                            ;;
;;                                                                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; First show that addition using apply-binop is commutative
;; If both x and y are excpt or flimit values, then apply-binop
;;   returns x.  Thus we require that at least one is well formed.
(defrule apply-binop--when-op-is-+-is-commutative
  (implies
    (or  (wf-val-p (apply-binop '+ x y))
	 (wf-val-p (apply-binop '+ y x)))
    (equal (apply-binop '+ x y)
	   (apply-binop '+ y x)))
  :enable apply-binop)

;; Now, try the apply-k version
(defrule apply-k-of-plus-is-commutative
  (let
    ( ( x+y
	(list (make-kont
		:fuel fuel
		:k (make-kont0-expr
		     :expr (make-ast-binop
			     :op '+
			     :left x
			     :right y)))))
      ( y+x
	(list (make-kont
		:fuel fuel
		:k (make-kont0-expr
		     :expr (make-ast-binop
			     :op '+
			     :left y
			     :right x))))))
  (implies
    (and (wf-val-p (apply-k v x+y))
	 (wf-val-p (apply-k v y+x)))
    (equal (apply-k v x+y)
	   (apply-k v y+x))))
  :cases ((wf-val-p v))))

(define ast-eval ((expr ast-p))
  :returns (v val-p)
  :measure (ast-count expr)
  (ast-case expr
    (:integer (make-val-integer :v expr.v))
    (:binop
      (apply-binop
	expr.op
	(ast-eval expr.left)
	(ast-eval expr.right)))))


