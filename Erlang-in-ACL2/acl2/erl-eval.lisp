(in-package "ACL2")
(include-book "centaur/fty/top" :DIR :SYSTEM)
(include-book "std/util/top" :DIR :SYSTEM)
(include-book "kestrel/fty/defsubtype" :DIR :SYSTEM)
(set-induction-depth-limit 1)

; require erl-ast, erl-value, erl-kont
(ld "erl-ast.lisp")
(ld "erl-value.lisp")
(ld "erl-kont.lisp")
(ld "eval-theorems.lisp")

;; TODO: maybe have a seperate evaluator for pattern and guard to make proofs easier?

;; Erlang Evaluator

(defines eval-expr
  (define eval-expr ((x expr-p) (k erl-k-p) (fuel natp))
    :returns (v erl-value-p)
    :measure (nfix fuel)
    (b* ((x (expr-fix x))
         (k (erl-k-fix k))
         (fuel (nfix fuel))
         ((if (<= fuel 0)) '(:error out-of-fuel)))
        (case (node-kind x) 
              (:integer (apply-k x k (1- fuel)))
              (:atom (apply-k x k (1- fuel)))
              (:string (apply-k x k (1- fuel)))
              (:binary-op
                (let ((op (node-binary-op->op x))
                      (expr1 (node-binary-op->left x))
                      (expr2 (node-binary-op->right x))) 
                     (eval-expr expr1 
                                (make-erl-k-binary-op-expr1 :op op 
                                                            :expr2 expr2 
                                                            :k k)
                                (1- fuel))))
              (otherwise (apply-k '(:error bad-ast) k (1- fuel))))))
    
  (define apply-k ((val erl-value-p) (k erl-k-p) (fuel integerp))
    :returns (v erl-value-p)
    :measure (nfix fuel)
    (b* ((val (erl-value-fix val))
         (k (erl-k-fix k))
         (fuel (ifix fuel))
         ((if (<= fuel 0)) '(:error out-of-fuel)))
        (case (erl-k-kind k)
              (:init val)
              (:binary-op-expr1
                (let ((op (erl-k-binary-op-expr1->op k))
                      (expr2 (erl-k-binary-op-expr1->expr2 k))
                      (next-k (erl-k-binary-op-expr1->k k)))
                     (eval-expr expr2
                                (make-erl-k-binary-op-expr2 :op op
                                                            :result val 
                                                            :k next-k)
                                (1- fuel))))
              (:binary-op-expr2
                (let ((op (erl-k-binary-op-expr2->op k))
                      (left-val (erl-k-binary-op-expr2->result k))
                      (next-k (erl-k-binary-op-expr2->k k)))
                     (case op
                      (+ (if (and (equal (erl-value-kind val) :integer)
                                  (equal (erl-value-kind left-val) :integer))
                             (apply-k (make-erl-value-integer :val (+ (erl-value-integer->val left-val)
                                                                      (erl-value-integer->val val))) 
                                      next-k 
                                      (1- fuel))
                             (apply-k '(:error bad-type) next-k (1- fuel))))
                      (* (if (and (equal (erl-value-kind val) :integer)
                                  (equal (erl-value-kind left-val) :integer))
                             (apply-k (make-erl-value-integer :val (* (erl-value-integer->val left-val)
                                                                      (erl-value-integer->val val))) 
                                      next-k 
                                      (1- fuel))
                             (apply-k '(:error bad-type) next-k (1- fuel))))
                      (- (if (and (equal (erl-value-kind val) :integer)
                                  (equal (erl-value-kind left-val) :integer))
                             (apply-k (make-erl-value-integer :val (- (erl-value-integer->val left-val)
                                                                      (erl-value-integer->val val))) 
                                      next-k 
                                      (1- fuel))
                             (apply-k '(:error bad-type) next-k (1- fuel))))
                      (div (if (and (equal (erl-value-kind val) :integer)
                                    (equal (erl-value-kind left-val) :integer)
                                    (> (erl-value-integer->val val) 0))
                               (apply-k (make-erl-value-integer :val (ifix (/ (erl-value-integer->val left-val)
                                                                              (erl-value-integer->val val)))) 
                                        next-k 
                                        (1- fuel))
                               (apply-k '(:error bad-type) next-k (1- fuel))))
                      (otherwise '(:error bad-op)))))
              (otherwise '(:error bad-kont))))))

;; ============================================================================================
;; (list :binary-op-expr1 op expr2 nil k)

; :verify-guards nil
; (:exprs (eval-exprs (erl-k-exprs->next k) bind (erl-k-exprs->k k) (ifix (1- (ifix fuel)))))
;     (if (<= (ifix fuel) 0)
;        '(:error bad-ast)

  ; (define eval-exprs ((x expr-list-p) (bind bind-p) (k erl-k-p) (fuel integerp))
  ;   :returns (v erl-value-p)
  ;   :measure (ifix fuel)
  ;   (if (<= (ifix fuel) 0) '(:error bad-ast)
  ;   (cond
  ;     ((null x) '(:error bad-ast))
  ;     ((null (cdr x)) (eval-expr (car x) bind k (ifix (1- (ifix fuel)))))
  ;     (t (eval-expr (car x) bind (make-erl-k-exprs :next (cdr x) :k k) (ifix (1- (ifix fuel))))))))


;; Example AST

'(:integer 1)
'(:unary-op - (:integer 1))
'(:binary-op + (:integer 1) (:integer 2))
'(:binary-op + (:binary-op * (:integer 3) (:integer 4)) (:integer 2))
'(:if  (((cases) (guards (:atom true)) (body :atom true))
        ((cases) (guards (:atom true)) (body :atom false))))

; clause
'((CASES (:INTEGER 2) (:INTEGER 3))
  (GUARDS)
  (BODY :INTEGER 1))


;; Evaluation examples
(eval-expr '(:integer 1) '(:init) 100)
(eval-expr '(:atom abc) '(:init) 100)
(eval-expr '(:string "abc") '(:init) 100)
(eval-expr '(:binary-op + (:integer 1) (:integer 2)) '(:init) 100)
(eval-expr '(:binary-op + (:binary-op * (:integer 3) (:integer 4)) (:integer 2))
           '(:init)
           100)

(eval-expr '(:binary-op div (:integer 10) (:integer 2)) '(:init) 100)
(eval-expr '(:binary-op div (:integer 3) (:integer 2)) '(:init) 100)




;;; Erlang Addition 

(defrule stupid-1
  (implies (and (node-p x)
                (equal (node-kind x) :binary-op)
                (equal (node-kind (node-binary-op->left x)) :integer)
                (equal (node-kind (node-binary-op->right x)) :integer))
           (expr-p x))
  :expand (expr-p x))


(defrule stupid-2
  (implies (and (node-p x)
                (equal (node-kind x) :binary-op)
                (equal (node-kind (node-binary-op->left x)) :integer)
                (equal (node-kind (node-binary-op->right x)) :integer))
            (equal (node-kind (expr-fix x)) :binary-op))
  :expand ((node-kind x) (expr-fix x)))

(defrule stupid-3
  (implies (and (node-p x)
                (equal (node-kind x) :binary-op)
                (equal (node-kind (node-binary-op->left x)) :integer)
                (equal (node-kind (node-binary-op->right x)) :integer))
           (and (equal (erl-value-kind (node-binary-op->right x)) :integer)
                (equal (erl-value-kind (node-binary-op->left x)) :integer)))
  :expand (node-kind x)
  :enable erl-value-kind)


(defrule stupid-4
  (IMPLIES (AND (EQUAL (NODE-KIND X) :INTEGER)
                (NODE-P X))
           (EQUAL (ERL-VALUE-KIND X) :INTEGER))
  :expand ((node-kind x) (erl-value-kind x)))

(defrule stupid-5
  (IMPLIES (AND (EQUAL (NODE-KIND X) :INTEGER)
                (NODE-P X))
           (and (erl-value-p x)
                (equal (node-integer->val x)
                       (erl-value-integer->val x))))
 :expand ((node-integer->val x) (erl-value-integer->val x)))


(defrule erl-addition-init
  (implies (and (expr-p x)
                (expr-p y)
                (integerp fuel)
                (> fuel 5)
                (equal (node-kind x) :integer)
                (equal (node-kind y) :integer)
                (equal z (make-node-binary-op :op '+ :left x :right y)))
          (equal (erl-value-integer->val (eval-expr z '(:init) fuel))
                 (+ (node-integer->val x) (node-integer->val y))))
  :expand ((eval-expr z '(:init) fuel)
           (eval-expr (node-binary-op->left z) 
                      (ERL-K-BINARY-OP-EXPR1 '+
                                             (NODE-BINARY-OP->RIGHT Z)
                                             NIL
                                             '(:INIT)) 
                      (- fuel 1))
           (APPLY-K (NODE-BINARY-OP->LEFT Z)
                    (ERL-K-BINARY-OP-EXPR1 '+
                                           (NODE-BINARY-OP->RIGHT Z)
                                           NIL
                                          '(:INIT))
                    (- fuel 2))
           (EVAL-EXPR (NODE-BINARY-OP->RIGHT Z)
                      (ERL-K-BINARY-OP-EXPR2 '+
                                             (NODE-BINARY-OP->LEFT Z)
                                             NIL 
                                             '(:INIT))
                      (- fuel 3))
           
           (APPLY-K (NODE-BINARY-OP->RIGHT Z)
                    (ERL-K-BINARY-OP-EXPR2 '+
                                           (NODE-BINARY-OP->LEFT Z)
                                           NIL
                                           '(:INIT))
                    (- fuel 4))
          (APPLY-K (ERL-VALUE-INTEGER
                      (+ (ERL-VALUE-INTEGER->VAL (NODE-BINARY-OP->LEFT Z))
                         (ERL-VALUE-INTEGER->VAL (NODE-BINARY-OP->RIGHT Z))))
                 '(:INIT)
                 (- fuel 5))))


(defrule erl-addition-init-is-commutative-lemma-1
  (implies (and (expr-p x)
                (expr-p y)
                (integerp fuel)
                (> fuel 5)
                (equal (node-kind x) :integer)
                (equal (node-kind y) :integer)
                (equal z1 (make-node-binary-op :op '+ :left x :right y))
                (equal z2 (make-node-binary-op :op '+ :left y :right x)))
        (equal (erl-value-integer->val (eval-expr z1 '(:init) fuel))
               (erl-value-integer->val (eval-expr z2 '(:init) fuel)))))

(defrule why
  (implies (EQUAL (+ 1 (LEN (CDDR X))) 1)
           (equal (len (cddr x)) 0)))

(defrule why-2
  (iff (equal x nil)
       (and (true-listp x) (equal (len x) 0))))

(defrule why-3
  (implies (and (EQUAL (+ 1 (LEN (CDDR X))) 1)
                (TRUE-LISTP (CDDR X)))
           (not (cddr x)))
  :hints (("Goal" :use ((:instance why
                          (x x))
                         (:instance why-2
                          (x (cddr x)))))))

(defrule very-stupid-1
  (implies (and (node-p x)
                (equal (car x) :integer))
           (integerp (cadr x)))
  :expand (node-p x))

(defrule very-stupid-2
  (implies (and (node-p x) 
                (equal (node-kind x) :integer))
           (equal (car x) :integer))
  :rule-classes (:forward-chaining))


(defrule very-stupid-3
  (IMPLIES (AND (NODE-P X)
              (equal (car x) :integer)
              (EQUAL (NODE-KIND X) :INTEGER))
           (NOT (CDDR X)))
  :expand (node-p x)
  :hints (("Goal" :use ((:instance very-stupid-2
                          (x x))))))






(defthmr erl-addition-is-init-commutative-lemma-2
  (implies (and (node-p x)
                (node-p y)
                (equal (node-kind x) :integer)
                (equal (node-kind y) :integer)
                (equal (erl-value-integer->val x)
                       (erl-value-integer->val y)))
           (equal x y))
  :hints (("Goal" :expand ((erl-value-integer->val x) (erl-value-integer->val y)))))


