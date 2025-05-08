(in-package "ACL2")
(include-book "centaur/fty/top" :DIR :SYSTEM)
(include-book "std/util/top" :DIR :SYSTEM)
(include-book "kestrel/fty/defsubtype" :DIR :SYSTEM)
(set-induction-depth-limit 1)

; require erl-ast, erl-value, erl-kont

;; TODO: maybe have a seperate evaluator for pattern and guard to make proofs easier?

(defines eval-expr
  ; :verify-guards nil
  
  (define eval-exprs ((x expr-list-p) (bind bind-p) (k erl-k-p) (fuel integerp))
    :returns (v erl-value-p)
    :measure (ifix fuel)
    (if (<= (ifix fuel) 0) '(:error bad-ast)
    (cond
      ((null x) '(:error bad-ast))
      ((null (cdr x)) (eval-expr (car x) bind k (ifix (1- (ifix fuel)))))
      (t (eval-expr (car x) bind (make-erl-k-exprs :next (cdr x) :k k) (ifix (1- (ifix fuel))))))))


  (define eval-expr ((x expr-p) (bind bind-p) (k erl-k-p) (fuel integerp))
    :returns (v erl-value-p)
    :measure (ifix fuel)
    (if (<= (ifix fuel) 0)
        '(:error bad-ast)
        (case (node-kind x) 
          (:integer (apply-k x bind k (ifix (1- (ifix fuel))))) ;; should it be (make-erl-value-integer :val (expr-integer->val x))?
          ; :atom (apply-k (expr-atom->val x) bind k)
          ; :string (apply-k (expr-string->val x) bind k)
          ; :nil (apply-k  bind k)
          (:otherwise (apply-k (make-erl-value-atom :val 'other) bind k (ifix (1- (ifix fuel)))))
          ; :cons 
          ; :tuple
          ; :var
          ; :unary-op
          ; :binary-op
          ; :if
          ; :case
          ; :match 
          )))
    
  (define apply-k ((val erl-value-p) (bind bind-p) (k erl-k-p) (fuel integerp))
    :returns (v erl-value-p)
    :measure (ifix fuel)
    (if (<= (ifix fuel) 0) '(:error bad-ast) (case (erl-k-kind k)
      (:init val)
      (:exprs (eval-exprs (erl-k-exprs->next k) bind (erl-k-exprs->k k) (ifix (1- (ifix fuel)))))
      (:otherwise (make-erl-value-atom :val 'other))))))