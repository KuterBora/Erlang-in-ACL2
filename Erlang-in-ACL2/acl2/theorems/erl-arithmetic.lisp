(in-package "ACL2")
(include-book "../erl-eval")
(include-book "erl-baisc")

(set-induction-depth-limit 1)

; Commutativity of Erlang Addition ---------------------------------------------

(defrule apply-k-of-addition-is-commutative-crock-2
  (implies
    (and
      (erl-value-p val)
      (erl-k-list-p rest)
      (erl-k-p k)
      (expr-p left)
      (expr-p right)
      (not (equal val (make-erl-value-fault)))
      (natp fuel))
    (and (erl-k-p (make-erl-k :fuel fuel :kont (make-kont-expr :expr (node-binop '+ left right))))
         (equal (kont-kind (erl-k->kont (make-erl-k :fuel fuel :kont (make-kont-expr :expr (node-binop '+ left right))))) :expr)
         (expr-p (node-binop '+ left right))
         (expr-p (node-binop '+ right left))
         (EQUAL (NODE-KIND (EXPR-FIX (NODE-BINOP '+ LEFT RIGHT))) :BINOP)
         (EQUAL (NODE-KIND (EXPR-FIX (NODE-BINOP '+ LEFT RIGHT))) :BINOP)     
         (equal (node-kind (kont-expr->expr (erl-k->kont (make-erl-k :fuel fuel :kont (make-kont-expr :expr (node-binop '+ left right)))))) :binop)
         (equal (node-kind (kont-expr->expr (erl-k->kont (make-erl-k :fuel fuel :kont (make-kont-expr :expr (node-binop '+ right left)))))) :binop)
         ))
  :expand ((expr-p (node-binop '+ left right))
           (expr-p (node-binop '+ right left))))


(defrule apply-k-of-addition-is-commutative-crock-3
  (implies
    (and
      (erl-value-p val)
      (erl-k-list-p rest)
      (erl-k-p k)
      (expr-p right)
      (expr-p left)
      (not (equal val (make-erl-value-fault)))
      (natp fuel)
      (> fuel 3))
    (equal 
      (apply-k val (cons (make-erl-k :fuel fuel :kont (make-kont-expr :expr (node-binop '+ left right))) rest))
      (apply-k
        (apply-erl-binop
          '+
          (apply-k '(:nil) (list (erl-k (+ -1 fuel) (kont-expr left))))
          (apply-k '(:nil) (list (erl-k (+ -2 fuel) (kont-expr right)))))
        rest))))
      
(defrule apply-k-of-binop-ensures-2
  (implies 
    (and
      (erl-value-p val)
      (erl-k-list-p rest)
      (expr-p right)
      (expr-p left)
      (erl-k-p k)
      (not (equal (apply-k val (cons (make-erl-k :fuel fuel :kont (make-kont-expr :expr (node-binop '+ left right))) rest)) '(:fault)))
      (natp fuel)
      (> fuel 3)
      (not (equal val (make-erl-value-fault))))
    (and (not (equal (apply-k '(:nil) (list (erl-k (+ -1 fuel) (kont-expr left)))) '(:fault)))    
         (not (equal (apply-k '(:nil) (list (erl-k (+ -2 fuel) (kont-expr right)))) '(:fault)))
         ))
    :disable (apply-k-of-binop-ensures)
    :use (
        (:instance apply-k-of-binop-ensures
        (val val)
        (rest rest)
        (k (make-erl-k :fuel fuel :kont (make-kont-expr :expr (node-binop '+ left right)))))
        )
    )


(defrule apply-binop-of-erl-addition-is-commutative
  (implies
    (and
      (erl-value-p right)
      (erl-value-p left))
    (equal 
      (apply-erl-binop '+ left right)
      (apply-erl-binop '+ right left)))
    :enable apply-erl-binop)



(defrule apply-k-of-addition-is-commutative
  (implies
    (and
      (erl-value-p val)
      (erl-k-list-p rest)
      (erl-k-p k)
      (expr-p right)
      (expr-p left)
      (not (equal val (make-erl-value-fault)))
      (not (equal (apply-k val (cons (make-erl-k :fuel fuel :kont (make-kont-expr :expr (node-binop '+ left right))) rest)) '(:fault)))
      (natp fuel)
      (> fuel 3))
    (equal 
      (apply-k val (cons (make-erl-k :fuel fuel :kont (make-kont-expr :expr (node-binop '+ left right))) rest))
      (apply-k val (cons (make-erl-k :fuel (+ 2 fuel) :kont (make-kont-expr :expr (node-binop '+ right left))) rest))))
    :disable (apply-k-of-binop-ensures-2 more-fuel-is-good-for-apply)
    :enable increase-fuel
    :hints (
      ("Goal''" :use (:instance apply-k-of-binop-ensures-2
        (val val)
        (rest rest)
        (left left)
        (right right)
        (k k)
        (fuel fuel)))
      ("Goal'5'" :use (
          (:instance more-fuel-is-good-for-apply
            (val '(:nil))
            (klst (LIST (ERL-K (+ -1 FUEL) (KONT-EXPR LEFT))))
            (z 1))
          (:instance more-fuel-is-good-for-apply
            (val '(:nil))
            (klst (LIST (ERL-K (+ -2 FUEL) (KONT-EXPR RIGHT))))
            (z 3))))))

(defun-sk exists-fuel-for-commutative-erl-addition (v x y f rest)
  (exists (f2)
    (implies
      (and (expr-p x)
           (expr-p y)
           (erl-value-p v)
           (natp f)
           (> f 3)
           (erl-k-list-p rest)
           (not (equal v '(:fault)))
           (not (equal (apply-k v (cons (make-erl-k :fuel f :kont (make-kont-expr :expr (node-binop '+ x y))) rest)) '(:fault))))
      (and (not (equal (apply-k v (cons (make-erl-k :fuel f2 :kont (make-kont-expr :expr (node-binop '+ y x))) rest)) '(:fault)))
           (equal (apply-k v (cons (make-erl-k :fuel f  :kont (make-kont-expr :expr (node-binop '+ x y))) rest))
                  (apply-k v (cons (make-erl-k :fuel f2 :kont (make-kont-expr :expr (node-binop '+ y x))) rest)))))))

(defrule apply-k-of-addition-is-commutative-sk
  (implies (erl-k-p k)
           (exists-fuel-for-commutative-erl-addition v x y f rest))
  :disable apply-k-of-addition-is-commutative
  :hints (("Goal"
            :use ((:instance EXISTS-FUEL-FOR-COMMUTATIVE-ERL-ADDITION-SUFF
                    (v v)
                    (x x)
                    (y y)
                    (f f)
                    (rest rest)
                    (f2 (+ 2 f)))
                  (:instance apply-k-of-addition-is-commutative
                      (val v)
                      (rest rest)
                      (left x)
                      (right y)
                      (fuel f)
                      (k k))))
                      ))