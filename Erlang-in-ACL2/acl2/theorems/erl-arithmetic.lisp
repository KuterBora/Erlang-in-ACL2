(in-package "ACL2")
(include-book "../erl-eval")
(include-book "erl-baisc")

(set-induction-depth-limit 1)

; TODO: This file is way behind, it needs to be updated.

; Commutativity of Erlang Addition ---------------------------------------------

; Apply-binop of erl-addition is commutative.
(local (defrule apply-binop-of-erl-addition-is-commutative
  (implies
    (and (erl-val-p right)
         (erl-val-p left))
    (equal (apply-erl-binop '+ left right)
          (apply-erl-binop '+ right left)))
  :enable apply-erl-binop))


; Proves that increasing fuel by 2 will alwayas make apply-k of erl-additon is commutative.
; This is needed for the case where left has just enough fuel to evalute without fault, 
; in which case the commutative evaluation would fail unless fuel is increased by at least 2.
(defrule apply-k-of-addition-is-commutative-witness
  (implies
    (and (erl-val-p val)
         (erl-klst-p rest)
         (expr-p right)
         (expr-p left)
         (not (equal val (make-erl-val-fault)))
         (not (equal (apply-k val (cons (make-erl-k :fuel fuel 
                                                    :kont (make-kont-expr :expr (node-binop '+ left right))) rest)) 
                      '(:fault)))
         (natp fuel)
         (> fuel 3))
    (equal 
      (apply-k val (cons (make-erl-k :fuel fuel 
                                     :kont (make-kont-expr :expr (node-binop '+ left right))) rest))
      (apply-k val (cons (make-erl-k :fuel (+ 2 fuel) 
                                     :kont (make-kont-expr :expr (node-binop '+ right left))) rest))))
    :disable (apply-k-of-binop-ensures-simplified more-fuel-is-good-for-apply)
    :enable increase-fuel
    :use ((:instance apply-k-of-binop-ensures-simplified
            (val val)
            (rest rest)
            (left left)
            (right right)
            (fuel fuel))
          (:instance more-fuel-is-good-for-apply
                (val '(:nil))
                (klst (list (erl-k (+ -1 fuel) (kont-expr left))))
                (n 1))
          (:instance more-fuel-is-good-for-apply
                (val '(:nil))
                (klst (list (erl-k (+ -2 fuel) (kont-expr right))))
                (n 3))))

; Skolem function that states: forall expressions x, y, if there exists a natp that
; is enough fuel to evaluate (+ x y), then there exists a natp that is enough fuel
; to evaluate (+ y x). 
(defun-sk exists-fuel-for-commutative-erl-addition (v x y f rest)
  (exists (f2)
    (implies
      (and (expr-p x)
           (expr-p y)
           (erl-val-p v)
           (natp f)
           (> f 3)
           (erl-klst-p rest)
           (not (equal v '(:fault)))
           (not (equal (apply-k v (cons (make-erl-k :fuel f :kont (make-kont-expr :expr (node-binop '+ x y))) rest)) '(:fault))))
      (and (not (equal (apply-k v (cons (make-erl-k :fuel f2 :kont (make-kont-expr :expr (node-binop '+ y x))) rest)) '(:fault)))
           (equal (apply-k v (cons (make-erl-k :fuel f  :kont (make-kont-expr :expr (node-binop '+ x y))) rest))
                  (apply-k v (cons (make-erl-k :fuel f2 :kont (make-kont-expr :expr (node-binop '+ y x))) rest)))))))

; If an erl-additon expression can be evaluated without fault, then there
; exists enough fuel that makes the expression commutative.
(defrule apply-k-of-addition-is-commutative
  (implies (erl-k-p k)
           (exists-fuel-for-commutative-erl-addition v x y f rest))
  :disable apply-k-of-addition-is-commutative-witness
  :use ((:instance exists-fuel-for-commutative-erl-addition-suff
          (v v)
          (x x)
          (y y)
          (f f)
          (rest rest)
          (f2 (+ 2 f)))
        (:instance apply-k-of-addition-is-commutative-witness
            (val v)
            (rest rest)
            (left x)
            (right y)
            (fuel f))))