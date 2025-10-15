(in-package "ACL2")
(include-book "erl-eval")

(set-induction-depth-limit 1)

; Erlang Binop -----------------------------------------------------------------

; apply-k-of-binop returns fault if eval-k returns fault
(local (defrule apply-k-of-binop-crock-1
  (implies
    (and (equal (erl-val-klst->v (eval-k k val)) '(:fault))
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop)
         (< 3 (erl-k->fuel k)))
  (equal
    (apply-k 
      (apply-erl-binop
        (node-binop->op (kont-expr->expr (erl-k->kont k)))
        (apply-k '(:nil) (list (erl-k (+ -1 (erl-k->fuel k)) 
                                      (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))))
        (apply-k '(:nil) (list (erl-k (+ -2 (erl-k->fuel k)) 
                                      (kont-expr (node-binop->right (kont-expr->expr (erl-k->kont k))))))))
      rest)
    '(:fault)))
  :enable eval-k))

; apply-erl-binop with a fault argument returns fault
(local (defrule apply-k-of-binop-crock-2
  (and (equal (apply-erl-binop op1 l '(:fault)) '(:fault))
       (equal (apply-erl-binop op2 '(:fault) r) '(:fault)))
  :enable apply-erl-binop))

; Reveal the first step of binop evaluation.
(local (defruled apply-k-of-binop-crock-3
  (implies
    (and (erl-val-p val)
         (erl-klst-p rest)
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop)
         (not (equal val '(:fault)))
         (< 3 (erl-k->fuel k)))
    (equal (apply-k val (cons k rest))
           (apply-k
              (apply-k 
                '(:nil)
                (list
                  (erl-k (+ -1 (erl-k->fuel k))
                         (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))
                  (erl-k (+ -1 (erl-k->fuel k))
                          (kont-binop-expr1 (node-binop->op (kont-expr->expr (erl-k->kont k)))
                                            (node-binop->right (kont-expr->expr (erl-k->kont k)))
                                            nil))))
              rest)))
  :disable apply-k-of-append
  :enable eval-k
  :expand (apply-k val (list k))
  :use ((:instance apply-k-of-append (klst1 (list k)) (klst2 rest) (klst (cons k rest)) (val val)))))

; Reveal the second step of binop evaluation.
(local (defruled apply-k-of-binop-crock-4
  (implies
    (and (erl-val-p val)
         (erl-klst-p rest)
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop)
         (not (equal val '(:fault)))
         (< 3 (erl-k->fuel k)))
    (equal (apply-k val (cons k rest))
           (apply-k
            (apply-k
              (apply-k '(:nil) (list (erl-k (+ -1 (erl-k->fuel k))
                                            (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))))
              (list (erl-k (+ -1 (erl-k->fuel k))
                           (kont-binop-expr1
                              (node-binop->op (kont-expr->expr (erl-k->kont k)))
                              (node-binop->right (kont-expr->expr (erl-k->kont k)))
                              nil))))
            rest)))
  :use ((:instance apply-k-of-append
            (klst1 (list (erl-k (+ -1 (erl-k->fuel k)) (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k))))))) 
            (klst2 (list (erl-k (+ -1 (erl-k->fuel k))
                                (kont-binop-expr1 (node-binop->op (kont-expr->expr (erl-k->kont k)))
                                                  (node-binop->right (kont-expr->expr (erl-k->kont k)))
                                nil)))) 
            (klst (list (erl-k (+ -1 (erl-k->fuel k))
                               (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))
                        (erl-k (+ -1 (erl-k->fuel k))
                               (kont-binop-expr1 (node-binop->op (kont-expr->expr (erl-k->kont k)))
                                                 (node-binop->right (kont-expr->expr (erl-k->kont k)))
                              nil)))) 
            (val '(:nil)))
        (:instance apply-k-of-binop-crock-3 (val val) (rest rest) (k k)))))


; Nested faults in the binop continutaion return fault.
(local (defrule apply-k-binop-of-fault
  (equal 
    (apply-k 
      val 
      (list (erl-k fuel 
                  (kont-binop-expr2 op '(:fault) nil))))
    '(:fault))
  :enable eval-k
  :expand 
    (apply-k 
      val 
      (list (erl-k fuel (kont-binop-expr2 op '(:fault) nil))))))

; Nested faults during binop evaulation return fault.
(local (defrule apply-k-of-binop-crock-5
  (implies
    (and (equal (apply-k val (cons k rest)) '(:fault))
         (erl-val-p val)
         (erl-klst-p rest)
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop)
         (not (equal val '(:fault)))
         (< 3 (erl-k->fuel k)))
    (equal
      (apply-k
        (apply-k 
          '(:nil)
          (list (erl-k (+ -2 (erl-k->fuel k))
                       (kont-expr (node-binop->right (kont-expr->expr (erl-k->kont k)))))
                (erl-k (+ -2 (erl-k->fuel k))
                       (kont-binop-expr2 (node-binop->op (kont-expr->expr (erl-k->kont k)))
                                         '(:fault)
                                         nil))))
        rest) 
      '(:fault)))
  :use ((:instance apply-k-of-append 
    (val '(:nil))
    (klst1 (list (erl-k (+ -2 (erl-k->fuel k))
                        (kont-expr (node-binop->right (kont-expr->expr (erl-k->kont k)))))))
    (klst2 (list (erl-k (+ -2 (erl-k->fuel k))
                        (kont-binop-expr2 (node-binop->op (kont-expr->expr (erl-k->kont k)))
                                          '(:fault)
                                          nil))))
    (klst (list (erl-k (+ -2 (erl-k->fuel k))
                       (kont-expr (node-binop->right (kont-expr->expr (erl-k->kont k)))))
                (erl-k (+ -2 (erl-k->fuel k))
                       (kont-binop-expr2 (node-binop->op (kont-expr->expr (erl-k->kont k)))
                                          '(:fault)
                                          nil))))))))

; Reveal the third step of binop evaluation.
(local (defruled apply-k-of-binop-crock-6
  (implies
    (and (erl-val-p val)
         (erl-klst-p rest)
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop)
         (not (equal val '(:fault)))
         (< 3 (erl-k->fuel k)))
    (equal (apply-k val (cons k rest))
           (apply-k
            (apply-k
              '(:nil)
              (list (erl-k (+ -2 (erl-k->fuel k))
                           (kont-expr (node-binop->right (kont-expr->expr (erl-k->kont k)))))
                    (erl-k (+ -2 (erl-k->fuel k))
                           (kont-binop-expr2
                              (node-binop->op (kont-expr->expr (erl-k->kont k)))
                              (apply-k '(:nil) (list (erl-k (+ -1 (erl-k->fuel k)) 
                                                            (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))))
                              nil))))
            rest)))
  :enable eval-k
  :use (:instance apply-k-of-binop-crock-4 (val val) (rest rest) (k k))
  :expand 
    (:free (v) 
      (apply-k v (list (erl-k (+ -1 (erl-k->fuel k))
                              (kont-binop-expr1 (node-binop->op (kont-expr->expr (erl-k->kont k)))
                                                (node-binop->right (kont-expr->expr (erl-k->kont k)))
                                                nil)))))))

; Reveal the fourth step of binop evaluation.
(local (defruled apply-k-of-binop-crock-7
  (implies
    (and (erl-val-p val)
         (erl-klst-p rest)
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop)
         (not (equal val '(:fault)))
         (< 3 (erl-k->fuel k)))
    (equal (apply-k val (cons k rest))
           (apply-k
            (apply-k
              (apply-k '(:nil) (list (erl-k (+ -2 (erl-k->fuel k)) 
                                            (kont-expr (node-binop->right (kont-expr->expr (erl-k->kont k)))))))
              (list (erl-k (+ -2 (erl-k->fuel k))
                           (kont-binop-expr2
                              (node-binop->op (kont-expr->expr (erl-k->kont k)))
                              (apply-k '(:nil) (list (erl-k (+ -1 (erl-k->fuel k)) 
                                                            (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))))
                              nil))))
            rest)))
  :use ((:instance apply-k-of-binop-crock-6 (val val) (rest rest) (k k))
        (:instance apply-k-of-append 
          (val '(:nil))
          (klst1 (list (erl-k (+ -2 (erl-k->fuel k)) 
                              (kont-expr (node-binop->right (kont-expr->expr (erl-k->kont k)))))))
          (klst2 (list (erl-k (+ -2 (erl-k->fuel k))
                           (kont-binop-expr2
                              (node-binop->op (kont-expr->expr (erl-k->kont k)))
                              (apply-k '(:nil) (list (erl-k (+ -1 (erl-k->fuel k)) 
                                                            (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))))
                              nil))))
          (klst (list (erl-k (+ -2 (erl-k->fuel k)) 
                             (kont-expr (node-binop->right (kont-expr->expr (erl-k->kont k)))))
                      (erl-k (+ -2 (erl-k->fuel k))
                             (kont-binop-expr2
                              (node-binop->op (kont-expr->expr (erl-k->kont k)))
                              (apply-k '(:nil) (list (erl-k (+ -1 (erl-k->fuel k)) 
                                                            (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))))
                              nil))))))))

; apply-k of a binop is equivalent to evaluating the left and right expressions 
; and then applying the binop.
(defrule apply-k-of-binop
  (implies
    (and (erl-val-p val)
         (erl-klst-p rest)
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop)
         (not (equal val (make-erl-val-fault)))
         (> (erl-k->fuel k) 3))
    (equal 
      (apply-k val (cons k rest))
      (apply-k
        (apply-erl-binop
          (node-binop->op (kont-expr->expr (erl-k->kont k)))
          (apply-k '(:nil) (list (erl-k (+ -1 (erl-k->fuel k)) 
                                        (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))))
          (apply-k '(:nil) (list (erl-k (+ -2 (erl-k->fuel k)) 
                                        (kont-expr (node-binop->right(kont-expr->expr (erl-k->kont k))))))))
        rest)))
    :use (:instance apply-k-of-binop-crock-7 (val val) (rest rest) (k k))
    :enable eval-k
    :expand (apply-k
              (apply-k '(:nil) (list (erl-k (+ -2 (erl-k->fuel k)) 
                                            (kont-expr (node-binop->right (kont-expr->expr (erl-k->kont k)))))))
              (list (erl-k (+ -2 (erl-k->fuel k))
                           (kont-binop-expr2
                              (node-binop->op (kont-expr->expr (erl-k->kont k)))
                              (apply-k '(:nil) (list (erl-k (+ -1 (erl-k->fuel k)) 
                                                            (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k)))))))
                              nil)))))

; if apply-k of a binop does not return fault for some fuel, then the subexpressions
; also do not return fault when evaluated with their according fuel. 
(defrule apply-k-of-binop-ensures
  (implies 
    (and (erl-val-p val)
         (erl-klst-p rest)
         (erl-k-p k)
         (equal (kont-kind (erl-k->kont k)) :expr)
         (equal (node-kind (kont-expr->expr (erl-k->kont k))) :binop)
         (not (equal (apply-k val (cons k rest)) (make-erl-val-fault)))
         (> (erl-k->fuel k) 3)
         (not (equal val (make-erl-val-fault))))
    (and (not (equal (apply-k '(:nil) (list (erl-k (+ -1 (erl-k->fuel k)) 
                                                   (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k))))))) 
                     (make-erl-val-fault)))    
         (not (equal (apply-k '(:nil) (list (erl-k (+ -2 (erl-k->fuel k)) 
                                                   (kont-expr (node-binop->right(kont-expr->expr (erl-k->kont k)))))))
                     (make-erl-val-fault)))))  
    :disable apply-erl-binop-of-fault
    :use ((:instance apply-erl-binop-of-fault
      (op (node-binop->op (kont-expr->expr (erl-k->kont k))))
      (left (apply-k '(:nil) (list (erl-k (+ -1 (erl-k->fuel k)) 
                                          (kont-expr (node-binop->left (kont-expr->expr (erl-k->kont k))))))))
      (right (apply-k '(:nil) (list (erl-k (+ -2 (erl-k->fuel k)) 
                                           (kont-expr (node-binop->right(kont-expr->expr (erl-k->kont k)))))))))))   

; If (op left right) is a valid erl-binop expression, then (op right left) is 
; also a valid erl-binop expression.
(defrule erl-binop-valid-expression
  (implies
    (and (erl-klst-p rest)
         (expr-p left)
         (expr-p right)
         (erl-binop-p op)
         (natp fuel))
    (and (erl-k-p (make-erl-k :fuel fuel :kont (make-kont-expr :expr (node-binop op left right))))
         (equal (kont-kind (erl-k->kont (make-erl-k :fuel fuel 
                                                    :kont (make-kont-expr :expr (node-binop op left right))))) 
                :expr)
         (expr-p (node-binop op left right))
         (expr-p (node-binop op right left))
         (EQUAL (NODE-KIND (EXPR-FIX (NODE-BINOP op LEFT RIGHT))) :BINOP)
         (EQUAL (NODE-KIND (EXPR-FIX (NODE-BINOP op LEFT RIGHT))) :BINOP)     
         (equal (node-kind (kont-expr->expr (erl-k->kont (make-erl-k :fuel fuel 
                                                                     :kont (make-kont-expr :expr (node-binop op left right)))))) 
                :binop)
         (equal (node-kind (kont-expr->expr (erl-k->kont (make-erl-k :fuel fuel 
                                                                     :kont (make-kont-expr :expr (node-binop op right left)))))) 
                :binop)))
  :expand ((expr-p (node-binop op left right))
           (expr-p (node-binop op right left))))

      
; Simplify apply-k-of-binop-ensures for use hints
(local (defrule apply-k-of-binop-ensures-simplified
  (implies 
    (and (erl-val-p val)
         (erl-klst-p rest)
         (expr-p right)
         (expr-p left)
         (not (equal (apply-k val (cons (make-erl-k :fuel fuel 
                                                    :kont (make-kont-expr :expr (node-binop '+ left right))) rest)) 
                     '(:fault)))
         (natp fuel)
         (> fuel 3)
         (not (equal val (make-erl-val-fault))))
    (and (not (equal (apply-k '(:nil) (list (erl-k (+ -1 fuel) (kont-expr left)))) '(:fault)))    
         (not (equal (apply-k '(:nil) (list (erl-k (+ -2 fuel) (kont-expr right)))) '(:fault)))))
    :disable (apply-k-of-binop-ensures)
    :use ((:instance apply-k-of-binop-ensures
            (val val)
            (rest rest)
            (k (make-erl-k :fuel fuel :kont (make-kont-expr :expr (node-binop '+ left right))))))))

