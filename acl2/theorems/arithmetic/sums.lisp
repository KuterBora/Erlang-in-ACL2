(in-package "ACL2")
(include-book "arithmetic/top" :dir :system)
(include-book "../erl-eval")


;; There are some useful theorems in eval-theorems.lisp, but I want to improve
;; some of them, so I will not include it.


(set-induction-depth-limit 1)

;; ACL2 add
(define add ((a integerp) (b integerp))
  (b* ((a (ifix a))
       (b (ifix b)))
      (+ a b)))

;; ACL2 sum-n
(define sum-n ((n natp))
  (b* ((n (nfix n))
       ((if (= n 0)) 0))
      (+ n (sum-n (1- n)))))

; Commenting this out, as it introduces rewrite rules that we do not want yet.
; (defrule sum-n-formula
;   (implies (natp n)
;     (equal (sum-n n) (/ (* n (+ n 1)) 2)))
;   :enable (sum-n))


;; Erlang World with the following functions defined locally.
;; - When you run Erlang on the command line, the module is set to 'local.
;;   Normally, functions like add and sum-n would be defined in a different module
;;   which we would have to import (or do a remote call module:call()) but I will
;;   ignore that here for simplicity.
;;
;; add(X, Y) when is_integer(X), is_integer(Y) -> X + Y.
;;
;; sum_n(0) -> 0;
;; sum_n(N) when is_integer(N) -> N + sum-n(N-1).
;;
;;
(define test-w ()
  :returns (w world-p)
  :enabled t
  '((local
      (attrs (module . local)
            (export)
            (import))
      (fn-defns
        (((name . add) (arity . 2))
         ((cases (:var X) (:var Y))
          (guards ((:call is_integer ((:var X))) 
                   (:call is_integer ((:var Y)))))
          (body (:binop
                  + 
                  (:var X) 
                  (:var Y)))))
        (((name . sum_n) (arity . 1))
         ((cases (:integer 0))
          (guards)
          (body (:integer 0)))
         ((cases (:var N))
          (guards ((:call is_integer ((:var N))) 
                   (:binop > (:var N) (:integer 0))))
          (body (:binop 
                  + 
                  (:var N) 
                  (:call sum_n ((:binop - (:var N) (:integer 1))))))))))))


;; Here are some examples of evaluating the functions.

; add(2, 3) -> (:integer 5)
(erl-state->in 
  (apply-k 
    (make-erl-state :world (test-w)) 
      (list 
        (erl-k 
          1000 
          (kont-expr (node-call 'add (list (node-integer 2) (node-integer 3))))))))

; sum_n(5) -> (:integer 15)
(erl-state->in 
  (apply-k 
    (make-erl-state :world (test-w)) 
      (list 
        (erl-k 
          1000 
          (kont-expr (node-call 'sum_n (list (node-integer 5))))))))

; sum_n("cow") -> function_clause
(erl-state->in 
  (apply-k 
    (make-erl-state :world (test-w)) 
    (list 
      (erl-k 
        1000 
        (kont-expr (node-call 'sum-n (list (node-string "cow"))))))))

; sum_n(5) -> out of fuel
(erl-state->in 
  (apply-k 
    (make-erl-state :world (test-w)) 
      (list 
        (erl-k
          1
          (kont-expr (node-call 'sum-n (list (node-integer 5))))))))


stop

;; I defined some helpers to reduce code duplication.

(define wf-state-p ((s erl-state-p))
  :enabled t
  (and (erl-state-p s)
       (let ((kind (erl-val-kind (erl-state->in s))))
            (and (not (equal kind :reject))
                 (not (equal kind :excpt))
                 (not (equal kind :flimit))))))

(define flimit ((s erl-state-p))
  :enabled t
  (and (erl-state-p s)
       (let ((kind (erl-val-kind (erl-state->in s))))
            (equal kind :flimit))))



;; I needed the following lemmas.

; (defrule apply-k-of-step
;   (implies 
;     (and (erl-klst-p klst)
;          (consp klst)
;          (wf-state-p s))
;     (equal (apply-k s klst)
;            (apply-k 
;             (erl-s-klst->s (eval-k (car klst) s)) 
;             (append (erl-s-klst->klst (eval-k (car klst) s)) (cdr klst)))))
;   :expand (apply-k s klst))

(defrule apply-k-of-step
  (implies 
    (and (erl-k-p khead)
         (erl-klst-p ktail)
         (wf-state-p s))
    (equal (apply-k s (cons khead ktail))
           (apply-k
            (erl-s-klst->s (eval-k khead s)) 
            (append (erl-s-klst->klst (eval-k khead s)) ktail))))
  :expand (apply-k s (cons khead ktail)))



(defrule apply-k-of-nil
  (implies (erl-state-p s)
           (equal (apply-k s nil) s))
  :enable apply-k)

(defrule update-state-with-flimit
  (equal (erl-val-kind (erl-state->in (update-erl-state->in s '(:flimit))))
         :flimit)
  :enable update-erl-state->in)
  
(defrule apply-k-of-flimit
  (implies (and (erl-state-p s)
                (equal (erl-val-kind (erl-state->in s)) :flimit))
           (equal (apply-k s klst) s))
  :enable apply-k)

; I certainly need something more general than these. I will get back to that.
(defrule crock-1
  (implies (and (symbolp s) (integerp i))
           (expr-p (node-call s (LIST (node-integer i)))))
  :enable expr-p)

(defrule crock-2
  (implies (and (symbolp s) (integerp a) (integerp b))
           (expr-p (node-call s (LIST (node-integer a) (node-integer b)))))
  :enable expr-p)



;; The theorms

(defrule apply-k-of-add
  (b* (
       ; There is a valid starting state.
       ((unless (wf-state-p s)) t) 
       ((erl-state s) s)

       ; The starting state has the correct world.
       ((unless (equal s.world (test-w))) t)
       
       ; The next continuation calls add(X, Y) with some fuel.
       ((unless (erl-k-p k)) t)
       ((erl-k k) k)

       ((unless
          (equal (kont-kind k.kont) :expr)) t)
        
       ((unless
          (equal (node-kind (kont-expr->expr k.kont)) :call))
          t)
       
       ((unless 
          (equal 'add (node-call->fn (kont-expr->expr k.kont)))) t)

       ((list a b) (node-call->args (kont-expr->expr k.kont)))
       
       ; Result of the function call
       (r (apply-k s (list k)))
       
       ((unless (wf-state-p r)) t)
       
       (a_res (apply-k (update-erl-state->in s '(:none)) (list (erl-k (erl-k->fuel k) (make-kont-expr :expr a)))))
       ((unless (wf-state-p a_res)) t)
       
       (b_res (apply-k (update-erl-state->in s '(:none)) (list (erl-k (erl-k->fuel k) (make-kont-expr :expr b)))))
       ((unless (wf-state-p b_res)) t))
      
        (equal (erl-state->in r) 
               (erl-val-integer (add (erl-val-integer->val (erl-state->in a_res))
                                     (erl-val-integer->val (erl-state->in b_res))))))
  :expand ((eval-k k s)
           
            ))





; (defrule apply-k-of-sum-n
;   (b* (
;        ; There is a valid starting state.
;        ((unless (wf-state-p s)) t) 
;        ((erl-state s) s)

;        ; The starting state has the correct world.
;        ((unless (equal s.world (test-w))) t)
       
;        ; The next continuation calls sum-n(N) with some fuel.
;        ((unless (erl-k-p k)) t)
;        ((erl-k k) k)
;        ((unless (equal k.kont (kont-expr (node-call 'sum_n (list (node-integer i)))))) t)
       
;        ; Result of the function call
;        (r (apply-k s (list k))))
      
;       (implies (and (not (flimit r)) (natp i))
;                (equal (erl-state->in r) (erl-val-integer (sum_n i))))))




(:unop
(make-erl-s-klst
  :s (update-erl-state->in s (make-erl-val-none))
  :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr x.expr))
              (make-erl-k :fuel (1- fuel) :kont (make-kont-unop :op x.op)))))


(defrule foo
  (implies (k is unop)
  
            (equal (eval-k k s)
                    (make-erl-s-klst
                      :s (update-erl-state->in s (make-erl-val-none))
                      :klst (list (make-erl-k :fuel (1- fuel) :kont (make-kont-expr :expr x.expr))
                                  (make-erl-k :fuel (1- fuel) :kont (make-kont-unop :op x.op))))
                    
                    )  
              )

  
  )