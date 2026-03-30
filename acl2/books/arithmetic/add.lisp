(in-package "ACL2")
(include-book "../../erl-eval")
(include-book "../../theorems/top")

(set-induction-depth-limit 1)

;; ACL2 add
(define add ((a integerp) (b integerp))
  (b* ((a (ifix a))
       (b (ifix b)))
      (+ a b)))

;; Erlang World with the following functions defined locally.
;; - When you run Erlang on the command line, the module is set to 'local.
;;   Normally, functions like add and would be defined in a different module
;;   which we would have to import (or do a remote call m:f()) but I will
;;   ignore that here for simplicity.
;;
;; add(X, Y) when is_integer(X), is_integer(Y) -> X + Y.
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
          (guards ((:call is_integer (:cons (:var X) (:nil))) 
                   (:call is_integer (:cons (:var Y) (:nil)))))
          (body (:binop
                  + 
                  (:var X) 
                  (:var Y)))))))))


(in-theory (disable apply-k-of-step apply-k-of-consp))

(defrule apply-k-of-add
  (b* (((unless (wf-state-p s)) t) 
       ((erl-state s) s)

       ; The starting state has the correct world.
       ((unless (equal s.world (test-w))) t)

       ; The starting state has the correct module.
       ((unless (equal s.module 'local)) t)
       
       ; The next continuation calls add(X, Y) with some fuel.
       ((unless (erl-k-p k)) t)
       ((erl-k k) k)
       ((unless (> k.fuel 10000000)) t)

       ((unless (equal (kont-kind k.kont) :expr)) t)
       ((unless (equal (node-kind (kont-expr->expr k.kont)) :call)) t)
       ((unless (equal 'add (node-call->fn (kont-expr->expr k.kont)))) t)

       ; Result of the function call
       (r (apply-k s (list k)))
       ((unless (wf-state-p r)) t)

       (args_res 
        (apply-k 
          (update-erl-state->in s '(:none)) 
          (list (make-erl-k 
                  :fuel (- k.fuel 1) 
                  :kont (make-kont-expr :expr (node-call->args (kont-expr->expr k.kont)))))))

      ((unless (wf-state-p args_res)) t)
      ((unless (equal (erl-val-kind (erl-state->in args_res)) :cons)) t)

      ((unless (equal (len (erl-val-cons->lst (erl-state->in args_res))) 2)) t)
      (a_val (car (erl-val-cons->lst (erl-state->in args_res))))
      (b_val (cadr (erl-val-cons->lst (erl-state->in args_res))))
      ((unless (and (equal (erl-val-kind a_val) :integer)
                    (equal (erl-val-kind b_val) :integer)))
       t) )

    (equal (erl-state->in r)
           (erl-val-integer (add (erl-val-integer->val a_val)
                                 (erl-val-integer->val b_val))))))