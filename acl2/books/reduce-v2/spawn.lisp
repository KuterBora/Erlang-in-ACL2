(in-package "ACL2")
(include-book "proc")

; TODO defsection
(local (include-book "std/lists/len" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (enable* set::definitions)))

(local (defrule set-order-crock
  (implies
    (and (not (set::emptyp s))
         (not (set::emptyp (set::tail s))))
    (<< (set::head s)
        (set::head (set::tail s))))
  :in-theory (enable* set::order-rules)))

(local (defrule list-order
  (implies
    (and
      a b
      (true-listp a) (true-listp b) 
      (car a) (car b) (equal (car a) (car b))
      (cadr a) (cadr b) (not (equal (cadr a) (cadr b)))
      (not (cddr a)) (not (cddr b))
      (<< (cadr a) (cadr b)))
      (<< a b))
  :enable (<< lexorder)))

(local (defrule natp-order
  (implies
    (natp x)
    (<< x (+ 1 x)))
  :enable (<< lexorder alphorder)))

(local (defrule order-of-make-pid
  (implies
    (pid-p p)
    (<< p (erl-val-pid (+ 1 (erl-val-pid->id p)))))
  :enable (pid-p erl-val-kind erl-val-pid erl-val-pid->id)
  :disable list-order
  :expand ((erl-val-p p))
  :use (:instance list-order
          (a p)
          (b (list :pid (+ 1 (cadr p)))))))

(encapsulate
  (((spawn *) => * :formals (pids) :guard (pid-set-p pids)))

  ; BOZO: when I change pid from nat, this may have to change completely.
  (local (define spawn ((pids pid-set-p))
    :returns pid
    :measure (set::cardinality (pid-set-fix pids))
    :guard-hints (("Goal" :in-theory (enable pid-set-p pid-p set::head)))
    (b* ((pids (pid-set-fix pids))
         ((if (set::emptyp pids)) '(:pid 0))
         ((if (set::emptyp (set::tail pids)))
          (make-erl-val-pid :id (+ 1 (erl-val-pid->id (set::head pids))))))
        (spawn (set::tail pids)))))
  
  (more-returns spawn
    (pid :name pid-p-of-spawn
      (pid-p pid)
      :hints (("Goal" :in-theory (enable spawn pid-p)))))
  
  (defcong pid-set-equiv equal (spawn pids) 1
    :hints (("Goal" :in-theory (enable spawn))))
  
  (local (defruled order-of-spawn
    (implies
      (pid-set-p pids)
      (<< (set::head pids) (spawn pids)))
    :in-theory (e/d (spawn) (set-order-crock))
    :hints (("Subgoal *1/4" :use (:instance set-order-crock (s pids)))
            ("Subgoal *1/2" :in-theory (enable set::head pid-set-p)
                            :expand (spawn pids)))))

  ; the new pid is unique
  (defrule unique-pid-of-spawn
    (implies (pid-set-p pids) (not (set::in (spawn pids) pids)))
    :in-theory (enable* spawn set::order-rules)
    :hints (("Subgoal *1/4" :use (:instance order-of-spawn)))))

(define simple-spawn ((pids pid-set-p))
    :returns pid
    :measure (set::cardinality (pid-set-fix pids))
    :guard-hints (("Goal" :in-theory (enable pid-set-p pid-p set::head)))
    (b* ((pids (pid-set-fix pids))
         ((if (set::emptyp pids)) '(:pid 0))
         ((if (set::emptyp (set::tail pids)))
          (make-erl-val-pid :id (+ 1 (erl-val-pid->id (set::head pids))))))
        (simple-spawn (set::tail pids)))
  ///
    (more-returns
      (pid :name pid-p-of-simple-spawn
        (pid-p pid)
        :hints (("Goal" :in-theory (enable simple-spawn pid-p)))))
  
    (defcong pid-set-equiv equal (simple-spawn pids) 1
      :hints (("Goal" :in-theory (enable simple-spawn))))
    
    (local (defruled order-of-simple-spawn
      (implies
        (pid-set-p pids)
        (<< (set::head pids) (simple-spawn pids)))
      :in-theory (e/d (simple-spawn) (set-order-crock))
      :hints (("Subgoal *1/4" :use (:instance set-order-crock (s pids)))
              ("Subgoal *1/2" :in-theory (enable set::head pid-set-p)
                              :expand (simple-spawn pids)))))

    (defrule unique-pid-of-simple-spawn
      (implies (pid-set-p pids) (not (set::in (simple-spawn pids) pids)))
      :in-theory (enable* simple-spawn set::order-rules)
      :hints (("Subgoal *1/4" :use (:instance order-of-simple-spawn)))))

(defattach spawn simple-spawn) 