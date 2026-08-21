(include-book "proc")

; TODO defsection
  (local (include-book "std/lists/len" :dir :system))
  (local (include-book "arithmetic/top" :dir :system))
  (local (defrule order-crock
    (implies
      (and (not (omap::emptyp m))
           (not (omap::emptyp (omap::tail m))))
      (<< (mv-nth 0 (omap::head m))
          (mv-nth 0 (omap::head (omap::tail m)))))
    :in-theory (enable* omap::order-rules)))
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
  (((spawn *) => * :formals (net) :guard (network-p net)))

  ; BOZO: when I change pid from nat, this will have to change completely.
  (local (define spawn ((net network-p))
    :returns pid
    :measure (acl2-count (network-fix net))
    :guard-hints (("Goal" :in-theory (enable network-p)))
    (b* ((net (network-fix net))
         ((if (omap::emptyp net)) '(:pid 0))
         ((if (omap::emptyp (omap::tail net)))
          (make-erl-val-pid :id (+ 1 (erl-val-pid->id (omap::head-key net))))))
        (spawn (omap::tail net)))))
  
  (more-returns spawn
    (pid :name pid-p-of-spawn
      (pid-p pid)
      :hints (("Goal" :in-theory (enable spawn pid-p)))))
  
  (defcong network-equiv equal (spawn net) 1
    :hints (("Goal" :in-theory (enable spawn))))
  
  (local (defruled order-of-spawn
    (implies
      (network-p m)
      (<< (omap::head-key m) (spawn m)))
    :in-theory (e/d* (spawn) (order-crock))
    :hints (("Subgoal *1/3" :use (:instance order-crock))
            ("Subgoal *1/2" :in-theory (enable omap::head network-p)
                            :expand (spawn m)))))

  ; the new pid is unique
  (defrule unique-pid-of-spawn
    (implies (network-p net) (not (omap::assoc (spawn net) net)))
    :in-theory (enable* spawn omap::order-rules)
    :hints (("Subgoal *1/4" :use (:instance order-of-spawn (m net))))))

(define simple-spawn ((net network-p))
    :returns pid
    :measure (acl2-count (network-fix net))
    :guard-hints (("Goal" :in-theory (enable network-p)))
    (b* ((net (network-fix net))
         ((if (omap::emptyp net)) '(:pid 0))
         ((if (omap::emptyp (omap::tail net)))
          (make-erl-val-pid :id (+ 1 (erl-val-pid->id (omap::head-key net))))))
        (simple-spawn (omap::tail net)))
  ///
    (more-returns
    (pid :name pid-p-of-simple-spawn
      (pid-p pid)
      :hints (("Goal" :in-theory (enable simple-spawn pid-p)))))
  
    (defcong network-equiv equal (simple-spawn net) 1
      :hints (("Goal" :in-theory (enable simple-spawn))))
    
    (local (defruled order-of-simple-spawn
      (implies
        (network-p m)
        (<< (omap::head-key m) (simple-spawn m)))
      :in-theory (e/d* (simple-spawn) (order-crock))
      :hints (("Subgoal *1/3" :use (:instance order-crock))
              ("Subgoal *1/2" :in-theory (enable omap::head network-p)
                              :expand (simple-spawn m)))))

    (defrule unique-pid-of-simple-spawn
      (implies (network-p net) (not (omap::assoc (simple-spawn net) net)))
        :in-theory (enable* simple-spawn omap::order-rules)
        :hints (("Subgoal *1/4" :use (:instance order-of-simple-spawn (m net))))))
(defattach spawn simple-spawn) 