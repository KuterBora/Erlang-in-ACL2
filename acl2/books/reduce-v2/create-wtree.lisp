(in-package "ACL2")
(include-book "spawn")

; TODO: defsection and doc

; Create a worker tree for reduce.
(define create-wtree0
  ((n natp) (self pid-p) (index natp) (parent erl-val-p)
   (children erl-vlst-p) (pids pid-set-p) (net network-p))
  :prepwork ((local (include-book "arithmetic-3/top" :dir :system)))
  :verify-guards nil
  :returns rnet
  :measure (nfix n)
  (b* ((n (nfix n))
       (self (pid-fix self))
       (index (nfix index))
       (parent (erl-val-fix parent))
       (children (erl-vlst-fix children))
       (pids (pid-set-fix pids))
       (net (network-fix net))
       ((if (zp n)) net)
       ((if (not (set::in self pids))) nil)
       ((if (omap::assoc self net)) nil)
       ((if (equal n 1))
        (omap::update self (make-reduce-proc self parent children index) net))
       (cpid (spawn pids))
       (child-net
         (create-wtree0
           (ceiling n 2) cpid (+ index (floor n 2)) self nil
           (set::insert cpid pids) net)))
      (create-wtree0
        (floor n 2) self index parent (cons cpid children)
        (set::union pids (omap::keys child-net)) child-net))
    ///
      (more-returns
        (rnet network-p :rule-classes :type-prescription
          :hints (("Goal" :in-theory (disable nfix)))))
        
      (verify-guards create-wtree0 :hints (("Goal" :in-theory (enable network-p))))
      
      (defcong nat-equiv equal (create-wtree0 a b c d e f g) 1)
      (defcong pid-equiv equal (create-wtree0 a b c d e f g) 2
        :hints (("Goal" :expand ((create-wtree0 a b c d e f g)
                                 (create-wtree0 a b-equiv c d e f g)))))
      (defcong nat-equiv equal (create-wtree0 a b c d e f g) 3
        :hints (("Goal" :in-theory (disable nfix)
                        :expand ((create-wtree0 a b c d e f g)
                                 (create-wtree0 a b c-equiv d e f g)))))
      (defcong erl-val-equiv equal (create-wtree0 a b c d e f g) 4)
      (defcong erl-vlst-equiv equal (create-wtree0 a b c d e f g) 5)
      (defcong pid-set-equiv equal (create-wtree0 a b c d e f g) 6
        :hints (("Goal" :expand ((create-wtree0 a b c d e f g)
                                 (create-wtree0 a b c d e f-equiv g)))))
      (defcong network-equiv equal (create-wtree0 a b c d e f g) 7
        :hints (("Goal" :expand ((create-wtree0 a b c d e f g)
                                 (create-wtree0 a b c d e f g-equiv))))))
  
(define create-wtree ((n natp))
  :returns (rnet network-p)
  :guard-hints (("Goal" :in-theory (enable pid-set-p)))
  (b* ((n (nfix n))
       (self (spawn nil)))
      (create-wtree0 n self 0 '(:atom none) nil (list self) nil))
  ///
    (defcong nat-equiv equal (create-wtree n) 1
      :hints (("Goal"
                :in-theory (disable nfix)
                :expand ((create-wtree n) (create-wtree n-equiv))
                :use (:instance nat-equiv-implies-equal-create-wtree0-1
                      (a n) (b self) (c 0) (d '(:atom none))
                      (e nil) (f (list self)) (g nil))))))