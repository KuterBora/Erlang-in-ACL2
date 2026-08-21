(in-package "ACL2")
(include-book "wtree")

(set-induction-depth-limit 1)
(local (include-book "arithmetic-3/top" :dir :system))


(and
  (wtree-p (create-wtree 1))
  (wtree-p (create-wtree 2))
  (wtree-p (create-wtree 3))
  (wtree-p (create-wtree 4))
  (wtree-p (create-wtree 5))
  (wtree-p (create-wtree 6))
  (wtree-p (create-wtree 7))
  (wtree-p (create-wtree 8)))

(define test (n)
  (b* ((n (nfix n))
       ((if (zp n)) t))
      (and
        (wtree-p (create-wtree n))
        (test (1- n)))))


(defrule proc->pid-of-make-reduce-proc
  (equal (proc->pid (make-reduce-proc pid x y z))
         (pid-fix pid))
  :enable (proc->pid make-reduce-proc))

(defrule leaf-p-of-make-reduce-proc
  (implies
    (and (natp index) (< 0 index) (pid-p parent))
    (leaf-p (make-reduce-proc x parent y index)))

  :enable (leaf-p make-reduce-proc bind-fix bind-p
    omap::mfix omap::mapp omap::from-lists
    omap::update omap::lookup omap::assoc
    omap::emptyp omap::head omap::tail))

(defrule root-p-of-make-reduce-proc
  (implies
    (and (equal index 0) (equal parent '(:atom none)))
    (root-p (make-reduce-proc x parent y index)))

  :enable (root-p make-reduce-proc bind-fix bind-p
    omap::mfix omap::mapp omap::from-lists
    omap::update omap::lookup omap::assoc
    omap::emptyp omap::head omap::tail))


(defrule wtree-p-of-create-wtree
  (wtree-p (create-wtree n))
  :hints
    (("Goal" :in-theory (e/d (wtree-p create-wtree create-wtree0 wtree0-p omap::size) (nfix)))))