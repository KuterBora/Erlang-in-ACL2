(in-package "ACL2")

(include-book "network")
(set-induction-depth-limit 1)

; Some utility functions.

(define outbox-emptyp ((outbox outbox-p))
  :returns (r booleanp)
  :measure (acl2-count (outbox-fix outbox))
  :hints (("Goal" :in-theory (enable outbox-p outbox-fix)))
  (b* ((outbox (outbox-fix outbox))
       ((if (omap::emptyp outbox)) t))
      (and (not (omap::head-val outbox))
           (outbox-emptyp (omap::tail outbox))))
  ///
    (defcong outbox-equiv equal (outbox-emptyp outbox) 1))