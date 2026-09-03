(in-package "ACL2")

(include-book "network")
(set-induction-depth-limit 1)

; Some utility functions and rules.
; TODO: I might move these elsewhere.

(defrule head-of-outbox
  (implies
    (and (not (omap::emptyp m)) (outbox-p m))
    (and
      (pid-p (mv-nth 0 (omap::head m)))
      (erl-vlst-p (mv-nth 1 (omap::head m)))))
  :enable outbox-p)

(defrule head-of-outbox-consp
  (implies
    (and
      (not (omap::emptyp m)) (outbox-p m)
      (mv-nth 1 (omap::head m)))
    (consp (mv-nth 1 (omap::head m))))
  :enable (outbox-p erl-vlst-p)
  :disable head-of-outbox
  :use (:instance head-of-outbox))

(defrule lookup-of-outbox-consp
  (implies
    (and (outbox-p m) (omap::assoc k m) (omap::lookup k m))
    (consp (omap::lookup k m)))
  :prep-lemmas
   ((defrule consp-when-erl-vlst-p-and-non-nil
      (implies (and (erl-vlst-p x) x) (consp x))
    :enable erl-vlst-p)))

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