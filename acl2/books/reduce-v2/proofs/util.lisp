(in-package "ACL2")

(include-book "../wtree/wtree-theorems")
(set-induction-depth-limit 1)


; Sum and Sum-range  ----------------------------------------------------------

; helpers to compute the work completed by a wtree so far.

; compute sum of numbers up to n.
(define sum ((n natp))
  (b* ((n (nfix n))
       ((if (= n 0)) 0))
      (+ n (sum (1- n)))))

; (sum-range 0 2) -> 3
; (sum-range 1 2) -> 3
; (sum-range 1 3) -> 6
; (sum-range 5 6) -> 11
(define sum-range ((i natp) (j natp))
  :returns (n natp)
  :measure (acl2-count (- (nfix j) (nfix i)))
  (b* ((i (nfix i))
       (j (nfix j))
       ((if (< j i)) 0)
       ((if (equal i j)) i))
      (+ i (sum-range (+ 1 i) j)))
  ///
    (defcong nat-equiv equal (sum-range i j) 1)
    (defcong nat-equiv equal (sum-range i j) 2)
    
    (defrule sum-range-of-add
      (implies
        (and (natp i) (natp j) (natp n) (<= i j) (< j n))
        (equal (+ (sum-range i j) (sum-range (+ j 1) n))
               (sum-range i n))))
    (defrule sum-range-of-sum
      (implies
        (and (natp i) (natp j) (<= i j))
        (equal (sum-range i j) (- (sum j) (sum (1- i)))))
      :enable sum)
    (defrule sum-range-of-one
      (implies (natp j) (equal (sum-range 1 j) (sum j)))
      :enable sum)
    (defrule sum-range-of-zero
      (implies (natp j) (equal (sum-range 0 j) (sum j)))
      :enable sum)
    (defrule sum-range-of-same
      (implies (natp i) (equal (sum-range i i) i))
      :disable (sum-range-of-sum sum-range-of-one sum-range-of-zero)))


; General Utility -------------------------------------------------------------

(defrule erl-vlst-p-of-remove-equal
  (implies (erl-vlst-p l) (erl-vlst-p (remove-equal x l)))
  :enable erl-vlst-p)

(defrule commutuativity-of-remove-equal
  (equal (remove-equal a (remove-equal b l))
         (remove-equal b (remove-equal a l))))

(defrule pid-lst-crock
  (implies
    (and (prefixp (rev l2) (rev l1))
         l2 (erl-vlst-p l2) (pid-lst-p l1))
    (pid-lst-p l2))
  :use (:instance prefix-of-pid-lst-p
        (l1 (rev l1)) (l2 (rev l2)))
  :prep-lemmas
    ((defrule prefix-of-pid-lst-p
       (implies
         (and (pid-lst-p l1) (erl-vlst-p l2) (prefixp l2 l1))
         (pid-lst-p l2))
       :enable prefixp)))

(defrule assoc-of-head-of-submap-crock
  (implies
    (and (omap::submap a b) (not (omap::emptyp a)))
    (omap::assoc (mv-nth 0 (omap::head a)) b))
  :in-theory (enable* omap::submap))

; Inbox Utility ---------------------------------------------------------------

; Check if the inbox contains a message {pid, _}
(define inbox-contains ((inbox erl-vlst-p) (pid pid-p))
  :returns (r booleanp)
  :measure (acl2-count (erl-vlst-fix inbox))
  (b* ((inbox (erl-vlst-fix inbox))
       (pid (pid-fix pid))
       ((unless inbox) nil)
       (m (car inbox))
       ((if (and (equal (erl-val-kind m) :tuple)
                 (equal (len (erl-val-tuple->lst m)) 2)
                 (equal (car (erl-val-tuple->lst m)) pid)))
        t))
      (inbox-contains (cdr inbox) pid))
  ///
    (defcong erl-vlst-equiv equal (inbox-contains inbox pid) 1)
    (defcong pid-equiv equal (inbox-contains inbox pid) 2))

; The negation of inbox-contains
(define inbox-without ((inbox erl-vlst-p) (pid pid-p))
  :returns (r erl-vlst-p)
  :measure (acl2-count (erl-vlst-fix inbox))
  (b* ((inbox (erl-vlst-fix inbox))
       (pid (pid-fix pid))
       ((unless inbox) nil)
       (m (car inbox))
       ((if (and (equal (erl-val-kind m) :tuple)
                 (equal (len (erl-val-tuple->lst m)) 2)
                 (equal (car (erl-val-tuple->lst m)) pid)))
        (erl-vlst-fix (cdr inbox))))
      (cons m (inbox-without (cdr inbox) pid)))
  ///
    (defcong erl-vlst-equiv equal (inbox-without inbox pid) 1)
    (defcong pid-equiv equal (inbox-without inbox pid) 2))

; Retrive the value of a message {pid, value},
; or return the null value.
(define inbox->value ((inbox erl-vlst-p) (pid pid-p))
  :returns (v erl-val-p)
  :measure (acl2-count (erl-vlst-fix inbox))
  (b* ((inbox (erl-vlst-fix inbox))
       (pid (pid-fix pid))
       ((unless inbox) (make-erl-val-none))
       (m (car inbox))
       ((if (and (equal (erl-val-kind m) :tuple)
                 (equal (len (erl-val-tuple->lst m)) 2)
                 (equal (car (erl-val-tuple->lst m)) pid)))
        (erl-val-fix (cadr (erl-val-tuple->lst m)))))
      (inbox->value (cdr inbox) pid))
  ///
    (defcong erl-vlst-equiv equal (inbox->value inbox pid) 1)
    (defcong pid-equiv equal (inbox->value inbox pid) 2))


; Wtree Utility ---------------------------------------------------------------

; Check if the parent of the pid has not yet received the worker's message.
(define parent-still-waiting-p
  ((self pid-p) (parent erl-val-p) (net network-p))
  :returns (r booleanp)
  (b* ((self (pid-fix self))
       (parent (erl-val-fix parent))
       (net (network-fix net))
       ; the root has no parent to wait for it
       ((unless (pid-p parent)) t)
       ((unless (omap::assoc parent net)) nil)
       (pproc (omap::lookup parent net))
       (pbind (erl-state->bind (proc->s pproc)))
       ; the parent cannot terminated until it receives all messages.
       ((if (equal (proc->ps pproc) :terminated)) nil))
      (or (not (omap::assoc 'CPids pbind))
          (not (equal (erl-val-kind (omap::lookup 'CPids pbind)) :cons))
          (consp (member-equal self
                   (erl-val-cons->lst (omap::lookup 'CPids pbind))))))
  ///
    (defcong pid-equiv equal (parent-still-waiting-p a b c) 1)
    (defcong erl-val-equiv equal (parent-still-waiting-p a b c) 2)
    (defcong network-equiv equal (parent-still-waiting-p a b c) 3))
