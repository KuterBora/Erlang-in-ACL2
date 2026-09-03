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


; Inbox Utility ---------------------------------------------------------------

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
      (inbox-contains (cdr inbox) pid)))