(in-package "ACL2")
(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/top" :dir :system)

(set-induction-depth-limit 1)

(set-well-founded-relation l<)

(fty::deftypes expr
  (fty::deftagsum expr
    (:int-const ((val integerp)))
    (:tuple     ((lst expr-list-p)))
    (:fun-call  ((fsym symbolp)
		 (args expr-list-p)))
    :measure (list (acl2-count x) 1))
  (fty::deflist expr-list
    :elt-type expr-p
    :true-listp t
    :measure (list (acl2-count x) 0)))

(defines pattern
  :flag-local nil
  (define pattern-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (expr-count x)
    :flag expr
    (and (expr-p x)
      (case (expr-kind x)
            (:int-const t)
            (:tuple (pattern-list-p (expr-tuple->lst x)))
            (:fun-call nil))))

  (define pattern-list-p ((x acl2::any-p))
    :returns (ok booleanp)
    :measure (expr-list-count x)
    :flag lst
    (if (consp x)
      (and (pattern-p (car x)) (pattern-list-p (cdr x)))
      (null x))))


(encapsulate nil
  ; first, we'll prove that pattern is a subtype of expr
  ; I tried putting this in the flag-theorem below, but it's needed for
  ; some of the lemmas that come first.
  (defrule pattern-is-subtype-of-expr
    (implies (pattern-p x)  (expr-p x))
    :expand (pattern-p x))

  ; three lemmas to prove that pattern-list is a subtype of expr-list
  ; How did I come up with these?  I tried the proof of the flag-theorem,
  ; saw the induction cases that failed, and stated the corresponding
  ; lemmas.  This seems to be a common pattern when using flag-theorems.
  (local (defrule car-and-cdr-when-pattern-list-p
    (implies (and (pattern-list-p x) (consp x))
      (and (pattern-p (car x)) (pattern-list-p (cdr x))
	   ))
    :expand (pattern-list-p x)
    :rule-classes (:forward-chaining)))

  (local (defrule pattern-list-induct
    (implies (and (pattern-list-p x) (expr-list-p (cdr x)))
	     (expr-list-p x))
    :expand (pattern-list-p x)
    :rule-classes (:forward-chaining)))

  (local (defrule pattern-list-p-when-not-consp
    (implies (and (pattern-list-p x) (not (consp x)))
	     (null x))
    :expand (pattern-list-p x)
    :rule-classes (:forward-chaining)))

  (defthm-pattern-flag
    (defthm pattern-list-is-subtype-of-expr-list
      (implies (pattern-list-p x)  (expr-list-p x))
      :flag lst)
    :skip-others t))

; From here, the next few steps will be to define fixing functions for pattern-p and pattern-list-p.
; I would start with expr-fix, and then handle the case when (expr-kind x) is invalid for a
; pattern.
; From there, defining the equivalence function is straightforward, e.g.:
;   (define pattern-equiv (x y)
;     returns (ok booleanp)
;     (equal (pattern-fix x) (pattern-fix y)))
; Then, you can use fty::deffixtype to introduce fty fixtypes for pattern-p and pattern-list-p.
