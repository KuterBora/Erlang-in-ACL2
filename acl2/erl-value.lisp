(in-package "ACL2")
(include-book "erl-ast")
(include-book "kestrel/fty/defsubtype" :DIR :SYSTEM)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

(set-induction-depth-limit 1)

; Erlang Values and Exceptions -------------------------------------------------

(set-well-founded-relation l<)

; Exceptions are run-time errors or generated errors and are of three different 
; classes, with different origins.
; - error:	Run-time error, for example, 1+a, or the process called error/1
; - exit:   The process called exit/1
; - throw:	The process called throw/1
(fty::deftagsum err-class
  (:error ())
  (:exit ())
  (:throw ()))

; Representation of the Erlang values returned by the evaluator.
; Remarks:
; - Strings are represented as lists of integer
; - Pairs are not supported
; - Named funs are not supported
; - TODO: pid
(fty::deftypes erl-val
  
  ; Erlang Values
  (fty::deftagsum erl-val
    ; Erlang return values
    (:integer ((val integerp)))
    (:atom ((val symbolp)))
    (:cons ((lst erl-vlst-p)))
    (:tuple ((lst erl-vlst-p)))
    (:fun ((arity natp)
           (cls erl-clause-list-p)
           (bind bind-p)
           (module symbolp)))
    (:excpt ((err erl-err-p)))

    ; Internal return values
    (:none ())
    (:reject ((err stringp)))
    (:flimit ())

    :measure (list (acl2-count x) 1))
  
  ; List of Erlang Values
  (fty::deflist erl-vlst
    :elt-type erl-val-p
    :true-listp t
    :measure (list (acl2-count x) 0))

  ; Erlang Errors
  (fty::defprod erl-err
    ((class err-class-p :default 'error)
     (reason exit-reason-p)
     (stack true-listp :default nil))
    :measure (list (acl2-count x) 1))

  ; Erlang Exit Reasons
  (fty::deftagsum exit-reason
    (:badarg ())
    (:badarith ())
    (:badmatch ((val erl-val-p)))
    (:function-clause ())
    (:case-clause ((val erl-val-p)))
    (:if-clause ())
    (:try-clause ((val erl-val-p)))
    (:undef ())
    (:badfun ((fun erl-val-p)))
    (:badarity ((fun erl-val-p) (args erl-vlst-p)))
    (:timeout-value ())
    (:noproc ())
    (:noconnection ())
    (:nocatch ((val erl-val-p)))
    (:system-limit ())
    :measure (list (acl2-count x) 0))
  
  ; Reprsentation of Erlang bindings. Maps each variable to a value.
  (fty::defomap bind
    :key-type symbol
    :val-type erl-val
    :measure (list (acl2-count x) 0)))


; Utility Functions/Structures -------------------------------------------------

; Erlang boolean
(fty::defsubtype erl-boolean
  :supertype erl-val-p
  :restriction 
    (lambda (x) 
      (and (equal (erl-val-kind x) :atom)
           (or (equal (erl-val-atom->val x) 'true)
              (equal (erl-val-atom->val x) 'false))))
  :fix-value (make-erl-val-atom :val 'false))

; Erlang anonymous function
(fty::defsubtype erl-fun
  :supertype erl-val-p
  :restriction 
    (lambda (x)
      (and (equal (erl-val-kind x) :fun)))
  :fix-value 
    (make-erl-val-fun 
      :arity 0 
      :cls '((:none)) 
      :bind nil 
      :module 'local))

(defrule erl-fun-p-of-erl-val-fun
  (implies (and (erl-val-p v) (equal (erl-val-kind v) :fun))
           (erl-fun-p v))
  :expand (erl-fun-p v))

; Helper for implementing list substraction
; For each element in the first argument, the first occurrence of this element 
; (if any) is removed from the second argument.
(define remove-first-of-each ((x erl-vlst-p) (lst erl-vlst-p))
  :returns (vlst erl-vlst-p)
  :measure (erl-vlst-count x)
  (b* ((x (erl-vlst-fix x))
       (lst (erl-vlst-fix lst)))      
      (if (endp x)
          lst
          (remove-first-of-each (cdr x) (remove1 (car x) lst :test 'equal)))))

; Turns a list of integers to a list of Erlang integers.
(define ints-to-erl-ints ((x integer-listp))
  :returns (vlst erl-vlst-p)
  :measure (len x)
  (b* ((x (integer-list-fix x))
       ((if (null x)) nil))
      (cons (make-erl-val-integer :val (car x))
            (ints-to-erl-ints (cdr x)))))

; Turns a string to its correponding Erlang list.
(define string=>erl-cons ((x stringp))
  :returns (v erl-val-p)
  (b* ((x (string x))
       (lst (string=>nats x))
       (erl-lst (ints-to-erl-ints lst)))
      (make-erl-val-cons :lst erl-lst))
  ///
    (more-returns
      (v (equal (erl-val-kind v) :cons)
      :name erl-val-kind-of-string=>erl-cons)))

; Obtain the arity from a clause-list
; Return nil if all clauses do not have the same arity, or if x is nil
(define erl-clause-list->arity ((x erl-clause-list-p))
  :measure (len x)
  (b* ((x (erl-clause-list-fix x))
       ((if (null x)) nil)
       (arity (len (node-clause->cases (car x))))
       ((if (null (cdr x))) arity)
       (rest (erl-clause-list->arity (cdr x)))
       ((if (null rest)) nil)
       ((unless (equal rest arity)) nil))
      arity))

; Erlang Equivalence -----------------------------------------------------------

; Checks if two Erlang values are equivalent. If one of the values is a rejection,
; the other value is also checked to be a rejection, regardless of its type.
; This is useful for simplifying theorems which have the hypothesis that the 
; given Erlang AST's are well-formed, and thus will not be rejected.
(define erl-equiv ((v1 erl-val-p) (v2 erl-val-p))
  (or (and (equal (erl-val-kind v1) :reject)
           (equal (erl-val-kind v2) :reject))
      (equal v1 v2)))

(defequiv erl-equiv
  :hints (("Goal" :in-theory (enable erl-equiv))))

(set-well-founded-relation o<)


; Theorems ---------------------------------------------------------------------

; If a vlst has len > 2, its cdr is not nil.
(defrule consp-of-cdr-of-erl-vlst
  (implies (and (erl-vlst-p x) (> (len x) 1))
           (consp (cdr x))))

; Appending two vlst will produce a vlst
(defrule append-of-erl-vlst
  (implies (and (erl-vlst-p vlst1) (erl-vlst-p vlst2))
           (erl-vlst-p (append vlst1 vlst2))))

; nth of an erl-vlst is an erl-val
(defrule nth-of-erl-vlst
  (implies 
    (and (erl-vlst-p vlst) 
         (integerp n)
         (>= n 0)
         (< n (len vlst)))
    (erl-val-p (nth n vlst))))

; A cons pair of two erl-vals is not an erl-val.
; This can be useful in a few places.
(defrule cons-of-erl-val-p
  (implies (erl-val-p v)
           (not (erl-val-p (cons v x))))
  :expand ((erl-val-p v) (erl-val-p (cons v x))))

; Some lemmas for symbol-listp-of-keys-of-bind-p
(local (defrule set-p-of-keys-of-bind-p
  (implies (bind-p b) (set::setp (omap::keys b)))))
  
(local (defrule symbolp-of-set-head
  (implies (and (set::setp s) (symbol-listp s))
            (symbolp (set::head s)))
  :expand (set::head s)))

(local (defrule symbol-listp-of-set-tail
  (implies (and (set::setp s) (symbol-listp s))
            (symbol-listp (set::tail s)))
  :expand (set::tail s)))
  
(local (defrule symbol-listp-of-set-insert
  (implies (and (set::setp s) (symbol-listp s) (symbolp x))
            (symbol-listp (set::insert x s)))
  :enable set::insert))

; The keys of a bind-p are a symbol-listp
(defrule symbol-listp-of-keys-of-bind-p
  (implies (bind-p b)
           (symbol-listp (omap::keys b)))
  :expand (bind-p b)
  :enable (omap::keys omap::head))
