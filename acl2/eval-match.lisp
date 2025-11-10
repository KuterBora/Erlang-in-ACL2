(in-package "ACL2")
(include-book "erl-ast")
(include-book "ast-theorems")
(include-book "erl-value")
(include-book "erl-state")
(include-book "eval-numeric")

(set-induction-depth-limit 1)

; Pattern Count Decreases ------------------------------------------------------

(local (defrule node-count-of-pattern-cons->tl
  (implies (and (not (arithm-expr-p (pattern-fix p)))
                (equal (node-kind (pattern-fix p))
                      :cons)
                (equal (erl-val-kind (erl-state->in s))
                      :cons)
                (erl-val-cons->lst (erl-state->in s)))
          (< (node-count (node-cons->tl (pattern-fix p)))
              (node-count p)))
  :enable pattern-fix))

(local (defrule node-count-of-pattern-cons->hd
  (implies (and (not (arithm-expr-p (pattern-fix p)))
              (equal (node-kind (pattern-fix p))
                     :cons)
              (equal (erl-val-kind (erl-state->in s))
                     :cons)
              (erl-val-cons->lst (erl-state->in s)))
         (< (node-count (node-cons->hd (pattern-fix p)))
            (node-count p)))
  :enable pattern-fix))

(local (defrule node-count-of-pattern-tuple-car
  (implies (and (not (arithm-expr-p (pattern-fix p)))
                (equal (node-kind (pattern-fix p))
                      :tuple)
                (equal (erl-val-kind (erl-state->in s))
                      :tuple)
                (erl-val-tuple->lst (erl-state->in s))
                (node-tuple->lst (pattern-fix p)))
          (< (node-count (car (node-tuple->lst (pattern-fix p))))
              (node-count p)))
  :enable pattern-fix))

(local (defrule node-count-of-pattern-tuple-cdr
  (implies (and (not (arithm-expr-p (pattern-fix p)))
                (equal (node-kind (pattern-fix p))
                      :tuple)
                (equal (erl-val-kind (erl-state->in s))
                      :tuple)
                (erl-val-tuple->lst (erl-state->in s))
                (node-tuple->lst (pattern-fix p)))
          (< (node-count (node-tuple (cdr (node-tuple->lst (pattern-fix p)))))
              (node-count p)))
  :enable (pattern-fix node-count node-list-count)))


; Evaluate Erlang Pattern Matching ---------------------------------------------

; TODO: figure out the correct error messages
(define eval-pattern ((p pattern-p) (s erl-state-p))
  :returns (rs erl-state-p)
  :measure (node-count p)
  :verify-guards nil
  (b* ((p (pattern-fix p))
       (s (erl-state-fix s))
       (s.in (erl-state->in s))
       (s.bind (erl-state->bind s)))
      (if (arithm-expr-p p)
          (b* ((n (eval-numeric p))
               ((unless (equal (erl-val-kind n) :integer))
                (make-erl-state :in (make-erl-val-reject :err "Illegal pattern.")))
               ((unless (equal n s.in)) 
                (make-erl-state 
                  :in (make-erl-val-excpt 
                       :err (make-erl-err :class (make-err-class-error) 
                                          :reason (make-exit-reason-badmatch :val s.in))))))
              s)
          (node-case p
            (:integer
              (if (and (equal (erl-val-kind s.in) :integer) 
                       (equal p.val (erl-val-integer->val s.in)))
                  s
                  (make-erl-state 
                    :in (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val s.in))))))
            ; TODO: lists and strings can be matched
            (:string
              (if (and (equal (erl-val-kind s.in) :string) 
                       (equal p.val (erl-val-string->val s.in)))
                  s
                  (make-erl-state 
                    :in (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val s.in))))))
            (:atom
              (if (and (equal (erl-val-kind s.in) :atom) 
                       (equal p.val (erl-val-atom->val s.in)))
                  s
                  (make-erl-state 
                    :in (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val s.in))))))
            (:nil
              (if (and (equal (erl-val-kind s.in) :cons) 
                       (null (erl-val-cons->lst s.in)))
                  s
                  (make-erl-state 
                  :in (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val s.in))))))
            ; TODO: lists and strings can be matched
            (:cons
              (b* (((unless (equal (erl-val-kind s.in) :cons))
                    (make-erl-state 
                      :in (make-erl-val-excpt 
                          :err (make-erl-err :class (make-err-class-error) 
                                             :reason (make-exit-reason-badmatch :val s.in)))))
                    ((if (null (erl-val-cons->lst s.in))) 
                      (make-erl-state 
                        :in (make-erl-val-excpt 
                            :err (make-erl-err :class (make-err-class-error) 
                                               :reason (make-exit-reason-badmatch :val s.in)))))
                    (hd (eval-pattern p.hd (make-erl-state :in (car (erl-val-cons->lst s.in)) :bind s.bind)))
                    (tl (eval-pattern p.tl (make-erl-state :in (make-erl-val-cons :lst (cdr (erl-val-cons->lst s.in))) 
                                                               :bind s.bind)))
                    (hd.in (erl-state->in hd))
                    (hd.bind (erl-state->bind hd))
                    (tl.in (erl-state->in tl))
                    (tl.bind (erl-state->bind tl))
                    ((if (equal (erl-val-kind hd.in) :reject)) hd)
                    ((if (equal (erl-val-kind tl.in) :reject)) tl)
                    ((if (equal (erl-val-kind hd.in) :excpt)) hd)
                    ((if (equal (erl-val-kind tl.in) :excpt)) tl)
                    ((unless (omap::compatiblep hd.bind tl.bind))
                     ; TODO: This is supposed to return the value that failed to match. 
                     ; However, there is no easy way to figure this out.
                     (make-erl-state 
                      :in (make-erl-val-excpt 
                          :err (make-erl-err :class (make-err-class-error) 
                                             :reason (make-exit-reason-badmatch :val s.in))))))
                  (make-erl-state :in s.in :bind (omap::update* tl.in hd.in))))
            (:tuple
              (b* (((unless (equal (erl-val-kind s.in) :tuple))
                    (make-erl-state 
                      :in (make-erl-val-excpt 
                          :err (make-erl-err :class (make-err-class-error) 
                                             :reason (make-exit-reason-badmatch :val s.in)))))
                    ((if (and (null (erl-val-tuple->lst s.in)) (null p.lst))) s)
                    ((if (or (null (erl-val-tuple->lst s.in)) (null p.lst)))
                      (make-erl-state
                        :in (make-erl-val-excpt 
                            :err (make-erl-err :class (make-err-class-error) 
                                               :reason (make-exit-reason-badmatch :val s.in)))))
                    
                    (hd (eval-pattern (car p.lst) (make-erl-state :in (car (erl-val-tuple->lst s.in)) 
                                                                  :bind s.bind)))
                    (tl (eval-pattern (make-node-tuple :lst (cdr p.lst))
                                      (make-erl-state :in (make-erl-val-tuple :lst (cdr (erl-val-cons->lst s.in)))
                                                      :bind s.bind)))
                    (hd.in (erl-state->in hd))
                    (hd.bind (erl-state->bind hd))
                    (tl.in (erl-state->in tl))
                    (tl.bind (erl-state->bind tl))
                    ((if (equal (erl-val-kind hd.in) :reject)) hd)
                    ((if (equal (erl-val-kind tl.in) :reject)) tl)
                    ((if (equal (erl-val-kind hd.in) :excpt)) hd)
                    ((if (equal (erl-val-kind tl.in) :excpt)) tl)
                    ((unless (omap::compatiblep hd.bind tl.bind))
                     ; TODO: This is supposed to return the value that failed to match. 
                     ; However, there is no easy way to figure this out.
                     (make-erl-state 
                      :in (make-erl-val-excpt 
                          :err (make-erl-err :class (make-err-class-error) 
                                             :reason (make-exit-reason-badmatch :val s.in))))))
                  (make-erl-state :in s.in :bind (omap::update* tl.in hd.in))))
            (:var
              (b* (((if (equal p.id '_)) s)
                   ((unless (omap::assoc p.id s.bind))
                    (make-erl-state :in s.in :bind (omap::update p.id s.in s.bind)))
                    ((unless (equal (omap::lookup p.id s.bind) s.in))
                     (make-erl-state 
                      :in (make-erl-val-excpt 
                          :err (make-erl-err :class (make-err-class-error) 
                                             :reason (make-exit-reason-badmatch :val s.in))))))
                  s))
            (:unop 
              (make-erl-state :in (make-erl-val-reject :err "Illegal pattern.")))
            ; TODO: String concat should be allowed.
            (:binop
              (make-erl-state :in (make-erl-val-reject :err "Illegal pattern.")))
            (:match 
              (make-erl-state :in (make-erl-val-reject :err "Illegal pattern."))))))
    
    /// 
      (verify-guards eval-pattern)
    
    )



;; in more returns prove that it does not return none or flimit