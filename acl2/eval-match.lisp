(in-package "ACL2")
(include-book "erl-ast")
(include-book "ast-theorems")
(include-book "erl-value")
(include-book "eval-numeric")

(set-induction-depth-limit 1)

; Pattern Count Decreases ------------------------------------------------------

(local (defrule node-count-of-pattern-cons->tl
  (implies (and (not (arithm-expr-p (pattern-fix p)))
                (equal (node-kind (pattern-fix p)) :cons)
                (equal (erl-val-kind val) :cons)
                (erl-val-cons->lst val))
           (< (node-count (node-cons->tl (pattern-fix p)))
              (node-count p)))
  :enable pattern-fix))

(local (defrule node-count-of-pattern-cons->hd
  (implies (and (not (arithm-expr-p (pattern-fix p)))
                (equal (node-kind (pattern-fix p)) :cons)
                (equal (erl-val-kind val) :cons)
                (erl-val-cons->lst val))
         (< (node-count (node-cons->hd (pattern-fix p)))
            (node-count p)))
  :enable pattern-fix))

(local (defrule node-count-of-pattern-tuple-car
  (implies (and (not (arithm-expr-p (pattern-fix p)))
              (equal (node-kind (pattern-fix p))
                     :tuple)
              (equal (erl-val-kind val) :tuple)
              (erl-val-tuple->lst val)
              (node-tuple->lst (pattern-fix p)))
         (< (node-count (car (node-tuple->lst (pattern-fix p))))
            (node-count p)))
  :enable pattern-fix))

(local (defrule node-count-of-pattern-tuple-cdr
  (implies (and (not (arithm-expr-p (pattern-fix p)))
                (equal (node-kind (pattern-fix p))
                      :tuple)
                (equal (erl-val-kind val) :tuple)
                (node-tuple->lst (pattern-fix p))
                (erl-val-tuple->lst val))
          (< (node-count (node-tuple (cdr (node-tuple->lst (pattern-fix p)))))
              (node-count p)))
  :enable (pattern-fix node-count node-list-count)))

(local (defrule node-count-of-pattern-match->lhs
  (implies (and (not (arithm-expr-p (pattern-fix p)))
                (equal (node-kind (pattern-fix p)) :match))
          (< (node-count (node-match->lhs (pattern-fix p)))
             (node-count p)))
  :enable pattern-fix))

(local (defrule node-count-of-pattern-match->rhs
  (implies (and (not (arithm-expr-p (pattern-fix p)))
                (equal (node-kind (pattern-fix p)) :match))
          (< (node-count (node-match->rhs (pattern-fix p)))
             (node-count p)))
  :enable pattern-fix))


; Evaluate Erlang Pattern Matching ---------------------------------------------

; Erlang reference manual explains: In pattern matching, a left-hand side pattern 
; is matched against a right-hand side term. If the matching succeeds, any unbound 
; variables in the pattern become bound. If the matching fails, an exception 
; is raised.
;
; Supported patterns:
; - Any valid Erlang term,
; - Bound or unbound variables, including the wildcard '_'
; - Pattern1 = Pattern2
; - Arithmetic Expressions
;
; An arithmetic expressions can be used in patterns if:
; - It uses only numeric or bitwise operators.
; - Its value can be evaluated to a constant when complied.
; which is implemented by the type arithm-expr. 
;
; Patterns allowed by Erlang that are not supported:
; - String Prefix in Patterns, for example: "hello " ++ X = "hello world".
;
; Implementation:
; - If there is an arithmetic expression, evaluate it and then 
;   check if the result is equal to the right-hand side value. The arithmetic
;   expression should have been evaluated at compile time, so the AST will be
;   rejected if there is an exception raised.
; - If the pattern is a term or bound variable, check if it is equal
;   to the right-hand side value. Lists and tuples are checked element by element.
; - If there is an unbound variable, bind the variable to the right-hand side 
;   value. Ignore this step if the variable is a wildcard, '_'. 
; - If sucessful, return the right-hand side value and the new bindings,
;   otherwise a badmatch exception.
;
(define eval-match ((p pattern-p) (val erl-val-p) (bind bind-p))
  :returns (mv (v erl-val-p) (b bind-p))
  :measure (node-count p)
  :verify-guards nil
  (b* ((p (pattern-fix p))
       (val (erl-val-fix val))
       (bind (bind-fix bind)))
      (if (arithm-expr-p p)
          (b* ((n (eval-numeric p))
               ((unless (equal (erl-val-kind n) :integer))
                (mv (make-erl-val-reject :err "Illegal pattern.") nil))
               ((unless (equal n val))
                (mv (make-erl-val-excpt 
                      :err (make-erl-err :class (make-err-class-error) 
                                         :reason (make-exit-reason-badmatch :val val)))
                    nil)))
              (mv val bind)) 
          (node-case p
            (:integer
              (if (and (equal (erl-val-kind val) :integer) 
                       (equal p.val (erl-val-integer->val val)))
                  (mv val bind)
                  (mv (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val val)))
                      nil)))
            (:string
              (if (and (equal (erl-val-kind val) :cons) 
                       (equal (string=>erl-cons p.val)
                              (erl-val-cons->lst val)))
                  (mv val bind)
                  (mv (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val val)))
                      nil)))
            (:atom
              (if (and (equal (erl-val-kind val) :atom) 
                       (equal p.val (erl-val-atom->val val)))
                  (mv val bind)
                  (mv (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val val)))
                      nil)))
            (:nil
              (if (and (equal (erl-val-kind val) :cons) 
                       (null (erl-val-cons->lst val)))
                  (mv val bind)
                  (mv (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val val)))
                      nil)))
            (:cons
              (b* (((unless (equal (erl-val-kind val) :cons))
                    (mv (make-erl-val-excpt 
                          :err (make-erl-err :class (make-err-class-error) 
                                             :reason (make-exit-reason-badmatch :val val)))
                        nil))
                    ((if (null (erl-val-cons->lst val))) 
                     (mv (make-erl-val-excpt 
                            :err (make-erl-err :class (make-err-class-error) 
                                               :reason (make-exit-reason-badmatch :val val)))
                          nil))
                    ((mv hd hd.bind) (eval-match p.hd (car (erl-val-cons->lst val)) bind))
                    ((mv tl tl.bind) 
                     (eval-match p.tl (make-erl-val-cons :lst (cdr (erl-val-cons->lst val))) bind))
                    ((if (equal (erl-val-kind hd) :reject)) (mv hd nil))
                    ((if (equal (erl-val-kind tl) :reject)) (mv tl nil))
                    ((if (equal (erl-val-kind hd) :excpt)) (mv hd nil))
                    ((if (equal (erl-val-kind tl) :excpt)) (mv tl nil))
                    ((unless (omap::compatiblep hd.bind tl.bind))
                     ; TODO: This is supposed to return the value that failed to match. 
                     ; However, there is no easy way to figure this out.
                     (mv (make-erl-val-excpt 
                          :err (make-erl-err :class (make-err-class-error) 
                                             :reason (make-exit-reason-badmatch :val val)))
                         nil)))
                  (mv val (omap::update* tl.bind hd.bind))))
            (:tuple
              (b* (((unless (equal (erl-val-kind val) :tuple))
                    (mv (make-erl-val-excpt 
                          :err (make-erl-err :class (make-err-class-error) 
                                             :reason (make-exit-reason-badmatch :val val)))
                        nil))
                    ((if (and (null (erl-val-tuple->lst val)) (null p.lst))) (mv val bind))
                    ((if (or (null (erl-val-tuple->lst val)) (null p.lst)))
                      (mv (make-erl-val-excpt 
                            :err (make-erl-err :class (make-err-class-error) 
                                               :reason (make-exit-reason-badmatch :val val)))
                          nil))
                    ((mv hd hd.bind) (eval-match (car p.lst) (car (erl-val-tuple->lst val)) bind))
                    ((mv tl tl.bind) (eval-match (make-node-tuple :lst (cdr p.lst)) 
                                                 (make-erl-val-tuple :lst (cdr (erl-val-tuple->lst val)))
                                                 bind))
                    ((if (equal (erl-val-kind hd) :reject)) (mv hd nil))
                    ((if (equal (erl-val-kind tl) :reject)) (mv tl nil))
                    ((if (equal (erl-val-kind hd) :excpt)) (mv hd nil))
                    ((if (equal (erl-val-kind tl) :excpt)) (mv tl nil))
                    ((unless (omap::compatiblep hd.bind tl.bind))
                     ; TODO: This is supposed to return the value that failed to match. 
                     ; However, there is no easy way to figure this out.
                     (mv
                      (make-erl-val-excpt 
                          :err (make-erl-err :class (make-err-class-error) 
                                             :reason (make-exit-reason-badmatch :val val)))
                      nil)))
                  (mv val (omap::update* tl.bind hd.bind))))
            (:var
              (b* (((if (equal p.id '_)) (mv val bind))
                   ((unless (omap::assoc p.id bind))
                    (mv val (omap::update p.id val bind)))
                    ((unless (equal (omap::lookup p.id bind) val))
                     (mv
                      (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val val)))
                      nil)))
                  (mv val bind)))
            (:unop 
              (mv (make-erl-val-reject :err "Illegal pattern.") nil))
            (:binop
              (mv (make-erl-val-reject :err "Illegal pattern.") nil))
            (:match 
              (b* (((mv l l.bind) (eval-match p.lhs val bind))
                   ((mv r r.bind) (eval-match p.rhs val bind))
                   ((if (equal (erl-val-kind l) :reject)) (mv l nil))
                   ((if (equal (erl-val-kind r) :reject)) (mv r nil))
                   ((if (equal (erl-val-kind l) :excpt)) (mv l nil))
                   ((if (equal (erl-val-kind r) :excpt)) (mv r nil))
                   ((unless (omap::compatiblep r.bind l.bind))
                     ; TODO: This is supposed to return the value that failed to match. 
                     ; However, there is no easy way to figure this out.
                     (mv
                      (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val val)))
                      nil)))
                  (mv val (omap::update* r.bind l.bind))))
            (:if
              (mv (make-erl-val-reject :err "Illegal pattern.") nil))
            (:case-of
              (mv (make-erl-val-reject :err "Illegal pattern.") nil))
            (:remote-call
              (mv (make-erl-val-reject :err "Illegal pattern.") nil))
            (:call
              (mv (make-erl-val-reject :err "Illegal pattern.") nil)))))
    /// 
      (verify-guards eval-match)
      (more-returns
        (v (or (equal (erl-val-kind v) :reject)
               (equal (erl-val-kind v) :excpt)
               (equal (erl-val-kind v)
                      (erl-val-kind val)))
          :name erl-val-kind-of-eval-match->in)))

; Match each pattern to the corresponding argument, accumulate the bindings.
; - When callfed by 'if' or 'case-of' clauses, this is simply a wrapper 
;   around eval-match
(define match-args ((ps pattern-list-p) (vs erl-vlst-p) (bind bind-p))
  :returns (mv (v erl-val-p) (b bind-p))
  :measure (len (pattern-list-fix ps))
  (b* ((ps (pattern-list-fix ps))
       (vs (erl-vlst-fix vs))
       (bind (bind-fix bind))
       ((if (and (null ps) (null vs))) (mv (make-erl-val-none) bind))
       ((if (or (null ps) (null vs))) 
        (mv (make-erl-val-reject :err "Match-Args expects same number of patterns and args") 
            nil))
       ((mv hd hd.bind) (eval-match (car ps) (car vs) bind))
       ((if (equal (erl-val-kind hd) :reject)) (mv hd nil))
       ((if (equal (erl-val-kind hd) :excpt)) (mv hd nil)))
     (match-args (cdr ps) (cdr vs) hd.bind))
  ///
    (more-returns
      (v (or (equal (erl-val-kind v) :reject)
             (equal (erl-val-kind v) :excpt)
             (equal (erl-val-kind v) :none))
         :name val-kind-of-match-args)))