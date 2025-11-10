(in-package "ACL2")
(include-book "erl-ast")
(include-book "ast-theorems")
(include-book "erl-value")
(include-book "eval-const")

(set-induction-depth-limit 1)


; TODO: purpose statement
; TODO: check what the match error values should be in Erlang

(define eval-pattern ((p pattern-p) (s erl-state-p))
  :returns (rs erl-state-p)
  (b* ((p (pattern-fix p))
       (s (erl-state-fix s))
       (s.in (erl-state->in s))
       (s.bind (erl-state->bind s)))
      (if (arithm-expr-p p)
          (b* ((n (eval-numeric p))
               ((unless (equal (erl-val-kind n) :integer))
                (make-erl-state :in (make-erl-val-reject :err "Illegal pattern."))))
               ((unless (equal n s.in)) 
                (make-erl-state 
                  :in (make-erl-val-excpt 
                       :err (make-erl-err :class (make-err-class-error) 
                                          :reason (make-exit-reason-badmatch :val s.in)))))
              s)
          (node-case p
            (:integer
              (if (and (equal (erl-val-kind s.in) :integer) 
                       (equal p.val (erl-val-integer->val s.in))
                  s
                  (make-erl-state 
                    :in (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val s.in)))))))
            ; TODO: lists and strings can be matched
            (:string
              (if (and (equal (erl-val-kind s.in) :string) 
                       (equal p.val (erl-val-string->val s.in))
                  s
                  (make-erl-state 
                    :in (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val s.in)))))))
            (:atom
              (if (and (equal (erl-val-kind s.in) :atom) 
                       (equal p.val (erl-val-atom->val s.in))
                  s
                  (make-erl-state 
                    :in (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val s.in)))))))
            (:nil
              (if (and (equal (erl-val-kind s.in) :cons) 
                       (null (erl-val-cons->lst s.in))
                  s
                  (make-erl-state 
                  :in (make-erl-val-excpt 
                        :err (make-erl-err :class (make-err-class-error) 
                                           :reason (make-exit-reason-badmatch :val s.in)))))))
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
                    (hd (eval-pattern p.hd (make-erl-val-state :in (car (erl-val-cons->lst s.in)) :bind s.bind)))
                    (tl (eval-pattern p.tl (make-erl-val-state :in (make-node-cons :lst (cdr (erl-val-cons->lst s.in))) 
                                                               :bind s.bind)))
                    (hd.in (erl-state->in hd))
                    (hd.bind (erl-state->bind hd))
                    (tl.in (erl-state->in tl))
                    (tl.bind (erl-state->bind tl))
                    ((if (equal (erl-val-kind hd.in) :reject)) hd)
                    ((if (equal (erl-val-kind tl.in) :reject)) tl)
                    ((if (equal (erl-val-kind hd.in) :excpt)) hd)
                    ((if (equal (erl-val-kind tl.in) :excpt)) tl)
                    ((unless (omaps::compatiblep hd.bind tl.bind))
                     ; TODO: This is supposed to return the value that failed to match. 
                     ; However, there is no easy way to figure this out.
                     (make-erl-state 
                      :in (make-erl-val-excpt 
                          :err (make-erl-err :class (make-err-class-error) 
                                             :reason (make-exit-reason-badmatch :val s.in))))))
                  (make-erl-state :in s.in :bind (omaps::update* tl.in hd.in))))
            (:tuple
              (b* (((unless (equal (erl-val-kind s.in) :tuple))
                    (make-erl-state 
                      :in (make-erl-val-excpt 
                          :err (make-erl-err :class (make-err-class-error) 
                                             :reason (make-exit-reason-badmatch :val s.in)))))
                    ((if (and (null (erl-val-tuple->lst s.in)) (null p.lst))) s)
                    ((if (null (erl-val-tuple->lst s.in))) 
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
                    ((unless (omaps::compatiblep hd.bind tl.bind))
                     ; TODO: This is supposed to return the value that failed to match. 
                     ; However, there is no easy way to figure this out.
                     (make-erl-state 
                      :in (make-erl-val-excpt 
                          :err (make-erl-err :class (make-err-class-error) 
                                             :reason (make-exit-reason-badmatch :val s.in))))))
                  (make-erl-state :in s.in :bind (omaps::update* tl.in hd.in))))
            (:var
              ; todo 
              )
            (:unop 
              (make-erl-state :in (make-erl-val-reject :err "Illegal pattern.")))
            (:binop
              ; todo
              (make-erl-state :in (make-erl-val-reject :err "Illegal pattern.")))))))

;; in more returns prove that it does not return none or flimit