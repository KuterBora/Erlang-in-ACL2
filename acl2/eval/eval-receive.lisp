(in-package "ACL2")
(include-book "eval-clauses")

; Erlang Receive ---------------------------------------------------------------

; TODO: documentation
(define eval-receive ((s erl-state-p) (cls erl-clause-list-p))
  (declare (ignorable cls))
  :returns (mv (rs erl-state-p) (body expr-list-p))
  (b* (((erl-state s) (erl-state-fix s))
        (cls (erl-clause-list-fix cls))
        ((mv (erl-state rs) body)      
         (eval-clauses (list s.in) cls s))
        ((if (equal (erl-val-kind rs.in) :reject)) (mv rs nil))
        ((if (null body))
         (mv (update-erl-state->in s (make-erl-val-blocked)) nil)))
      (mv rs body))
  
  ///
    (defcong erl-state-equiv equal (eval-receive s cls) 1)
    (defcong erl-clause-list-equiv equal (eval-receive s cls) 2))