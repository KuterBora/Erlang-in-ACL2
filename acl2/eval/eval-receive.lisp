(in-package "ACL2")
(include-book "eval-clauses")

; Erlang Receive ---------------------------------------------------------------

; TODO: documentation
(define eval-receive ((s erl-state-p) (cls erl-clause-list-p))
  (declare (ignorable cls))
  :returns (mv (rs erl-state-p) (body expr-list-p))
  (mv (update-erl-state->in s (make-erl-val-blocked)) nil)
  
  ///
    (defcong erl-state-equiv equal (eval-receive s cls) 1)
    (defcong erl-clause-list-equiv equal (eval-receive s cls) 2))