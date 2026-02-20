(in-package "ACL2")
(include-book "../erl-eval")
(include-book "std/testing/assert-equal" :DIR :SYSTEM)
(include-book "std/testing/must-succeed" :dir :system)

; load this file to execute all the tests for the Erlang evaluator.

(acl2::must-succeed (ld "basic.lisp"))
(acl2::must-succeed (ld "comparison.lisp"))
(acl2::must-succeed (ld "clauses.lisp"))
(acl2::must-succeed (ld "functions.lisp"))
(acl2::must-succeed (ld "anon_functions.lisp"))