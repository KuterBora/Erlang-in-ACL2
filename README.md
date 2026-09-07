# Erlang in ACL2: A CPS Evaluator

## Erlang in ACL2

There are a few naming differences in the paper, in this repo:
- `estate` is `erl-state`
- `eval-cont-list is `apply-k`
- `cont-binop` and `cont-expr` are `kont-binop` and `kont-expr`

## Certify with:
ACL2_DIR/books/build/cert.pl --acl2 ACL2 *.lisp where ACL2_DIR denotes your ACL2 sources directory and ACL2 denotes a recent ACL2 executable.

## Important files:

### The Translator 
erl-to-acl2/erl-to-acl2.lisp : translator for Erlang modules and expressions.

### The AST Evaluator:
- acl2/eval/erl-ast : the ACL2 representation of Erlang AST
- acl2/eval/erl-kont : the continuations.
- acl2/eval/erl-eval : the AST evaluator
- acl2/eval/erl-state : the program state

### The Scheduler:
-acl2/scheduler/abstract : the abstract scheduler
acl2/scheduler/erl-in-acl2 : run the entire pipeline here.

### Examples:
- acl2/scheduler/examples : message passing examples
- acl2/books/erl-arithmetic/sum_of_nats : prove the closed form of summation for Erlang
- acl2/books/reduce-v2 : the reduce implementation and proofs.
- acl2/books/reduce-v2 : the top file describing what is done.
