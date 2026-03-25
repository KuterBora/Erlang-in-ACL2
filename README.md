# Erlang in ACL2: A CPS Evaluator

## Setup

TODO

## Erlang in ACL2

TODO: description

Top-level repo guide:
- `acl2`: TODO
- `erl`: reference interpreter in Erlang.

Here are some key files and folders in `acl2`:
- `theorems` Contains theorems regarding Erlang code.
- `examples` Contains examples of evaluation and test cases.

- `erl-ast.lisp`: Defines an ACL2 representation of the Erlang AST.
- `ast-theorems.lisp`: Contains theorems regarding the Erlang AST.

- `erl-val.lisp`: ACL2 representations of Erlang values and exceptions.
- `erl-kont.lisp`: Defines continuations that encode the next step of the evaluator.
- `erl-state.lisp` Defines Erlang-state which represents the current value, bindings, world, and messages of the evaluator.

- `termination.lisp`: Contains the termination proof for the evaluator.
- `erl-eval.lisp`: The Erlang evaluator.
- `eval-theorems.lisp` Contains the core theorems regarding the evaluator.
