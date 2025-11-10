# Erlang in ACL2 Code Repository

## Setup

1. **Install Erlang and ALC2**
   - Erlang: TODO
   - ACL2: TODO
  
2. **Clone the Repository**  
   Clone this repository to your local machine:

   ```bash
   git clone <https://github.com/KuterBora/Erlang-in-ACL2>
   ```
   
3. **Certify the Books**
    TODO

## Erlang in ACL2

TODO: description of Erlang in ACL2

Top-level repo guide:
- `acl2`: TODO
- `erlang`: Scripts to parse and convert Erlang code to an ACL2 compatible AST.
- `ref`: reference interpreter in Erlang.

Here are some key files and folders in `acl2`:
- `erl-ast.lisp`: Defines an ACL2 representation of the Erlang AST.
- `ast-theorems.lisp`: Contains theorems regarding the Erlang AST.
- `erl-val.lisp`: ACL2 representations of Erlang values and exceptions.
- `erl-kont.lisp`: Defines continuations that encode the next step of the evaluator.
- `erl-state.lisp` Defines Erlang-state which represents the current value, bindings, world, and messages of the evaluator.
- `const-eval.lisp` Evaluator for constant Erlang expressions.
- `eval-termination.lisp`: Contains the termination proof for the evaluator.
- `erl-eval.lisp`: The Erlang evaluator.
- `eval-theorems.lisp` Contains the core theorems regarding the evaluator.
- `theorems` Contains proofs on evaluated Erlang code.
- `examples` Contains examples of evaluation and test cases.