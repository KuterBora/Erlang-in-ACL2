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

# Erlang in ACL2

TODO: description of Erlang in ACL2

Top-level repo guide:
- `acl2`: TODO
- `erlang`: Scripts to parse Erlang and convert it to an ACL2 compatible AST.
- `ref`: reference interpreter in Erlang.

Here are some key files in `acl2`:
- `erl-ast.lisp`: Defines an ACL2 representation of the Erlang AST.
- `ast-theorems.lisp`: Defines some trivial theorems regarding the ACL2 representation of the Erlang AST.
- `erl-val.lisp`: Defines the values retuned by the evaluator.
- `erl-kont.lisp`: Defines continuations that encode the next step of the evaluator. 
- `erl-op.lisp`: Defines ACL2 representations of built in Erlang functions.
- `eval-termination.lisp`: Contains the termination proof for the evaluator.
- `erl-eval.lisp`: The Erlang evaluator.
