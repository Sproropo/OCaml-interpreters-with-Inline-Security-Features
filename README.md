# Functional Language Interpreters with Security

This repository contains implementations of two interpreters in OCaml, each incorporating unique security mechanisms. This project was developed from scratch. (Note: This is an older project originally created and distributed by me in 2021 before being uploaded in 2024 to GitHub.)

## Interpreter 1: Permissions and Stack Inspection in OCaml
- File: `interpreter1.ml`
- Execution can succeed or fail based on permission fulfillment.

### How does it work
- It implements a permission system for functions in OCaml. Functions are in the form `Fun(x, fBody, p)`, where `p` is a permission tuple `Perm(Read, Write, Open)`. The operations can only take two integer values “1” and “0”, where “1” means the function is allowed to perform the operation.
- Permissions are defined by the function `myDelta`. The function `eval` initializes permissions to “1”.
- Stack Creation: The function `ieval` transforms `Fun` into `Closure`, carrying the local permissions `p` of the function and the stack `g`. During `Call(eFun, eArg)`, after ensuring that `eFun` is a `Closure(x, fBody, fDeclEnv, p)`, the permissions `p` are put on top of the stack `g`.
- Stack Inspection: Every time a Read, Write, or Open operation is encountered in the program, the package `If(Prim("=", WriteVar, CstI s0), Write , Abort)` is unpacked by `ieval`.

## Interpreter 2: Security with Local Policies instrumented
- File: `interpreter2.ml` 
- Execution flow relies on the success of local policy checks.

### How does it work
- Security is regulated by local policies with defined scopes and actions. Local policies can be defined by users.
- Policy checks occur within the current scope during execution.
- The function `pval` takes `Proc([exp_list])` as input and returns a list of values resulting from the evaluation of the expressions. It allows sharing of history between expressions in the list.
- Safety Framing: There are two constructs that allow this: Phi and UserPolicy. Phi allows calling predefined policies (noWaR, noOaW, noRaO), while UserPolicy allows the user to generate new policies by inserting a string in the form “nCaC”.
- History: All constructs that have more than one expression allow the last evaluated expression to inherit the updated history from the evaluation of the internal expressions to the construct.

# Test
Each file includes tests at the end.

