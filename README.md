# Functional Language Interpreters with Security

This repository contains implementations of two interpreters in OCaml, each incorporating unique security mechanisms.

## Interpreter 1: Permission-Based Security 
- File: `interpreter1.ml`
- Functions are annotated with sets of primitive construct for runtime permission checks (i.e. {read, write}) controlling access to security-relevant actions.
- Execution can succeed or fail based on permission fulfillment.

## Interpreter 2: Security with Local Policies
- File: `interpreter2.ml` 
- Security is regulated by local policies with defined scopes and actions.
- Policy checks occur within the current scope during execution.
- Execution flow relies on the success of local policy checks.

# Test
Each file includes tests at the end.

