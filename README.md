
# Policy as Type

**Provably Correct Access Control Policies using Dependent Types**

This repository demonstrates how access control policies can be encoded as types in dependently typed languages, using **Agda**. It implements the concepts from the paper _Policy as Code, Policy as Type_ with examples comparing this approach to Rego (OPA) and, indirectly, Sentinel and Cedar.

Well-defined, provably-correct, and correctly applied policies are your best protection against criminal malice and incompetence. With life and commerce online, 
we are exposed to reputational, legal, and financial risk in millisecond timeframes; there won't always be a human in the loop when a criminal exploits a hole in 
your digital contract, or your AI hallucinates and transfers your money around.

Organizations and even people need the most powerful available policy technologies, which means attribute based access control (ABAC). However, only the
approach we demonstrate here can provide provable guarantees for the correctness of your policies and ensure they are correctly applied.

Main Points
---

- Policies are types; a policy specifies which communications are well-formed (allowed) and which are not (refused)

- Dependently typed languages, such as **Agda** or **Lean**, are sufficiently rich to express even very complex policies as types

- As such, your code can be statically checked against these policies, ensuring they are correctly applied; existing systems cannot do so
at the same level of complexity

- The values our policies evaluate will soon be distributed over the network; policy technologies must handle that correctly

- Security policies are actually types that can be statically type-checked in dependently typed languages.

## Structure

| Folder       | Purpose |
|--------------|---------|
| `agda/`      | Core modules implementing policy types and proofs |
| `examples/`  | Examples and Rego comparisons |
| `docs/`      | Overview materials and diagrams |
| `paper/`     | PDF version of the full paper (optional) |
