# Policy as Type

**Provably Correct Access Control Policies using Dependent Types**

This repository demonstrates how access control policies can be encoded as types in dependently typed languages, using **Agda**. It implements the concepts from the paper _Policy as Code, Policy as Type_ with examples comparing this approach to Rego (OPA) and, indirectly, Sentinel and Cedar.

Well-defined, provably-correct, and correctly applied policies are your best protection against criminal malice and incompetence. With life and commerce online, 
we are exposed to reputational, legal, and financial risk in millisecond timeframes; there won't always be a human in the loop when a criminal exploits a hole in 
your digital contract, or your AI hallucinates and transfers your money around.

Organizations and even people need the most powerful available policy technologies, which means attribute based access control (ABAC). However, only the
approach we demonstrate here can provide provable guarantees for the correctness of your policies.

Main Contributions
---

Policies are types; a policy specifies which communications are well-typed (allowed) and which are not (refused)

Dependently typed languages, such as **Agda** or **Lean** are sufficiently rich to express these even very complex policies as types

As such, your code can be statically checked against these policies
Security policies are actually types that can be statically type-checked in dependently typed languages.

The dynamic and real-time nature of the online world, combined with the increasing reliance on AI, requires dynamic policies able to react to changes
at internet speed; this requires the complexity and power of attribute based access control technologies.

