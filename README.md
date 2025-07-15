
# Policy as Type

**Provably Correct Access Control Policies using Dependent Types**

This repository demonstrates how access control policies can be encoded as types in dependently typed languages, using **Agda** (or **Lean**). It implements the concepts
from the paper [_Policy as Code, Policy as Type_](https://arxiv.org/abs/2506.01446) with examples comparing this approach to
Rego (OPA) and, indirectly, Sentinel and Cedar.

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

## Running the Examples

While the paper shows code in Agda, I've also translated the examples to Lean as well.

To check out the agda examples you need to install agda and the agda standard library. The examples have been built with agda-stdlib 2.0, so should work with any 2.x version.

Instructions for installing Agda can be found [here](https://agda.readthedocs.io/en/stable/getting-started/installation.html).

For the Lean examples, you'll need to install lean. Instructions are [here](https://lean-lang.org/documentation/setup/). They assume you'll be developing with VS Code.

## Structure

| Folder       | Purpose |
|--------------|---------|
| `examples/agda`  | Agda version of the examples |
| `examples/lean` | Lean version fo the examples |
| `paper/`     | PDF and MD versions of the full paper |

## Acknowledgements

I would like to thank [Allen Brown, Jr.](https://www.linkedin.com/in/allen-brown-36b1261/), for many discussions and his careful reading which has significantly improved this paper.

### License
Code – MIT (see LICENSE)
Docs/Figures – CC-BY-4.0
