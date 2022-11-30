# Interactions between equality and hom types

The two files in this folder show how an unrestricted definition of Martin-Löf's equality in Paige North's directed type theory automatically induces an equivalence between hom and equality-types.

In a conversation on the EPIT2020's summer school discord server, she explains that the existence of identity types corresponds in the semantics of her [paper](https://arxiv.org/abs/1807.10566) to an opfibration $Id(A) \to A \times A$, whose existence forces $A$ to be a groupoid.

This corresponds to the fact that the assignment $(A,B) \to Iso(A,B)$ is not functorial in $A$ nor $B$. However $Iso$ becomes functorial when restricted to the core of the considered category. This suggests restricting the definition of Martin Löf's equality to the core of our types.