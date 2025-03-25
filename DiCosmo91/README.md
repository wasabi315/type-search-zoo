# DiCosmo91

A type-based library search algorithm for System F due to Di Cosmo.
Given a query type, it finds functions whose type is equal to the query type modulo the following isomorphisms:

```math
\begin{align*}
  A \times (B \times C) & = (A \times B) \times C \\
  A \times B & = B \times A \\
  A \times 1 & = A \\
  A \rightarrow (B \rightarrow C) & = (A \times B) \rightarrow C \\
  1 \rightarrow A & = A \\
  A \rightarrow (B \times C) & = (A \rightarrow B) \times (A \rightarrow C) \\
  A \rightarrow 1 & = 1 \\
  \forall X. \forall Y. A &= \forall Y. \forall X. A \\
  \forall X. A &= \forall Y. A[X \mapsto Y] & (X \text{ free for } Y \text { in } A, Y \text{ not free in } A) \\
  \forall X. (A \rightarrow B) &= A \rightarrow \forall X. B & (X \text{ not free in } A) \\
  \forall X. (A \times B) &= \forall X. A \times \forall X. B \\
  \forall X. 1 &= 1
\end{align*}
```

The search features are the following:

- Insensitivity to
  - Currying/uncurrying
  - The order of arguments and product components
  - A function that returns a pair / a pair of functions that return the components
  - The position of quantifiers (as long as not changing the meaning of the type)

```text
> (forall y. (y * x -> y) -> y -> y) -> [x]
build : forall a. (forall b. (a -> b -> b) -> b -> b) -> [a]
> ((y * x -> y) -> y -> y) -> [x]
**no results**
```

`stack run -- signatures.txt` to try it out.

## References

- Roberto Di Cosmo 1991. Invertibility of terms and valid isomorphisms.
  - Provides a finite, decidable axiomatisation of the isomorphisms holding in the models of System F with surjective pairing and terminal object.
