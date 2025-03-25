# Rittri89

A type-based library search algorithm for Hindley-Milner type system presented in [Rittri89].
Given a query type, it finds functions whose type is equal to the query type modulo the following isomorphisms which are valid in any cartesian closed category:

```math
\begin{align*}
  A \times (B \times C) & = (A \times B) \times C \\
  A \times B & = B \times A \\
  A \times 1 & = A \\
  A \rightarrow (B \rightarrow C) & = (A \times B) \rightarrow C \\
  1 \rightarrow A & = A \\
  A \rightarrow (B \times C) & = (A \rightarrow B) \times (A \rightarrow C) \\
  A \rightarrow 1 & = 1
\end{align*}
```

The search features are the following:

- Insensitivity to
  - Currying/uncurrying
  - The order of arguments and product components
  - A function that returns a pair / a pair of functions that return the components

```text
> (x * y -> y) -> [x] -> y -> y
foldr : (a -> b -> b) -> b -> [a] -> b
foldl : (b -> a -> b) -> b -> [a] -> b
```

`stack run -- signatures.txt` to try it out.

## References

- Mikael Rittri. 1989. Using types as search keys in function libraries. In Proceedings of the fourth international conference on Functional programming languages and computer architecture (FPCA ’89), November 01, 1989. Association for Computing Machinery, New York, NY, USA, 174–183. https://doi.org/10.1145/99370.99384
