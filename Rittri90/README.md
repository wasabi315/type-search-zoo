# Rittri90

A type-based library search algorithm for Hindley-Milner type system based on CCC-matching in [Rittri90].
Given a query type, it finds functions whose type matches (can be instantiated to) the query type modulo the following isomorphisms which are valid in any cartesian closed category:

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
- Ability to match types more general than the query type

```text
> (x * x -> x) -> [x] -> x -> x
const : a -> b -> a
  by instantiating {a ← x, b ← (x * x -> x) * [x]}

foldr : (a -> b -> b) -> b -> [a] -> b
  by instantiating {a ← x, b ← x}

foldl : (b -> a -> b) -> b -> [a] -> b
  by instantiating {a ← x, b ← x}

fst : a * b -> a
  by instantiating {a ← x, b ← (x * x -> x) * [x]}

snd : a * b -> b
  by instantiating {a ← (x * x -> x) * [x], b ← x}

bimap : (a -> b) -> (c -> d) -> a * c -> b * d
  by instantiating {a ← (x * x -> x) * [x], b ← (), c ← (), d ← x}
```

`stack run -- signatures.txt` to try it out.

## References

- Bernard Lang. 2005. Matching with multiplication and exponentiation (extended abstract). Math. Struct. Comput. Sci. 15, 05 (October 2005), 959. https://doi.org/10.1017/s0960129505004883
- Mikael Rittri. 1990. Retrieving library identifiers via equational matching of types. In 10th International Conference on Automated Deduction. Springer Berlin Heidelberg, Berlin, Heidelberg, 603–617. https://doi.org/10.1007/3-540-52885-7_117
