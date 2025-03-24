# NPS93

A type-based library search algorithm based on CC-unification in [NPS93].
Given a query type, it finds functions whose type unifies with the query type under the following isomorphisms, which are valid in any symmetric monoidal closed category:

$$
\begin{align*}
  A \times (B \times C) & = (A \times B) \times C \\
  A \times B & = B \times A \\
  A \times 1 & = A \\
  A \rightarrow (B \rightarrow C) & = (A \times B) \rightarrow C \\
  1 \rightarrow A & = A
\end{align*}
$$

These isomorphisms are not used because they would make the unification problem undecidable:

$$
\begin{align*}
  A \rightarrow (B \times C) & = (A \rightarrow B) \times (A \rightarrow C) \\
  A \rightarrow 1 & = 1
\end{align*}
$$

The search features:

- Insensitivity to currying/uncurrying and the order of arguments or components in products
- Ability to match types more general than the query type
- Support for variables in the query that can be unified (e.g. `?a`)

```text
> (x * x -> x) -> [x] -> ?a -> x
foldr1 : (a -> a -> a) -> [a] -> a
  by instantiating {?a ← (), a ← x}

foldl1 : (a -> a -> a) -> [a] -> a
  by instantiating {?a ← (), a ← x}

foldr : (a -> b -> b) -> b -> [a] -> b
  by instantiating {?a ← x, a ← x, b ← x}

foldl : (b -> a -> b) -> b -> [a] -> b
  by instantiating {?a ← x, a ← x, b ← x}

const : a -> b -> a
  by instantiating {?a ← x, a ← x, b ← [x] * (x * x -> x)}

... (more results)
```

`stack run -- signatures.txt` to run.

## References

- P. Narendran, F. Pfenning, and R. Statman. 2002. On the unification problem for Cartesian closed categories. In [1993] Proceedings Eighth Annual IEEE Symposium on Logic in Computer Science, 2002. IEEE Comput. Soc. Press, 57–63. https://doi.org/10.1109/lics.1993.287600
- M. Rittri. 1993. Retrieving library functions by unifying types modulo linear isomorphism. Theor. Inform. Appl. 27, 6 (1993), 523–540. https://doi.org/10.1051/ita/1993270605231
- Mark E. Stickel. 1981. A unification algorithm for associative-commutative functions. J. ACM 28, 3 (July 1981), 423–434. https://doi.org/10.1145/322261.322262
- E. Contejean and H. Devie. 1994. An efficient incremental algorithm for solving systems of linear Diophantine equations. Inf. Comput. 113, 1 (August 1994), 143–172. https://doi.org/10.1006/inco.1994.1067
