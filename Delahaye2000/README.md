# Delahaye2000

A type-based library search algorithm for dependent types due to Delahaye.
Given a query type, it finds functions whose type is equal to the query type modulo the following isomorphisms basically:

```math
\begin{align*}
  A &= B & \text{if } A \text{ and } B \text{ are } \beta\text{-equivalent} \\
  \Sigma x : A. B &= \Sigma x : B. A & \text{if } x \text{ is not free in } A \text{ and } B \\
  \Sigma x : (\Sigma y : A. B). C &= \Sigma x : A. \Sigma y : B[y \mapsto x]. C[x \mapsto (x, y)] \\
  \Pi x : (\Sigma y : A. B). C &= \Pi x : A. \Pi y : B[y \mapsto x]. C[x \mapsto (x, y)] \\
  \Pi x : A. \Sigma y : B. C &= \Sigma y : (\Pi x : A. B). \Pi x : A. C[y \mapsto y x] \\
  \Sigma x : A. 1 &= A \\
  \Sigma x : 1. A &= A[x \mapsto ()] \\
  \Pi x : A. 1 &= 1 \\
  \Pi x : 1. A &= A[x \mapsto ()]
\end{align*}
```

However, the algorithm avoids considering isomorphisms where conversion functions appear in the type.

Here's the reasoning:
Suppose two types $A$ and $B$ are isomorphic, and let $\sigma$ and $\tau$ be the functions that convert between $A$ and $B$.
Can we say that $\Pi x : A. C$ is isomorphic to $\Pi x : B. C$? No. First, $\Pi x : B. C$ is not well-typed at all. It should be $\Pi x : B. C[x \mapsto \tau x]$.

Does a conversion function between them exist?
One might think the conversion functions are:

```math
\begin{align*}
  \lambda f x. f (\tau x) &:\ (\Pi x : A. C) \rightarrow (\Pi x : B. C[x \mapsto \tau x]) \\
  \lambda f x. f (\sigma x) &:\ (\Pi x : B. C[x \mapsto \tau x]) \rightarrow (\Pi x : A. C[x \mapsto \tau (\sigma x)])
\end{align*}
```

However, since $\tau (\sigma x)$ is not always definitionally equal to $x$, we don't always get back $\Pi x : A. C$. Instead, we get $\Pi x : A. C[x \mapsto \tau (\sigma x)]$!

Resulting search features are the following:

- Insensitivity to (as long as conversion functions does not appear in the type)
  - $\beta$-reduced or not
  - Currying/uncurrying
  - The order of arguments and dependent pairs components (as long as they are not dependent on each other)
  - A function that returns a dependent pair / a dependent pair of functions that return the components

```text
> (X Y : Type) -> Y * X -> X * Y
pair : (A : Type) (B : Type) -> A -> B -> A * B
swap : (A : Type) (B : Type) -> A * B -> B * A
> (P : (A : Type) * A) -> P.1
id : (A : Type) -> A -> A
> (b : Bool) -> Eq Bool b false -> Eq Bool b true -> False
eqTrueFalseAbs : (b : Bool) -> Eq Bool b true -> Eq Bool b false -> False
```

`stack run -- signatures.txt` to run.

## References

- David Delahaye. 2000. Information retrieval in a coq proof library using type isomorphisms. In Lecture Notes in Computer Science. Springer Berlin Heidelberg, Berlin, Heidelberg, 131–147. https://doi.org/10.1007/3-540-44557-9_8
