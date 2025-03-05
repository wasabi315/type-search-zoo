# Delahaye2000

Type System: Dependent types

Search Flexiblity:

- Insensitive to currying/uncurrying and the argument order
- Associative sigmas with identity
- Commutative products (sigmas with no dependencies between the components)

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
