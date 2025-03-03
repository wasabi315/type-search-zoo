# DiCosmo91

Type System: SystemF

Search Flexiblity:

- Insensitive to currying/uncurrying and the argument order.
- Associative and commutative products with identity.

```text
> (forall y. (y * x -> y) -> y -> y) -> [x]
build : forall a. (forall b. (a -> b -> b) -> b -> b) -> [a]
> ((y * x -> y) -> y -> y) -> [x]
**yield no results**
```

`stack run -- signatures.txt` to run.

## References

- Roberto Di Cosmo 1991. Invertibility of terms and valid isomorphisms.
  - Provides a finite, decidable axiomatisation of the isomorphisms holding in the models of System F with surjective pairing and terminal object.
