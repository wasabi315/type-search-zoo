# Lang78

- Insensitive to currying/uncurrying
- Associative products with identity
- Able to match types more general than the query type

```text
> a * b -> a
const : a -> b -> a
  by instantiating {a := a, b := b}

fst : a * b -> a
  by instantiating {a := a, b := b}

bimap : (a -> b) -> (c -> d) -> a * c -> b * d
  by instantiating {a := b, b := (), c := (), d := a}
```

## References

- Bernard Lang. 2005. Matching with multiplication and exponentiation (extended abstract). Math. Struct. Comput. Sci. 15, 05 (October 2005), 959. https://doi.org/10.1017/s0960129505004883
- Mikael Rittri. 1990. Retrieving library identifiers via equational matching of types. In 10th International Conference on Automated Deduction. Springer Berlin Heidelberg, Berlin, Heidelberg, 603–617. https://doi.org/10.1007/3-540-52885-7_117
