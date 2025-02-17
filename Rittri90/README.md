# Rittri90

- Insensitive to currying/uncurrying and argument order
- Associative-commutative products with identity
- Able to match types more general than the query type

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

`stack run -- signatures.txt` to run.

## References

- Bernard Lang. 2005. Matching with multiplication and exponentiation (extended abstract). Math. Struct. Comput. Sci. 15, 05 (October 2005), 959. https://doi.org/10.1017/s0960129505004883
- Mikael Rittri. 1990. Retrieving library identifiers via equational matching of types. In 10th International Conference on Automated Deduction. Springer Berlin Heidelberg, Berlin, Heidelberg, 603–617. https://doi.org/10.1007/3-540-52885-7_117
