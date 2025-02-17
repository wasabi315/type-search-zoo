# Rittri89

- Insensitive to currying/uncurrying and the argument order
- Associative and commutative products with identity.

```text
> (x * y -> y) -> [x] -> y -> y
foldr : (a -> b -> b) -> b -> [a] -> b
foldl : (b -> a -> b) -> b -> [a] -> b
```

`stack run -- signatures.txt` to run.

## References

- Mikael Rittri. 1989. Using types as search keys in function libraries. In Proceedings of the fourth international conference on Functional programming languages and computer architecture (FPCA ’89), November 01, 1989. Association for Computing Machinery, New York, NY, USA, 174–183. https://doi.org/10.1145/99370.99384
