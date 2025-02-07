# Rittri89

- Insensitive to currying/uncurrying and the order of arguments.
- Associative and commutative products with identity.

```text
> (b * a -> b) -> [a] * b -> b
foldr : (a -> b -> b) -> b -> [a] -> b
foldl : (b -> a -> b) -> b -> [a] -> b
```

## References

- Mikael Rittri. 1989. Using types as search keys in function libraries. In Proceedings of the fourth international conference on Functional programming languages and computer architecture (FPCA ’89), November 01, 1989. Association for Computing Machinery, New York, NY, USA, 174–183. https://doi.org/10.1145/99370.99384
