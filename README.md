# :mag: type-search-zoo

> [!NOTE]
> Work in progress.

A collection of type-based library search algorithms.

## List of Algorithms

### Rittri89

- Type system: Hindley-Milner
- Search flexibility:
  - Insensitive to currying/uncurrying and the argument order
  - Associative and commutative products with identity

```text
> (x * y -> y) -> [x] -> y -> y
foldr : (a -> b -> b) -> b -> [a] -> b
foldl : (b -> a -> b) -> b -> [a] -> b
```

### Lang78

- Type system: Hindley-Milner
- Search flexibility:
  - Insensitive to currying/uncurrying
  - Associative products with identity
  - Able to match types more general than the query type

```text
> x -> x -> x
const : a -> b -> a
  by instantiating {a ← x, b ← x}

fst : a * b -> a
  by instantiating {a ← x, b ← x}

snd : a * b -> b
  by instantiating {a ← x, b ← x}

bimap : (a -> b) -> (c -> d) -> a * c -> b * d
  by instantiating {a ← x, b ← (), c ← (), d ← x}
```

### Rittri90

- Type system: Hindley-Milner
- Search flexibility:
  - Insensitive to currying/uncurrying and the argument order
  - Associative and commutative products with identity
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

### DiCosmo91

- Type system: SystemF
- Search flexibility:
  - Insensitive to currying/uncurrying and the argument order
  - Associative and commutative products with identity

```text
> (forall y. (y * x -> y) -> y -> y) -> [x]
build : forall a. (forall b. (a -> b -> b) -> b -> b) -> [a]
> ((y * x -> y) -> y -> y) -> [x]
**yield no results**
```

## Delahaye2000

- Type System: Dependent types
- Search Flexiblity:
  - Insensitive to currying/uncurrying and the argument order
  - Associative sigmas with identity, and commutative if there are no dependencies between the components

```text
> (X : Type) (Y : X -> Type) (x : X) -> ((y : X) -> Y y) -> Y x
apply : (A : Type) (B : A -> Type) -> ((x : A) -> B x) -> (x : A) -> B x
> (X Y : Type) -> Y * X -> X * Y
pair : (A : Type) (B : Type) -> A -> B -> A * B
swap : (A : Type) (B : Type) -> A * B -> B * A
```
