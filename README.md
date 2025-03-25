# :mag: type-search-zoo

> [!NOTE]
> Work in progress.

A collection of type-based library search algorithms.

## List of Algorithms

### Rittri89

- Type system: Hindley-Milner
- Search features:
  - Insensitivity to
    - Currying/uncurrying
    - The order of arguments and product components
    - A function that returns a pair / a pair of functions that return the components

```text
> (x * y -> y) -> [x] -> y -> y
foldr : (a -> b -> b) -> b -> [a] -> b
foldl : (b -> a -> b) -> b -> [a] -> b
```

### Lang78

- Type system: Hindley-Milner
- Search features:
  - Insensitivity to
    - Currying/uncurrying
    - Associativity of products
    - A function that returns a pair / a pair of functions that return the components
  - Ability to match types more general than the query type

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
- Search features:
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

### NPS93

- Type system: Hindley-Milner
- Search features:
  - Insensitivity to
    - Currying/uncurrying
    - The order of arguments and product components
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

### DiCosmo91

- Type system: SystemF
- Search features:
  - Insensitivity to
    - Currying/uncurrying
    - The order of arguments and product components
    - A function that returns a pair / a pair of functions that return the components
    - The position of quantifiers (as long as not changing the meaning of the type)

```text
> (forall y. (y * x -> y) -> y -> y) -> [x]
build : forall a. (forall b. (a -> b -> b) -> b -> b) -> [a]
> ((y * x -> y) -> y -> y) -> [x]
**yield no results**
```

### Delahaye2000

- Type system: Dependent types
- Search features:
  - Insensitivity to (with some restrictions)
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
