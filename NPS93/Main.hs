module Main where

import Control.Applicative (Alternative)
import Control.Arrow ((&&&))
import Control.Exception (Exception (..))
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Logic
import Data.Char
import Data.Foldable
import Data.Function
import Data.List (findIndices, intersperse, sortOn, subsequences, transpose)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Maybe
import Data.MultiSet (MultiSet)
import Data.MultiSet qualified as MS
import Data.Set (Set)
import Data.Set qualified as S
import Data.String
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Tuple
import Data.Unique
import Data.Void
import LinearDiophantine
import System.Console.Haskeline
import System.Environment
import System.Exit
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L
import Witherable (forMaybe)

--------------------------------------------------------------------------------
-- Utils

all2 :: (a -> b -> Bool) -> [a] -> [b] -> Bool
all2 p xs ys = and $ zipWith p xs ys

choose :: (Alternative m, Foldable t) => t a -> m a
choose = foldr ((<|>) . pure) empty

--------------------------------------------------------------------------------
-- Names and variables

data Name
  = Name Text
  | Gen Unique -- Generated name
  deriving stock (Eq, Ord)

instance IsString Name where
  fromString s = Name (T.pack s)

instance Show Name where
  show = \case
    Name t -> T.unpack t
    Gen u -> "v$" <> show (hashUnique u)

genName :: IO Name
genName = Gen <$> newUnique

isGen :: Name -> Bool
isGen = \case
  Gen _ -> True
  Name _ -> False

data Var
  = Flexi Name -- variable to be unified
  | Rigid Name -- quantified variable
  deriving stock (Eq, Ord, Show)

--------------------------------------------------------------------------------
-- Substitutions

type Subst t = Map Var t

class Substable t where
  subst :: Subst t -> t -> t

composeSubst :: (Substable t) => Subst t -> Subst t -> Subst t
subst2 `composeSubst` subst1 = M.map (subst subst2) subst1 <> subst2

--------------------------------------------------------------------------------

infix 2 :=

data Equation a = a := a
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

substEq :: (Substable t) => Subst t -> Equation t -> Equation t
substEq sub (t1 := t2) = subst sub t1 := subst sub t2

--------------------------------------------------------------------------------
-- Types

infixr 5 `Prod`

infixr 4 `Arr`

data Ty
  = Var Var -- x or ?x
  | Const Name [Ty] -- f(t1, t2, ...) (e.g. List(a))
  | Unit -- ()
  | Ty `Prod` Ty -- t * u
  | Ty `Arr` Ty -- t -> u
  deriving stock (Eq, Ord, Show)

pattern FlexiVar, RigidVar :: Name -> Ty
pattern FlexiVar n = Var (Flexi n)
pattern RigidVar n = Var (Rigid n)

instance IsString Ty where
  fromString x = Var (Rigid (fromString x))

flexiVarSet :: Ty -> Set Var
flexiVarSet = \case
  Var v@(Flexi _) -> S.singleton v
  Var (Rigid _) -> mempty
  Const _ ts -> foldMap flexiVarSet ts
  Unit -> mempty
  t1 `Prod` t2 -> flexiVarSet t1 <> flexiVarSet t2
  t1 `Arr` t2 -> flexiVarSet t1 <> flexiVarSet t2

rigidVarSet :: Ty -> Set Var
rigidVarSet = \case
  Var v@(Rigid _) -> S.singleton v
  Var (Flexi _) -> mempty
  Const _ ts -> foldMap rigidVarSet ts
  Unit -> mempty
  t1 `Prod` t2 -> rigidVarSet t1 <> rigidVarSet t2
  t1 `Arr` t2 -> rigidVarSet t1 <> rigidVarSet t2

instance Substable Ty where
  subst sub = go
    where
      go = \case
        v@(Var v') -> M.findWithDefault v v' sub
        Const c ts -> Const c (map go ts)
        Unit -> Unit
        t1 `Prod` t2 -> go t1 `Prod` go t2
        t1 `Arr` t2 -> go t1 `Arr` go t2

-- Instantiate quantified variables with fresh flexible variables
-- Returns the new vars -> old vars mapping as well as the instantiated type.
instantiate :: Ty -> IO (Ty, Map Var Var)
instantiate t = do
  ren <- sequence $ M.fromSet (const $ Flexi <$> genName) (rigidVarSet t)
  let t' = subst (Var <$> ren) t
      ren' = M.fromList $ map swap $ M.toList ren
  pure (t', ren')

--------------------------------------------------------------------------------
-- Associative-commutative unification

-- Flattened types: nested products are flattened into a MultiSet
-- to take associativity and commutativity into account.
data Flat
  = FVar Var
  | FConst Name [Flat]
  | Flat `FArr` Flat
  | FUnit
  | FProd (MultiSet Flat) -- invariant: the size is >= 2
  deriving stock (Eq, Ord, Show)

flatten :: Ty -> Flat
flatten = \case
  Var v -> FVar v
  Const c ts -> FConst c (map flatten ts)
  Unit -> FUnit
  t1 `Prod` t2 -> flatten t1 `flatProd` flatten t2
  t1 `Arr` t2 -> flatten t1 `FArr` flatten t2

flatProd :: Flat -> Flat -> Flat
flatProd = \cases
  FUnit t -> t
  t FUnit -> t
  (FProd t) (FProd u) -> FProd $ t <> u
  (FProd t) u -> FProd $ MS.insert u t
  t (FProd u) -> FProd $ MS.insert t u
  t u -> FProd $ MS.fromList [t, u]

unflatten :: Flat -> Ty
unflatten = \case
  FVar v -> Var v
  FConst c ts -> Const c (map unflatten ts)
  FUnit -> Unit
  FProd ts -> foldr1 Prod $ map unflatten $ MS.toList ts
  a `FArr` b -> unflatten a `Arr` unflatten b

fromOccurList :: [(Flat, Int)] -> Flat
fromOccurList xs = case MS.size xs' of
  0 -> FUnit
  1 -> MS.findMin xs'
  _ -> FProd xs'
  where
    xs' = MS.fromMap $ M.fromList xs

instance Substable Flat where
  subst sub = go
    where
      go = \case
        v@(FVar v') -> M.findWithDefault v v' sub
        FConst c ts -> FConst c (map (subst sub) ts)
        t1 `FArr` t2 -> go t1 `FArr` go t2
        FUnit -> FUnit
        FProd ts -> foldr (flatProd . go) FUnit ts

occurIn :: Var -> Flat -> Bool
occurIn x = go
  where
    go = \case
      FVar y -> x == y
      FConst _ ts -> any go ts
      t1 `FArr` t2 -> go t1 || go t2
      FUnit -> False
      FProd ts -> any go ts

isFlexiVar :: Flat -> Bool
isFlexiVar = \case
  FVar (Flexi _) -> True
  _ -> False

acUnify' :: Set (Equation Flat) -> Subst Flat -> LogicT IO (Subst Flat)
acUnify' eqs accumSub = case S.minView eqs of
  Nothing -> pure accumSub
  -- ?x = ?x
  Just (FVar (Flexi x) := FVar (Flexi y), eqs')
    | x == y -> acUnify' eqs' accumSub
  -- ?x = s (?x not in s) then substitute ?x with s
  Just (FVar x@(Flexi _) := s, eqs')
    | not (x `occurIn` s) -> do
        let sub = M.singleton x s
            accSub' = sub `composeSubst` accumSub
            eqs'' = S.map (substEq sub) eqs'
        acUnify' eqs'' accSub'
  -- t = ?x (?x not in t) then substitute ?x with t
  Just (t := FVar x@(Flexi _), eqs')
    | not (x `occurIn` t) -> do
        let sub = M.singleton x t
            accSub' = sub `composeSubst` accumSub
            eqs'' = S.map (substEq sub) eqs'
        acUnify' eqs'' accSub'
  -- x = x
  Just (FVar (Rigid x) := FVar (Rigid y), eqs')
    | x == y -> acUnify' eqs' accumSub
  -- (t1 -> t2) = (t3 -> t4) ~> t1 = t3 /\ t2 = t4
  Just (t1 `FArr` t2 := t3 `FArr` t4, eqs') ->
    acUnify' (S.fromList [t1 := t3, t2 := t4] <> eqs') accumSub
  -- f(t1, t2, ...) = f(s1, s2, ...) ~> t1 = s1 /\ t2 = s2 /\ ...
  Just (FConst f ts := FConst g ss, eqs')
    | f == g -> do
        let eqs'' = S.fromList $ zipWith (:=) ts ss
        acUnify' (eqs' <> eqs'') accumSub
  -- () = ()
  Just (FUnit := FUnit, eqs') ->
    acUnify' eqs' accumSub
  -- t1 * ... * tn = s1 * ... * sm
  Just (FProd ts := FProd ss, eqs') -> do
    eqs'' <- solveAC ts ss
    acUnify' (eqs' <> S.fromList eqs'') accumSub
  Just _ -> do
    empty

solveAC :: MultiSet Flat -> MultiSet Flat -> LogicT IO [Equation Flat]
solveAC = \ts ss -> do
  let -- Remove types that are in both sets
      ts' = MS.toMap $ ts MS.\\ ss
      ss' = MS.toMap $ ss MS.\\ ts
      -- Remaining types and their multiplicities
      (us, eq) = unzip $ M.toList $ ts' <> M.map negate ss'
  case eq of
    [] -> pure mempty
    _ : _ -> do
      let -- Solve the linear diophantine equation
          basis = solveLinearDiophantine eq
          -- Filter out beforehand basis vectors that results in a unsolvable equation
          basis' = filter (isGoodBasisVec us) basis
      newVars <- liftIO $ replicateM (length basis') (FVar . Flexi <$> genName)
      subBasis <- choose $ tail $ subsequences basis'
      let sols = transpose subBasis
      guard $ all2 isGoodSol us sols
      pure $ zipWith (\u sol -> u := fromOccurList (zip newVars sol)) us sols
  where
    isMaybeUnifiable :: Flat -> Flat -> Bool
    isMaybeUnifiable = \cases
      -- either side is a flexible variable
      (FVar (Flexi _)) _ -> True
      _ (FVar (Flexi _)) -> True
      -- or both sides have the same rigid variable or type constructor
      (FVar (Rigid x)) (FVar (Rigid y)) -> x == y
      (FConst f _) (FConst g _) -> f == g
      (_ `FArr` _) (_ `FArr` _) -> True
      FUnit FUnit -> True
      (FProd _) (FProd _) -> True
      _ _ -> False

    isGoodBasisVec :: [Flat] -> [Int] -> Bool
    isGoodBasisVec ts = \b ->
      all
        (`S.notMember` badPairs)
        [ (i, j)
          | let nonZeroIxs = findIndices (/= 0) b,
            i <- nonZeroIxs,
            j <- nonZeroIxs,
            i < j
        ]
      where
        badPairs =
          S.fromList
            [ (i, j)
              | let its = zip [0 :: Int ..] ts,
                (i, t) <- its,
                (j, s) <- its,
                i < j && not (isMaybeUnifiable t s)
            ]

    isGoodSol :: Flat -> [Int] -> Bool
    isGoodSol t s =
      n > 0 -- all components of the product receives at least one occurrence of variables
        && (isFlexiVar t || n == 1)
      where
        n = sum s

acUnify :: [Equation Ty] -> LogicT IO (Subst Ty)
acUnify eqs = do
  let eqs' = S.fromList $ map (fmap flatten) eqs
  sub <- acUnify' eqs' mempty
  pure $ M.map unflatten sub

--------------------------------------------------------------------------------
-- Main algorithm

reduce :: Ty -> Ty
reduce = \case
  v@(Var _) -> v
  Const c ts -> Const c (map reduce ts)
  Unit -> Unit
  t1 `Prod` t2 -> case (reduce t1, reduce t2) of
    -- () * t ~> t
    (Unit, t2') -> t2'
    -- t * () ~> t
    (t1', Unit) -> t1'
    (t1', t2') -> t1' `Prod` t2'
  t1 `Arr` t2 -> case (reduce t1, reduce t2) of
    -- 1 -> t ~> t
    (Unit, t2') -> t2'
    -- t -> u -> v ~> t * u -> v
    (t1', u `Arr` v) -> (t1' `Prod` u) `Arr` v
    (t1', t2') -> t1' `Arr` t2'

hasConst :: Ty -> Bool
hasConst = \case
  Var _ -> False
  Const _ _ -> True
  Unit -> False
  t1 `Prod` t2 -> hasConst t1 || hasConst t2
  t1 `Arr` t2 -> hasConst t1 || hasConst t2

unifyUnit :: Ty -> Maybe (Subst Ty)
unifyUnit a = do
  -- It is not possible to bring the type isomorphic to Unit
  -- if it has uninterpreted type constructors or rigid variables.
  guard $ S.null $ rigidVarSet a
  guard $ not $ hasConst a
  -- It is otherwise possible by substituting all flexible variables with Unit.
  pure $ M.fromSet (const Unit) (flexiVarSet a)

-- Entrypoint: the cc-unification algorithm
ccUnify :: Ty -> Ty -> LogicT IO (Subst Ty)
ccUnify a b = do
  -- Nondeterministically choose variables to be substituted with Unit
  mvarsA <- choose $ S.powerSet $ flexiVarSet a
  mvarsB <- choose $ S.powerSet $ flexiVarSet b
  let unitSub = M.fromSet (const Unit) (mvarsA <> mvarsB)
  -- Apply the substitutions and reduce the types
  case (reduce (subst unitSub a), reduce (subst unitSub b)) of
    -- If either side is Unit, try unifying the other side with Unit
    (Unit, b') -> do
      remainingSub <- choose $ unifyUnit b'
      pure $ remainingSub `composeSubst` unitSub
    (a', Unit) -> do
      remainingSub <- choose $ unifyUnit a'
      pure $ remainingSub `composeSubst` unitSub
    (a', b') -> do
      (a'', eqa) <- possibleInnermostReductions a'
      (b'', eqb) <- possibleInnermostReductions b'
      let eqs = (a'' := b'') : eqa ++ eqb
      remainingSub <- acUnify eqs
      pure $ remainingSub `composeSubst` unitSub

-- Assume the type is irreducible with respect to 1 * A ~> A and 1 -> A ~> A
possibleInnermostReductions :: Ty -> LogicT IO (Ty, [Equation Ty])
possibleInnermostReductions = \case
  t@(Var _) -> pure (t, [])
  Const c ts -> do
    (ts', eqs) <- mapAndUnzipM possibleInnermostReductions ts
    pure (Const c ts', concat eqs)
  Unit -> pure (Unit, [])
  t1 `Prod` t2 -> do
    (t1', eqs1) <- possibleInnermostReductions t1
    (t2', eqs2) <- possibleInnermostReductions t2
    pure (t1' `Prod` t2', eqs1 ++ eqs2)
  t@(t1 `Arr` t2) ->
    pure (t, [])
      <|> do
        x1 <- liftIO $ FlexiVar <$> genName
        x2 <- liftIO $ FlexiVar <$> genName
        x3 <- liftIO $ FlexiVar <$> genName
        let -- x1 -> (x2 -> x3) ~> (x1 * x2) -> x3
            l = x1 `Arr` (x2 `Arr` x3)
            r = (x1 `Prod` x2) `Arr` x3
        (t1', eqs1) <- possibleInnermostReductions t1
        (t2', eqs2) <- possibleInnermostReductions t2
        pure (r, (t1' `Arr` t2' := l) : eqs1 ++ eqs2)

--------------------------------------------------------------------------------
-- Ranking in terms of the size of the substitution

-- The number of each variable in the type
numEachVar :: Ty -> Map Var Int
numEachVar = \case
  Var v -> M.singleton v 1
  Const _ ts -> M.unionsWith (+) $ map numEachVar ts
  Unit -> mempty
  t1 `Prod` t2 -> M.unionWith (+) (numEachVar t1) (numEachVar t2)
  t1 `Arr` t2 -> M.unionWith (+) (numEachVar t1) (numEachVar t2)

-- The number of type constructors in the type
numConst :: Ty -> Int
numConst = \case
  Var _ -> 0
  Const _ _ -> 1
  Unit -> 1
  t1 `Prod` t2 -> numConst t1 + numConst t2 + 1
  t1 `Arr` t2 -> numConst t1 + numConst t2 + 1

substSize :: Subst Ty -> Int
substSize sub =
  let varNum = M.unionsWith (+) $ map numEachVar $ M.elems sub
      repVarScore = sum varNum - M.size varNum
      constScore = sum $ M.map numConst sub
   in weightRepeatedVar * repVarScore + weightConst * constScore

weightRepeatedVar :: Int
weightRepeatedVar = 1

weightConst :: Int
weightConst = 2

--------------------------------------------------------------------------------
-- Pretty printing

enclose :: ShowS -> ShowS -> ShowS -> ShowS
enclose l r x = l . x . r

punctuate :: ShowS -> [ShowS] -> ShowS
punctuate sep xs = foldr (.) id (intersperse sep xs)

prettyVar :: Var -> ShowS
prettyVar = \case
  Flexi n -> showChar '?' . shows n
  Rigid n -> shows n

prettyTy :: Int -> Ty -> ShowS
prettyTy p = \case
  Var v -> prettyVar v
  Const c [] -> shows c
  Const "List" [a] -> enclose (showChar '[') (showChar ']') (prettyTy 0 a)
  Const c as@(_ : _) ->
    shows c . showParen True (punctuate (showString ", ") (map (prettyTy 0) as))
  Unit -> showString "()"
  a `Prod` b -> showParen (p > 5) $ prettyTy 6 a . showString " * " . prettyTy 5 b
  a `Arr` b -> showParen (p > 4) $ prettyTy 5 a . showString " -> " . prettyTy 4 b

prettySubst :: Subst Ty -> ShowS
prettySubst sub =
  M.toList sub
    & map (\(x, t) -> prettyVar x . showString " ← " . prettyTy 0 t)
    & punctuate (showString ", ")
    & enclose (showChar '{') (showChar '}')

prettyEq :: Equation Ty -> ShowS
prettyEq (t1 := t2) = prettyTy 0 t1 . showString " = " . prettyTy 0 t2

prettyEqs :: (Foldable t) => t (Equation Ty) -> ShowS
prettyEqs eqs = punctuate (showString ", ") (map prettyEq $ toList eqs)

--------------------------------------------------------------------------------
-- Parsing

type Parser = Parsec Void Text

sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

pFunName :: Parser Text
pFunName = lexeme do
  n <- takeWhile1P (Just "function name") isAlphaNum
  guard $ isLower (T.head n)
  pure n

pVarName :: Parser Name
pVarName = lexeme do
  n <- takeWhile1P (Just "type variable") isAlphaNum
  guard $ isLower (T.head n)
  pure (Name n)

pConstName :: Parser Name
pConstName = lexeme do
  n <- takeWhile1P (Just "type constructor") isAlphaNum
  guard $ isUpper (T.head n)
  pure (Name n)

pAtom :: Bool -> Parser Ty
pAtom allowFlexi =
  try (RigidVar <$> pVarName)
    <|> (guard allowFlexi *> char '?' *> (FlexiVar <$> pVarName))
    <|> (Const <$> pConstName <*> option [] (parens (pTy allowFlexi `sepBy` symbol ",")))
    <|> (Const "List" . pure <$> brackets (pTy allowFlexi))
    <|> try (Unit <$ symbol "()")
    <|> parens (pTy allowFlexi)

pProd :: Bool -> Parser Ty
pProd allowFlexi = foldr1 Prod <$> pAtom allowFlexi `sepBy1` symbol "*"

pTy :: Bool -> Parser Ty
pTy allowFlexi = foldr1 Arr <$> pProd allowFlexi `sepBy1` symbol "->"

parseTy :: Bool -> Text -> Either (ParseErrorBundle Text Void) Ty
parseTy allowFlexi = parse (pTy allowFlexi <* eof) ""

parseSigs :: FilePath -> Text -> Either (ParseErrorBundle Text Void) [(Text, Ty)]
parseSigs path = flip parse path $ many ((,) <$> pFunName <*> (symbol ":" *> pTy False)) <* eof

--------------------------------------------------------------------------------

orDie :: (Exception e) => Either e a -> IO a
orDie = either (die . displayException) pure

helpText :: String
helpText = "Enter a type to query, :q to quit, or :h for help.\n\nType syntax:\n  <var>   ::= [a-z][a-zA-Z0-9]\n  <const> ::= [A-Z][a-zA-Z0-9]\n  <type>  ::= <var> | <const> | <const>(<type>, <type>, ...) | [<type>] | () | <type> * <type> | <type> -> <type>\n"

doSearch :: [(Text, Ty)] -> String -> InputT IO ()
doSearch sigs input = case parseTy True (T.pack input) of
  Left err -> outputStrLn (displayException err)
  Right query -> do
    matches <-
      sortOn snd <$> forMaybe sigs \(x, sig) -> do
        let queryVars = flexiVarSet query
        (sig', ren) <- liftIO $ instantiate sig
        subs <- liftIO $ observeAllT $ ccUnify sig' query
        case sortOn snd (map (id &&& substSize) subs) of
          [] -> pure Nothing
          ((sub, size) : _) -> do
            let querySub = M.restrictKeys sub queryVars
                libSub =
                  M.toList sub
                    & mapMaybe (\(v, t) -> (,t) <$> ren M.!? v)
                    & M.fromList
            pure $ Just ((x, sig, querySub <> libSub), size)
    for_ matches \((x, sig, sub), _) -> do
      outputStrLn $ T.unpack x ++ " : " ++ prettyTy 0 sig ""
      outputStrLn $ "  by instantiating " ++ prettySubst sub "\n"

main :: IO ()
main = do
  [path] <- getArgs
  src <- T.readFile path
  sigs <- orDie $ parseSigs path src
  runInputT defaultSettings do
    outputStrLn helpText
    fix \loop -> do
      minput <- getInputLine "> "
      case minput of
        Nothing -> loop
        Just ":q" -> pure ()
        Just ":h" -> outputStrLn helpText >> loop
        Just input -> doSearch sigs input >> loop
