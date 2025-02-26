module Main where

import Control.Exception (Exception (..))
import Control.Monad
import Control.Monad.IO.Class
import Data.Char
import Data.Foldable
import Data.Function
import Data.List (intersperse, permutations)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Maybe
import Data.Monoid
import Data.MultiSet (MultiSet)
import Data.MultiSet qualified as MS
import Data.String
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Traversable
import Data.Unique
import Data.Void
import List.Transformer (ListT)
import List.Transformer qualified as LT
import System.Console.Haskeline
import System.Environment
import System.Exit
import System.IO
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L
import Prelude hiding (exponent)

--------------------------------------------------------------------------------
-- Utils

concatZipWithM :: (Applicative m) => (a -> b -> m [c]) -> [a] -> [b] -> m [c]
concatZipWithM f xs ys = concat <$> zipWithM f xs ys

--------------------------------------------------------------------------------
-- Matching problem vocabulary from Rittri 1990.

-- | A matching problem is a pair of two terms: a pattern and a subject.
-- We seek the set of all substitutions that make the pattern and subject equal.
type Matching t = (t, t)

-- | A matching system is a set of matching problems.
-- We seek the set of all substitutions that is the solution to *all* the matching problems in the system.
type MatchingSys t = [Matching t]

-- | A matching disjunction system is a set of matching systems.
-- We seek the set of all substitutions that is the solution to *any* of the matching systems in the disjunction system.
type MatchingDisjSys t = [MatchingSys t]

-- | A substitution is a mapping from names to terms.
type Subst t = Map Name t

composeSubst :: (Subst t -> t -> t) -> Subst t -> Subst t -> Subst t
composeSubst appSubst subst2 subst1 = M.map (appSubst subst2) subst1 <> subst2

-- Lift a algorithm for a matching problem to one for a matching system
liftForMatchingSys ::
  (Monad m) =>
  (Subst t -> t -> t) ->
  (Matching t -> ListT m (Subst t)) ->
  (MatchingSys t -> ListT m (Subst t))
liftForMatchingSys appSubst alg sys =
  foldM
    ( \accSubst (pat, subj) -> do
        let problem = (appSubst accSubst pat, subj)
        subst <- alg problem
        pure $ composeSubst appSubst subst accSubst
    )
    mempty
    sys

-- Lift a algorithm for a matching problem to one for a matching disjunction system
liftForMatchingDisjSys ::
  (Monad m) =>
  (Subst t -> t -> t) ->
  (Matching t -> ListT m (Subst t)) ->
  (MatchingDisjSys t -> ListT m (Subst t))
liftForMatchingDisjSys appSubst alg disjSys =
  LT.select disjSys >>= liftForMatchingSys appSubst alg

--------------------------------------------------------------------------------
-- Types

infixr 5 `Prod`

infixr 4 `Arr`

data Name
  = Name Text
  | Gen Unique -- Generated name
  deriving stock (Eq, Ord)

instance IsString Name where
  fromString s = Name (T.pack s)

instance Show Name where
  show = \case
    Name t -> T.unpack t
    Gen u -> "$" <> show (hashUnique u)

genName :: IO Name
genName = Gen <$> newUnique

isGen :: Name -> Bool
isGen = \case
  Gen _ -> True
  Name _ -> False

data Ty
  = Var Name -- x
  | Const Name [Ty] -- f(t1, t2, ...) (e.g. List(a))
  | Unit -- ()
  | Ty `Prod` Ty -- t * u
  | Ty `Arr` Ty -- t -> u
  deriving stock (Eq, Ord, Show)

instance IsString Ty where
  fromString x = Var (fromString x)

-- | Converts all type variables to type constants.
freezeVars :: Ty -> Ty
freezeVars = \case
  Var x -> Const x []
  Const c as -> Const c (map freezeVars as)
  Unit -> Unit
  a `Prod` b -> freezeVars a `Prod` freezeVars b
  a `Arr` b -> freezeVars a `Arr` freezeVars b

--------------------------------------------------------------------------------
-- Normal form of types
-- The same one in the Rittri89 folder.

infixr 5 `nfProd`

infix 4 `FArr`

infix 4 `nfArr'`

infixr 4 `nfArr`

data Atom
  = AVar Name
  | AConst Name [NF]
  deriving stock (Show, Eq, Ord)

data Factor = NF `FArr` Atom
  deriving stock (Show, Eq, Ord)

type NF = MultiSet Factor

-- a ~ () -> a
nfAtom :: Atom -> NF
nfAtom a = MS.singleton (nfUnit `FArr` a)

nfVar :: Name -> NF
nfVar v = nfAtom (AVar v)

nfConst :: Name -> [NF] -> NF
nfConst c as = nfAtom (AConst c as)

nfUnit :: NF
nfUnit = mempty

-- a * (b * c) ~ (a * b) * c
-- a * b ~ b * a
-- a * () ~ a
-- () * a ~ a
nfProd :: NF -> NF -> NF
a `nfProd` b = a <> b

-- a -> (e -> b) ~ (a * e) -> b
nfArr' :: NF -> Factor -> Factor
a `nfArr'` (e `FArr` b) = (a `nfProd` e) `FArr` b

-- a -> (b1 * b2 * ... * bn) ~ (a -> b1) * (a -> b2) * ... * (a -> bn)
-- a -> () ~ ()
nfArr :: NF -> NF -> NF
a `nfArr` b = MS.map (nfArr' a) b

-- Reduce a type to its normal form
reduce :: Ty -> NF
reduce = \case
  Var x -> nfVar x
  Const c as -> nfConst c (map reduce as)
  Unit -> nfUnit
  a `Prod` b -> reduce a `nfProd` reduce b
  a `Arr` b -> reduce a `nfArr` reduce b

-- Convert a normal form to a type

unreduceAtom :: Atom -> Ty
unreduceAtom = \case
  AVar x -> Var x
  AConst c as -> Const c (map unreduce as)

unreduceFactor :: Factor -> Ty
unreduceFactor (e `FArr` b)
  | MS.null e = unreduceAtom b
  | otherwise = unreduce e `Arr` unreduceAtom b

unreduce :: NF -> Ty
unreduce a = case MS.minView a of
  Nothing -> Unit
  Just (f, fs) -> foldr (\g acc -> unreduceFactor g `Prod` acc) (unreduceFactor f) fs

-- Substitution for NF

nfSubstAtom :: Subst NF -> Atom -> NF
nfSubstAtom sub = \case
  a@(AVar x) -> fromMaybe (nfAtom a) (sub M.!? x)
  AConst c as -> nfConst c (map (nfSubst sub) as)

nfSubstFactor :: Subst NF -> Factor -> NF
nfSubstFactor sub (e `FArr` b) = nfSubst sub e `nfArr` nfSubstAtom sub b

nfSubst :: Subst NF -> NF -> NF
nfSubst sub = MS.unionsMap (nfSubstFactor sub)

--------------------------------------------------------------------------------
-- Base of a NF

data AtomKind
  = AKConst Name Int -- Name and arity
  | AKVar Name
  deriving stock (Show, Eq, Ord)

type Base = MultiSet AtomKind

atomKind :: Atom -> AtomKind
atomKind = \case
  AVar x -> AKVar x
  AConst c as -> AKConst c (length as)

base :: NF -> Base
base a = MS.map (\(_ `FArr` b) -> atomKind b) a

--------------------------------------------------------------------------------

-- A brute-force associative-commutative-unit matching algorithm
-- Assumes the subject does not contain any variables
acuMatch :: Matching Base -> [Subst Base]
acuMatch = \(pat, subj) ->
  let -- Remove atoms pairwise that are present in both base
      pat' = pat MS.\\ subj
      subj' = subj MS.\\ pat
   in go mempty (MS.toOccurList pat') subj'
  where
    go subst = \cases
      -- If the pattern and subject are both empty, return the substitution we have accumulated so far
      [] subj -> [subst | MS.null subj]
      -- If the pattern is a constant, it cannot match
      ((AKConst {}, _) : _) _ -> empty
      -- If the pattern is a variable, try all possible substitutions
      -- @m@ is the number of times the variable appears in the pattern
      -- @ms@ is the map of how many times each atom appears in the subject
      ((AKVar x, m) : p) subj -> do
        -- Try assigning a base to the variable @x@.
        -- Since the variable appears @m@ times in the pattern,
        -- an atom that appears @n@ times in the subject can be assigned between
        -- 0 and @n `div` m@ times in the base
        b <- traverse (\n -> [0 .. n `div` m]) (MS.toMap subj)
        let b' = MS.fromMap b
            -- Remove the assigned atoms in the base from the subject to get the remaining subject
            subj' = subj MS.\\ b'
        -- Recurse with the new substitution and the remaining subject
        go (M.insert x b' subst) p subj'

-- Returns the most general type that has the given base
mostGeneral :: Base -> IO NF
mostGeneral = fmap MS.fromList . traverse mg . MS.toList
  where
    mg :: AtomKind -> IO Factor
    mg = \case
      -- x ~> (() -> y) -> x
      AKVar x -> do
        y <- genName
        pure $ nfVar y `FArr` AVar x
      -- c ~> (() -> y) -> c(y1, y2, ..., yn)
      AKConst c n -> do
        y <- genName
        ys <- replicateM n genName
        pure $ nfVar y `FArr` AConst c (map nfVar ys)

mostGeneralSubst :: Subst Base -> IO (Subst NF)
mostGeneralSubst = traverse mostGeneral

-- | Entrypoint: match a pattern with a subject and return all possible substitutions.
-- Assumes the subject does not contain any variables.
nfMatches :: Matching NF -> ListT IO (Subst NF)
nfMatches (pat, subj) = do
  bsubst <- LT.select $ acuMatch (base pat, base subj)
  nsubst <- liftIO $ mostGeneralSubst bsubst
  nsubst' <- liftForMatchingDisjSys nfSubst nfMatches (equivMatchingDisjSys (nfSubst nsubst pat, subj))
  pure $ composeSubst nfSubst nsubst' nsubst

-- | Extract a matching disjunction system that is equivalent to the given matching problem.
-- Assumes the pattern and subject have a common base.
equivMatchingDisjSys :: Matching NF -> MatchingDisjSys NF
equivMatchingDisjSys = \(pat, subj) -> do
  let subj' = MS.toList subj
  pat' <- permutations (MS.toList pat)
  Just sys <- pure $ concatZipWithM go pat' subj'
  pure sys
  where
    go = \cases
      -- Type constructor should match
      (a `FArr` AConst c as) (a' `FArr` AConst c' as')
        | c == c' -> Just $ (a, a') : zip as as'
      _ _ -> Nothing

--------------------------------------------------------------------------------
-- Pretty printing

enclose :: ShowS -> ShowS -> ShowS -> ShowS
enclose l r x = l . x . r

punctuate :: ShowS -> [ShowS] -> ShowS
punctuate sep xs = foldr (.) id (intersperse sep xs)

prettyTy :: Int -> Ty -> ShowS
prettyTy p = \case
  Var v -> shows v
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
    & map (\(x, t) -> shows x . showString " ← " . prettyTy 0 t)
    & punctuate (showString ", ")
    & enclose (showChar '{') (showChar '}')

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

pAtom :: Parser Ty
pAtom =
  try (Var <$> pVarName)
    <|> (Const <$> pConstName <*> option [] (parens (pTy `sepBy` symbol ",")))
    <|> (Const "List" . pure <$> brackets pTy)
    <|> try (Unit <$ symbol "()")
    <|> parens pTy

pProd :: Parser Ty
pProd = foldr1 Prod <$> pAtom `sepBy1` symbol "*"

pTy :: Parser Ty
pTy = foldr1 Arr <$> pProd `sepBy1` symbol "->"

parseTy :: Text -> Either (ParseErrorBundle Text Void) Ty
parseTy = parse (pTy <* eof) ""

parseSigs :: FilePath -> Text -> Either (ParseErrorBundle Text Void) [(Text, Ty)]
parseSigs path = flip parse path $ many ((,) <$> pFunName <*> (symbol ":" *> pTy)) <* eof

--------------------------------------------------------------------------------

orDie :: (Exception e) => Either e a -> IO a
orDie = either (die . displayException) pure

helpText :: String
helpText = "Enter a type to query, :q to quit, or :h for help.\n\nType syntax:\n  <var>   ::= [a-z][a-zA-Z0-9]\n  <const> ::= [A-Z][a-zA-Z0-9]\n  <type>  ::= <var> | <const> | <const>(<type>, <type>, ...) | [<type>] | () | <type> * <type> | <type> -> <type>\n"

doSearch :: [(Text, Ty, NF)] -> String -> InputT IO ()
doSearch sigs input = case parseTy (T.pack input) of
  Left err -> outputStrLn (displayException err)
  Right query -> do
    let nfQuery = reduce $ freezeVars query
    forM_ sigs \(x, sig, nfSig) -> do
      matches <- liftIO $ LT.next $ nfMatches (nfSig, nfQuery)
      case matches of
        LT.Nil -> pure ()
        LT.Cons sub _ -> do
          let sub' = unreduce <$> M.filterWithKey (\k _ -> not $ isGen k) sub
          outputStrLn $ T.unpack x ++ " : " ++ prettyTy 0 sig ""
          outputStrLn $ "  by instantiating " ++ prettySubst sub' "\n"

main :: IO ()
main = do
  [path] <- getArgs
  src <- T.readFile path
  sigs <- orDie $ parseSigs path src
  let sigs' = map (\(x, sig) -> (x, sig, reduce sig)) sigs
  runInputT defaultSettings do
    outputStrLn helpText
    fix \loop -> do
      minput <- getInputLine "> "
      case minput of
        Nothing -> loop
        Just ":q" -> pure ()
        Just ":h" -> outputStrLn helpText >> loop
        Just input -> doSearch sigs' input >> loop
