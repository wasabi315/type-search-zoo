module Main where

import Control.Applicative (Alternative)
import Control.Exception (Exception (..))
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Logic
import Data.Char
import Data.Foldable
import Data.Function
import Data.List (inits, intersperse, tails)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Maybe
import Data.String
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Traversable
import Data.Unique
import Data.Void
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

choose :: (Alternative m, Foldable t) => t a -> m a
choose = foldr ((<|>) . pure) empty

--------------------------------------------------------------------------------
-- Matching problem vocabulary from Rittri 1990.

-- | A matching problem is a pair of two terms: a pattern and a subject.
-- We seek the set of all substitutions that make the pattern and subject equal.
type Matching t = (t, t)

-- | A matching system is a set of matching problems.
-- We seek the set of all substitutions that is the solution to *all* the matching problems in the system.
type MatchingSys t = [Matching t]

-- | A substitution is a mapping from names to terms.
type Subst t = Map Name t

composeSubst :: (Subst t -> t -> t) -> Subst t -> Subst t -> Subst t
composeSubst appSubst subst2 subst1 = M.map (appSubst subst2) subst1 <> subst2

-- Lift a algorithm for a matching problem to one for a matching system
liftForMatchingSys ::
  (Subst t -> t -> t) ->
  (Matching t -> LogicT m (Subst t)) ->
  (MatchingSys t -> LogicT m (Subst t))
liftForMatchingSys appSubst alg sys =
  foldM
    ( \accSubst (pat, subj) -> do
        let problem = (appSubst accSubst pat, subj)
        subst <- alg problem
        pure $ composeSubst appSubst subst accSubst
    )
    mempty
    sys

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
  | Const Name -- C (e.g. Int, Bool)
  | Unit -- ()
  | Ty `Prod` Ty -- t * u
  | Ty `Arr` Ty -- t -> u
  deriving stock (Eq, Ord, Show)

instance IsString Ty where
  fromString x = Var (fromString x)

-- | Converts all type variables to type constants.
freezeVars :: Ty -> Ty
freezeVars = \case
  Var x -> Const x
  Const c -> Const c
  Unit -> Unit
  a `Prod` b -> freezeVars a `Prod` freezeVars b
  a `Arr` b -> freezeVars a `Arr` freezeVars b

--------------------------------------------------------------------------------
-- Normal form of types
-- Unlike the NF in the Rittri89, we use lists instead of multisets because the product type here is not commutative.

infixr 5 `nfProd`

infix 4 `FArr`

infixr 4 `nfArr`

data Atom
  = AVar Name
  | AConst Name
  deriving stock (Show, Eq, Ord)

data Factor = NF `FArr` Atom
  deriving stock (Show, Eq, Ord)

type NF = [Factor]

-- a ~ () -> a
nfAtom :: Atom -> NF
nfAtom a = [nfUnit `FArr` a]

nfVar :: Name -> NF
nfVar v = nfAtom (AVar v)

nfConst :: Name -> NF
nfConst c = nfAtom (AConst c)

nfUnit :: NF
nfUnit = []

-- a * (b * c) ~ (a * b) * c
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
a `nfArr` b = map (nfArr' a) b

-- Reduce a type to its normal form
reduce :: Ty -> NF
reduce = \case
  Var x -> nfVar x
  Const c -> nfConst c
  Unit -> nfUnit
  a `Prod` b -> reduce a `nfProd` reduce b
  a `Arr` b -> reduce a `nfArr` reduce b

-- Convert a normal form to a type

unreduceAtom :: Atom -> Ty
unreduceAtom = \case
  AVar x -> Var x
  AConst c -> Const c

unreduceFactor :: Factor -> Ty
unreduceFactor = \case
  [] `FArr` b -> unreduceAtom b
  e `FArr` b -> unreduce e `Arr` unreduceAtom b

unreduce :: NF -> Ty
unreduce = \case
  [] -> Unit
  (f : fs) -> foldr (\g acc -> unreduceFactor g `Prod` acc) (unreduceFactor f) fs

-- Substitution for NF

nfSubstAtom :: Subst NF -> Atom -> NF
nfSubstAtom sub = \case
  a@(AVar x) -> fromMaybe (nfAtom a) (sub M.!? x)
  a -> nfAtom a

nfSubstFactor :: Subst NF -> Factor -> NF
nfSubstFactor sub (e `FArr` b) = nfSubst sub e `nfArr` nfSubstAtom sub b

nfSubst :: Subst NF -> NF -> NF
nfSubst subst a = concatMap (nfSubstFactor subst) a

--------------------------------------------------------------------------------
-- Exponent and base of a NF

-- Given a normal form (a1 -> b1) * (a2 -> b2) * ... * (an -> bn),
-- the exponent is the sequence of normal forms [a1, a2, ..., an].
-- The base is the sequence of atoms [b1, b2, ..., bn].
-- We write 't B b' if the term t has the base b, following the paper.

type Exponent = [NF]

type Base = [Atom]

exponent :: NF -> Exponent
exponent a = map (\(e `FArr` _) -> e) a

base :: NF -> Base
base a = map (\(_ `FArr` b) -> b) a

bsubst :: Subst Base -> Base -> Base
bsubst subst b =
  concatMap
    \case
      v@(AVar x) -> fromMaybe [v] (subst M.!? x)
      c@(AConst _) -> [c]
    b

--------------------------------------------------------------------------------

-- | A brute-force associative-unit matching algorithm
-- Assumes the subject does not contain any type variables
auMatch :: Matching Base -> [Subst Base]
auMatch = \(pat, subj) -> go M.empty pat subj
  where
    go subst = \cases
      -- Matching is done successfully so we return the substitution accumulated so far
      [] [] -> pure subst
      -- Matching is not possible so fail
      [] (_ : _) -> empty
      (AVar v : p) s -> do
        -- Try all possible ways of splitting the subject and assign the first part to the variable
        (s', s'') <- zip (inits s) (tails s)
        let -- New substitution
            subst' = M.insert v s' subst
            -- Apply the substitution to the rest of the pattern
            p' = bsubst subst' p
        -- Recursively match the rest of the pattern and subject
        go subst' p' s''
      (AConst _ : _) [] -> empty
      (AConst _ : _) (AVar _ : _) -> error "Type variable in subject"
      (AConst c : p) (AConst c' : s)
        -- If the constants match, continue matching the rest of the pattern and subject
        | c == c' -> go subst p s
        -- If the constants do not match, matching fails
        | otherwise -> empty

-- | Returns the most general type that has the given base
mostGeneral :: Base -> IO NF
mostGeneral b =
  traverse
    ( \a -> do
        y <- genName
        pure $ nfVar y `FArr` a
    )
    b

mostGeneralSubst :: Subst Base -> IO (Subst NF)
mostGeneralSubst bsub = traverse mostGeneral bsub

-- | Entrypoint: match a pattern with a subject and return all possible substitutions.
-- Assumes the subject does not contain any type variables.
nfMatches :: Matching NF -> LogicT IO (Subst NF)
nfMatches (pat, subj) = do
  -- Perform associative-unit matching on the bases to get a list of possible substitutions
  bsubst <- choose $ auMatch (base pat, base subj)
  -- Bring the substitution in the "base world" to the "NF world"
  nsubst <- liftIO $ mostGeneralSubst bsubst
  -- Apply the substitution to the pattern
  let pat' = nfSubst nsubst pat
  -- Recursively match the pattern and subject
  nsubst' <- liftForMatchingSys nfSubst nfMatches (equivMatchingSys (pat', subj))
  -- Compose the substitutions
  pure $ composeSubst nfSubst nsubst' nsubst

-- | Extract a matching system that is equivalent to the given matching problem.
-- Assumes the pattern and subject have a common base.
equivMatchingSys :: Matching NF -> MatchingSys NF
equivMatchingSys (pat, subj) =
  -- If the base of the pattern and subject are the same, then the matching problem is equivalent to the matching system where each matching problem is the corresponding pair of normal forms from the exponent of the pattern and subject.
  -- Note that the length of the exponent of the pattern and subject are the same because the base is the same.
  zip (exponent pat) (exponent subj)

--------------------------------------------------------------------------------
-- Pretty printing

prettyTy :: Int -> Ty -> ShowS
prettyTy p = \case
  Var v -> shows v
  Const c -> shows c
  Unit -> showString "()"
  a `Prod` b -> showParen (p > 5) $ prettyTy 6 a . showString " * " . prettyTy 5 b
  a `Arr` b -> showParen (p > 4) $ prettyTy 5 a . showString " -> " . prettyTy 4 b

enclose :: ShowS -> ShowS -> ShowS -> ShowS
enclose l r x = l . x . r

punctuate :: ShowS -> [ShowS] -> ShowS
punctuate sep xs = foldr (.) id (intersperse sep xs)

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

pVarOrConst :: Parser Ty
pVarOrConst = lexeme do
  n <- takeWhile1P (Just "type variable or type constant") isAlphaNum
  if
    | isLower (T.head n) -> pure (Var (Name n))
    | isUpper (T.head n) -> pure (Const (Name n))
    | otherwise -> empty

pAtom :: Parser Ty
pAtom =
  pVarOrConst
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
helpText = "Enter a type to query, :q to quit, or :h for help.\n\nType syntax:\n  <var>   ::= [a-z][a-zA-Z0-9]\n  <const> ::= [A-Z][a-zA-Z0-9]\n  <type>  ::= <var> | <const> | () | <type> * <type> | <type> -> <type>\n"

doSearch :: [(Text, Ty, NF)] -> String -> InputT IO ()
doSearch sigs input = case parseTy (T.pack input) of
  Left err -> outputStrLn (displayException err)
  Right query -> do
    let nfQuery = reduce $ freezeVars query
    forM_ sigs \(x, sig, nfSig) -> do
      matches <- liftIO $ observeManyT 1 $ nfMatches (nfSig, nfQuery)
      case matches of
        [sub] -> do
          let sub' = unreduce <$> M.filterWithKey (\k _ -> not $ isGen k) sub
          outputStrLn $ T.unpack x ++ " : " ++ prettyTy 0 sig ""
          outputStrLn $ "  by instantiating " ++ prettySubst sub' "\n"
        _ -> pure ()

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
