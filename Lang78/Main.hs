module Main where

import Control.Exception (Exception (..))
import Control.Monad
import Control.Monad.IO.Class
import Data.Char
import Data.Foldable
import Data.Function
import Data.List (inits, intersperse, tails)
import Data.Map.Merge.Strict qualified as M
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Maybe
import Data.Monoid
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

-- | Like @insert@, but returns Nothing if the key already exists with a different value.
insertNoConflict :: (Ord k, Eq a) => k -> a -> Map k a -> Maybe (Map k a)
insertNoConflict k v =
  M.alterF
    \case
      Just v' | v /= v' -> Nothing
      _ -> Just (Just v)
    k

-- | Like @union@, but returns Nothing if the two maps have conflicting values.
unionNoConflict :: (Ord k, Eq a) => Map k a -> Map k a -> Maybe (Map k a)
unionNoConflict =
  M.mergeA
    M.preserveMissing
    M.preserveMissing
    (M.zipWithAMatched \_ x y -> if x == y then Just x else Nothing)

-- | Like @unions@, but returns Nothing if the maps have conflicting values.
unionsNoConflict :: (Ord k, Eq a, Foldable t) => t (Map k a) -> Maybe (Map k a)
unionsNoConflict = foldlM unionNoConflict M.empty

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

type Subst = Map Name Ty

--------------------------------------------------------------------------------
-- Normal form of types

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

type NFSubst = Map Name NF

nfSubstAtom :: NFSubst -> Atom -> NF
nfSubstAtom sub = \case
  a@(AVar x) -> fromMaybe (nfAtom a) (sub M.!? x)
  a -> nfAtom a

nfSubstFactor :: NFSubst -> Factor -> NF
nfSubstFactor sub (e `FArr` b) = nfSubst sub e `nfArr` nfSubstAtom sub b

nfSubst :: NFSubst -> NF -> NF
nfSubst sub a = concatMap (nfSubstFactor sub) a

nfSubstCompose :: NFSubst -> NFSubst -> NFSubst
nfSubstCompose a b = M.map (nfSubst a) b <> a

--------------------------------------------------------------------------------
-- Exponent and base of a NF

type Exponent = [NF]

type Base = [Atom]

exponent :: NF -> Exponent
exponent a = map (\(e `FArr` _) -> e) a

base :: NF -> Base
base a = map (\(_ `FArr` b) -> b) a

-- Substitution for Base
type BSubst = Map Name Base

--------------------------------------------------------------------------------

infix 4 `baseMatches`

infix 4 `nfMatches`

-- Associative matching of two bases
-- Assumes the subject does not contain any type variables
baseMatches :: Base -> Base -> [BSubst]
baseMatches = go M.empty
  where
    go sub = \cases
      [] [] -> pure sub
      [] (_ : _) -> empty
      (AVar v : p) s -> do
        (s', s'') <- zip (inits s) (tails s)
        sub' <- maybeToList $ insertNoConflict v s' sub
        go sub' p s''
      (AConst _ : _) [] -> empty
      (AConst _ : _) (AVar _ : _) -> error "Type variable in subject"
      (AConst c : p) (AConst c' : s)
        | c == c' -> go sub p s
        | otherwise -> empty

-- Returns the most general type that has the given base
mostGeneral :: Base -> IO NF
mostGeneral b =
  traverse
    ( \a -> do
        y <- genName
        pure $ nfVar y `FArr` a
    )
    b

mostGeneralSubst :: BSubst -> IO NFSubst
mostGeneralSubst bsub = traverse mostGeneral bsub

-- Entrypoint: tries to match a pattern against a subject and returns all possible substitutions
-- Assumes the subject does not contain any type variables
nfMatches :: NF -> NF -> IO [NFSubst]
nfMatches pat subj = do
  let bsubs = base pat `baseMatches` base subj
      expSubj = exponent subj
  concat <$> for bsubs \bsub -> do
    nsub <- mostGeneralSubst bsub
    nsubs <- zipWithM nfMatches (exponent (nfSubst nsub pat)) expSubj

    let nsubs' = map (`nfSubstCompose` nsub) $ mapMaybe unionsNoConflict $ sequence nsubs

    pure nsubs'

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

prettySubst :: Subst -> ShowS
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
  n <- takeWhile1P (Just "fun") isAlphaNum
  guard $ isLower (T.head n)
  pure n

pVarOrConst :: Parser Ty
pVarOrConst = lexeme do
  n <- takeWhile1P (Just "var or const") isAlphaNum
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
      matches <- liftIO $ nfSig `nfMatches` nfQuery
      case matches of
        [] -> pure ()
        sub : _ -> do
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
