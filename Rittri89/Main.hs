module Main where

import Control.Exception (Exception (..))
import Control.Monad
import Data.Char
import Data.Function
import Data.List (permutations)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.MultiSet (MultiSet)
import Data.MultiSet qualified as MS
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Void
import System.Console.Haskeline
import System.Environment
import System.Exit
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

--------------------------------------------------------------------------------
-- Types

infixr 5 `Prod`

infixr 4 `Arr`

type Name = Text

data Scheme = Scheme [Name] Ty
  deriving stock (Show)

data Ty
  = Var Name -- x
  | Unit -- ()
  | Ty `Prod` Ty -- t * u
  | Ty `Arr` Ty -- t -> u
  | List Ty -- [t]
  deriving stock (Show)

freeVarSet :: Ty -> Set Name
freeVarSet = \case
  Var x -> S.singleton x
  Unit -> S.empty
  a `Prod` b -> freeVarSet a <> freeVarSet b
  a `Arr` b -> freeVarSet a <> freeVarSet b
  List a -> freeVarSet a

closeTy :: Ty -> Scheme
closeTy a = Scheme xs a
  where
    xs = S.toList $ freeVarSet a

type Rename = Map Name Name

rename :: Rename -> Ty -> Ty
rename ren = \case
  Var x -> Var (ren M.! x)
  Unit -> Unit
  a `Prod` b -> rename ren a `Prod` rename ren b
  a `Arr` b -> rename ren a `Arr` rename ren b
  List a -> List (rename ren a)

--------------------------------------------------------------------------------
-- Main algorithm

-- To make search insensitive to currying/uncurrying and argument order,
-- we adopt the following type isomorphisms as axioms:
--   1.         a * b = b * a
--   2.   a * (b * c) = (a * b) * c
--   3.   a -> b -> c = (a * b) -> c
--   4.  a -> (b * c) = (a -> b) * (a -> c)
--   5.        () * a = a
--   6.       () -> a = a
--   7.       a -> () = ()
--
-- The algorithm proceeds in two steps:
--   i.  Rewrite types by applying axioms (3) to (7):
--   ii. Compare types by multiset equality (axioms (1) and (2)):
--
-- The normal form @NF@ of a type is the result of step i.
-- By the axioms, product types at return types of functions are pushed outward, arguments are uncurried, and unit types are eliminated, hence the shape.
-- Step ii is automatic in this implementation because we use @MultiSet@ to represent @NF@!

infixr 5 `nfProd`

infix 4 `FArr`, `nfArr'`, `nfArr`

data Atom
  = AVar Name
  | AList NF
  deriving stock (Show, Eq, Ord)

data Factor = NF `FArr` Atom
  deriving stock (Show, Eq, Ord)

type NF = MultiSet Factor

nfAtom :: Atom -> NF
nfAtom a = MS.singleton (nfUnit `FArr` a)

nfVar :: Name -> NF
nfVar x = nfAtom (AVar x)

nfList :: NF -> NF
nfList a = nfAtom (AList a)

nfUnit :: NF
nfUnit = mempty

nfProd :: NF -> NF -> NF
a `nfProd` b = a <> b

-- a -> (e -> b) ~ (a * e) -> b
nfArr' :: NF -> Factor -> Factor
a `nfArr'` (e `FArr` b) = (a <> e) `FArr` b

-- a -> (b1 * b2 * ... * bn) ~ (a -> b1) * (a -> b2) * ... * (a -> bn)
nfArr :: NF -> NF -> NF
a `nfArr` b = MS.map (nfArr' a) b

-- Normalise type into NF
reduce :: Ty -> NF
reduce = \case
  Var x -> nfVar x
  Unit -> nfUnit
  a `Prod` b -> reduce a `nfProd` reduce b
  a `Arr` b -> reduce a `nfArr` reduce b
  List a -> nfList (reduce a)

-- check if two types are equal modulo the axioms and α-equivalence
equiv :: Scheme -> Scheme -> Bool
equiv (Scheme xs _) (Scheme ys _)
  -- check the schemes bind the same number of variables
  | length xs /= length ys = False
equiv (Scheme xs a) (Scheme ys b) =
  any (\ren -> a' == reduce (rename ren b)) rens
  where
    a' = reduce a
    -- possible renamings
    rens = M.fromList . flip zip xs <$> permutations ys

-- entrypoint
search :: [(Name, Scheme)] -> Scheme -> [(Name, Scheme)]
search sigs query =
  filter
    (\(_, sig) -> equiv sig query)
    sigs

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

pName :: Parser Name
pName = lexeme $ takeWhile1P (Just "name") isAlphaNum

pAtom :: Parser Ty
pAtom =
  (Var <$> pName)
    <|> try (Unit <$ symbol "()")
    <|> parens pTy
    <|> brackets (List <$> pTy)

pProd :: Parser Ty
pProd = foldr1 Prod <$> pAtom `sepBy1` symbol "*"

pTy :: Parser Ty
pTy = foldr1 Arr <$> pProd `sepBy1` symbol "->"

pScheme :: Parser Scheme
pScheme = do
  xs <- option [] do
    _ <- symbol "forall"
    xs <- many pName
    _ <- symbol "."
    pure xs
  Scheme xs <$> pTy

parseTy :: Text -> Either (ParseErrorBundle Text Void) Ty
parseTy = parse (pTy <* eof) ""

parseSigs :: FilePath -> Text -> Either (ParseErrorBundle Text Void) [(Name, Scheme)]
parseSigs path = flip parse path $ many ((,) <$> pName <*> (symbol ":" *> pScheme)) <* eof

prettyTy :: Int -> Ty -> ShowS
prettyTy p = \case
  Var x -> showString (T.unpack x)
  Unit -> showString "()"
  a `Prod` b -> showParen (p > 5) $ prettyTy 6 a . showString " * " . prettyTy 5 b
  a `Arr` b -> showParen (p > 4) $ prettyTy 5 a . showString " -> " . prettyTy 4 b
  List a -> showString "[" . prettyTy 0 a . showString "]"

prettyScheme :: Scheme -> ShowS
prettyScheme (Scheme xs a) =
  showString "forall"
    . foldr ((.) . (showChar ' ' .) . showString . T.unpack) id xs
    . showString ". "
    . prettyTy 0 a

--------------------------------------------------------------------------------

orDie :: (Exception e) => Either e a -> IO a
orDie = either (die . displayException) pure

helpText :: String
helpText = "Enter a type to query, :q to quit, or :h for help.\nType syntax:\n  <var>  ::= [a-z][a-zA-Z0-9]\n  <type> ::= <var> | () | <type> * <type> | <type> -> <type> | [<type>]"

main :: IO ()
main = do
  [path] <- getArgs
  sigs <- orDie . parseSigs path =<< T.readFile path
  runInputT defaultSettings do
    outputStrLn helpText
    fix \loop -> do
      minput <- getInputLine "> "
      case minput of
        Nothing -> loop
        Just ":q" -> pure ()
        Just ":h" -> outputStrLn helpText >> loop
        Just input -> case parseTy (T.pack input) of
          Left e -> outputStrLn (displayException e) >> loop
          Right (closeTy -> query) -> do
            let matches = search sigs query
            forM_ matches \(x, a) -> do
              outputStrLn $ T.unpack x ++ " : " ++ prettyScheme a ""
            loop
