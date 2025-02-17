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
import Data.String
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

data Ty
  = Var Name -- x
  | Unit -- ()
  | Ty `Prod` Ty -- t * u
  | Ty `Arr` Ty -- t -> u
  | List Ty -- [t]
  deriving stock (Show)

instance IsString Ty where
  fromString x = Var (T.pack x)

varSet :: Ty -> Set Name
varSet = \case
  Var x -> S.singleton x
  Unit -> S.empty
  a `Prod` b -> varSet a <> varSet b
  a `Arr` b -> varSet a <> varSet b
  List a -> varSet a

type Rename = Map Name Name

possibleRenamings :: Ty -> Ty -> [Rename]
possibleRenamings a b = do
  let avars = S.toList $ varSet a
      bvars = S.toList $ varSet b
  guard $ length avars == length bvars
  M.fromList . flip zip avars <$> permutations bvars

rename :: Rename -> Ty -> Ty
rename r = \case
  Var x -> Var $ r M.! x
  Unit -> Unit
  a `Prod` b -> rename r a `Prod` rename r b
  a `Arr` b -> rename r a `Arr` rename r b
  List a -> List $ rename r a

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

infix 4 `FArr`

infix 4 `nfArr'`

infixr 4 `nfArr`

data Atom
  = AVar Name
  | AList NF
  deriving stock (Show, Eq, Ord)

data Factor = NF `FArr` !Atom
  deriving stock (Show, Eq, Ord)

type NF = MultiSet Factor

-- It is possible to directly reduce types into NF!

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

reduce :: Ty -> NF
reduce = \case
  Var x -> nfVar x
  Unit -> nfUnit
  a `Prod` b -> reduce a `nfProd` reduce b
  a `Arr` b -> reduce a `nfArr` reduce b
  List a -> nfList (reduce a)

-- Entrypoint: check if two types are equal modulo the axioms and α-equivalence
equiv :: Ty -> Ty -> Bool
equiv a b =
  let a' = reduce a
      rs = possibleRenamings a b
   in any (\r -> a' == reduce (rename r b)) rs

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

parseTy :: Text -> Either (ParseErrorBundle Text Void) Ty
parseTy = parse (pTy <* eof) ""

parseSigs :: FilePath -> Text -> Either (ParseErrorBundle Text Void) [(Name, Ty)]
parseSigs path = flip parse path $ many ((,) <$> pName <*> (symbol ":" *> pTy)) <* eof

prettyTy :: Int -> Ty -> ShowS
prettyTy p = \case
  Var x -> showString (T.unpack x)
  Unit -> showString "()"
  a `Prod` b -> showParen (p > 5) $ prettyTy 6 a . showString " * " . prettyTy 5 b
  a `Arr` b -> showParen (p > 4) $ prettyTy 5 a . showString " -> " . prettyTy 4 b
  List a -> showString "[" . prettyTy 0 a . showString "]"

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
          Right query -> do
            forM_ sigs \(x, a) -> do
              when (equiv query a) do
                outputStrLn $ T.unpack x ++ " : " ++ prettyTy 0 a ""
            loop
