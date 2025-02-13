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
  fromString x = Var (fromString x)

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

-- To make search results insensitive to currying/uncurrying and argument order,
-- we define type equivalence using the following axioms (Rittri, 1989):
--   1.         a * b = b * a
--   2.   a * (b * c) = (a * b) * c
--   3.   a -> b -> c = (a * b) -> c
--   4.  a -> (b * c) = (a -> b) * (a -> c)
--   5.        () * a = a
--   6.       () -> a = a
--   7.       a -> () = ()
--
-- The algorithm proceeds in two steps:
--   i. Rewrite types by applying axioms (3-7):
--      - Push products in return types of functions outward
--      - Uncurry functions as much as possible
--      - Eliminate unit types
--   ii. Compare types recursively by multiset equality (axiom 1-2):
--      - For function types: compare their argument types as multisets and their return types
--      - For product types: compare their components as multisets
--      - For list types: compare their element types
--
-- Example: Comparing (a -> b -> b) -> b -> [a] -> b and (b * a -> b) * [a] -> b -> b
--   i. (a -> b -> b) -> b -> [a] -> b ~> (a * b -> b) * b * [a] -> b
--      (b * a -> b) * b -> [a] -> b   ~> (b * a -> b) * [a] * b -> b
--   ii. The comparison proceeds recursively:
--      1. Compare the multisets of top-level factors:
--         {(a * b -> b), b, [a]} and {(b * a -> b), [a], b}
--      2. For function factors (a * b -> b) and (b * a -> b):
--         - Their argument types a * b and b * a are equal as multisets
--         - Their return types b and b are equal
--      3. For list factors [a] and [a]: their element types are equal
--      4. For atomic factors b and b: they are equal
--      Therefore, the types are equivalent.
--
-- NF is the normal form of a type, which is the result of the step i above.
-- It is defined as the multiset of factors so the derived Eq instance will perform the step ii above.

infix 4 `FArr`

infixr 4 `nfArr`

data Atom
  = AVar Name
  | AList NF
  deriving stock (Show, Eq, Ord)

data Factor = NF `FArr` Atom
  deriving stock (Show, Eq, Ord)

type NF = MultiSet Factor

-- It is possible to directly reduce the types to NF!

nfAtom :: Atom -> NF
nfAtom a = MS.singleton (mempty `FArr` a)

-- x ~ () -> x
nfVar :: Name -> NF
nfVar x = nfAtom (AVar x)

-- [t] ~ () -> [t]
nfList :: NF -> NF
nfList a = nfAtom (AList a)

nfArr' :: NF -> Factor -> Factor
nfArr' a (e `FArr` b) = (a <> e) `FArr` b

nfArr :: NF -> NF -> NF
nfArr a b = MS.map (nfArr' a) b

reduce :: Ty -> NF
reduce = \case
  Var x -> nfVar x
  Unit -> mempty
  a `Prod` b -> reduce a <> reduce b
  a `Arr` b -> reduce a `nfArr` reduce b
  List a -> nfList (reduce a)

-- Entrypoint: check if two types are equivalent in the normal form (modulo α-equivalence)
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
orDie = either (\e -> putStrLn (displayException e) >> exitFailure) pure

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
