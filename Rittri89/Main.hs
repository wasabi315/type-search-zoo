module Main where

import Control.Exception (Exception (..))
import Control.Monad
import Data.Char
import Data.Function
import Data.List (permutations)
import Data.Maybe
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
  = Var Name
  | Unit
  | Ty `Prod` Ty
  | Ty `Arr` Ty
  | List Ty
  deriving stock (Show)

instance IsString Ty where
  fromString x = Var (fromString x)

--------------------------------------------------------------------------------
-- Normal form of types

infix 4 `NFArr`

data Atom
  = AVar Name
  | AList NF
  deriving stock (Show, Eq, Ord)

data Factor = NF `NFArr` Atom
  deriving stock (Show, Eq, Ord)

type NF = MultiSet Factor

--------------------------------------------------------------------------------
-- Main algorithm

{-

Original code from the paper:

red :: Ty -> Ty
red (Var x) = Var x
red Unit = Unit
red (a :* b) = case (red a, red b) of
  (Unit, b) -> b
  (a, Unit) -> a
  (a, b) -> a :* b
red (a :-> b) = case (red a, red b) of
  (Unit, a) -> a
  (a, b :-> c) -> (a :* b) :-> c
  (_, Unit) -> Unit
  (a, b :* c) -> red (a :-> b) :* red (a :-> c)
  (a, b) -> a :-> b
red (List a) = List (red a)

chtype :: Ty -> NF
chtype (Var x) = MS.singleton (mempty :=> x)
chtype (x :-> Var y) = MS.singleton (chtype x :=> y)
chtype (_ :-> _) = error "not normal"
chtype Unit = mempty
chtype (a :* b) = chtype a <> chtype b
chtype (List a) = undefined

equiv :: Ty -> Ty -> Bool
equiv a b = chtype (red a) == chtype (red b)

-}

tyvars :: Ty -> Set Name
tyvars = \case
  Var x -> S.singleton x
  Unit -> S.empty
  a `Prod` b -> tyvars a <> tyvars b
  a `Arr` b -> tyvars a <> tyvars b
  List a -> tyvars a

possibleRenamings :: Ty -> Ty -> [[(Name, Name)]]
possibleRenamings a b = do
  let avars = S.toList $ tyvars a
      bvars = S.toList $ tyvars b
  guard $ length avars == length bvars
  flip zip avars <$> permutations bvars

rename :: [(Name, Name)] -> Ty -> Ty
rename r = \case
  Var x -> Var $ fromJust $ lookup x r
  Unit -> Unit
  a `Prod` b -> rename r a `Prod` rename r b
  a `Arr` b -> rename r a `Arr` rename r b
  List a -> List $ rename r a

atom :: Atom -> NF
atom a = MS.singleton (mempty `NFArr` a)

var :: Name -> NF
var x = atom (AVar x)

list :: NF -> NF
list a = atom (AList a)

(-->) :: NF -> NF -> NF
(-->) a = MS.map (\(b `NFArr` x) -> (a <> b) `NFArr` x)

reduce :: Ty -> NF
reduce = \case
  Var x -> var x
  Unit -> mempty
  a `Prod` b -> reduce a <> reduce b
  a `Arr` b -> reduce a --> reduce b
  List a -> list (reduce a)

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
