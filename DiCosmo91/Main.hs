module Main where

import Control.Exception (Exception (..))
import Control.Monad
import Control.Monad.IO.Class
import Data.Char
import Data.Function
import Data.List (intersperse, permutations)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Set (Set)
import Data.Set qualified as S
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
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

--------------------------------------------------------------------------------
-- Types

infixr 5 `Prod`

infixr 4 `Arr`

type Name = Text

data Ty n
  = Var n -- x
  | Unit -- ()
  | Ty n `Prod` Ty n -- t * u
  | Ty n `Arr` Ty n -- t -> u
  | List (Ty n) -- [t]
  | Forall n (Ty n) -- ∀x. t
  deriving stock (Show)

instance (IsString n) => IsString (Ty n) where
  fromString x = Var (fromString x)

freeVarSet :: (Ord n) => Ty n -> Set n
freeVarSet = \case
  Var x -> S.singleton x
  Unit -> S.empty
  a `Prod` b -> freeVarSet a <> freeVarSet b
  a `Arr` b -> freeVarSet a <> freeVarSet b
  List a -> freeVarSet a
  Forall x a -> S.delete x (freeVarSet a)

type Rename n = Map n n

-- Close an open type by adding Foralls for all free variables
close :: (Ord n) => Ty n -> Ty n
close t = foldr Forall t (freeVarSet t)

--------------------------------------------------------------------------------
-- Main algorithm
-- Axioms:
--   1.            a * b = b * a
--   2.      a * (b * c) = (a * b) * c
--   3.      a -> b -> c = (a * b) -> c
--   4.     a -> (b * c) = (a -> b) * (a -> c)
--   5.           () * a = a
--   6.          () -> a = a
--   7.          a -> () = ()
--   8.    forall x y. a = forall y x. a
--   9.      forall x. a = forall y. a[x:=y]           (if y not free in a)
--  10. forall x. a -> b = a -> forall x. b            (if x not free in a)
--  11.  forall x. a * b = forall x. a * forall x. b
--  12.     forall x. () = ()
--
-- The algorithm is much like one in the Rittri89 folder, but handles quantifiers and names.
-- Differences:
--   * Factors have the shape forall x1 .. xn. a1 * ... * am -> b instead.
--   * Freshen names during reduction in order to avoid name capture.

infixr 5 `nfProd`

infix 4 `nfArr'`

infixr 4 `nfArr`

data UName = UName Unique Name
  deriving stock (Eq, Ord)

instance Show UName where
  show (UName u n) = T.unpack n ++ "$" ++ show (hashUnique u)

data Atom
  = AVar UName
  | AList NF
  deriving stock (Show, Eq, Ord)

data Factor = Factor (Set UName) NF Atom
  deriving stock (Show, Eq, Ord)

type NF = [Factor]

renameAtom :: Rename UName -> Atom -> Atom
renameAtom ren = \case
  v@(AVar x) -> maybe v AVar $ ren M.!? x
  AList a -> AList $ renameNF ren a

renameFactor :: Rename UName -> Factor -> Factor
renameFactor ren (Factor vs e b) =
  Factor vs (renameNF ren' e) (renameAtom ren' b)
  where
    ren' = M.withoutKeys ren vs

renameNF :: Rename UName -> NF -> NF
renameNF ren = map (renameFactor ren)

nfAtom :: Atom -> NF
nfAtom a = [Factor S.empty nfUnit a]

nfVar :: UName -> NF
nfVar x = nfAtom (AVar x)

nfList :: NF -> NF
nfList x = nfAtom (AList x)

nfUnit :: NF
nfUnit = []

nfProd :: NF -> NF -> NF
a `nfProd` b = a ++ b

-- a -> (forall v. e -> b) ~ forall v. (a * e -> b) (if v is not free in a)
nfArr' :: NF -> Factor -> Factor
a `nfArr'` Factor vs e b = Factor vs (a <> e) b

-- a -> (b1 * b2 * ... * bn) ~ (a -> b1) * (a -> b2) * ... * (a -> bn)
nfArr :: NF -> NF -> NF
a `nfArr` b = map (nfArr' a) b

nfForall' :: UName -> Factor -> Factor
nfForall' v (Factor vs e b) = Factor (S.insert v vs) e b

nfForall :: UName -> NF -> NF
nfForall a b = map (nfForall' a) b

reduce :: Map Name UName -> Ty Name -> IO NF
reduce ren = \case
  Var x -> pure $ nfVar (ren M.! x)
  Unit -> pure nfUnit
  a `Prod` b -> liftA2 nfProd (reduce ren a) (reduce ren b)
  a `Arr` b -> liftA2 nfArr (reduce ren a) (reduce ren b)
  List a -> nfList <$> reduce ren a
  Forall x a -> do
    u <- newUnique
    let x' = UName u x
    nfForall x' <$> reduce (M.insert x x' ren) a

unreduceAtom :: Atom -> Ty UName
unreduceAtom = \case
  AVar x -> Var x
  AList xs -> List $ unreduce xs

unreduceFactor :: Factor -> Ty UName
unreduceFactor (Factor vs e b) =
  addForall $ addArr $ unreduceAtom b
  where
    addForall t = if S.null vs then t else foldr Forall t vs
    addArr t = if null e then t else unreduce e `Arr` t

unreduce :: NF -> Ty UName
unreduce = \case
  [] -> Unit
  (f : fs) -> foldr (Prod . unreduceFactor) (unreduceFactor f) fs

equivAtom :: Atom -> Atom -> Bool
equivAtom = \cases
  (AVar px) (AVar sx) -> px == sx
  (AList a) (AList b) -> equivNF a b
  _ _ -> False

possibleRenamings :: Set UName -> Set UName -> [Rename UName]
possibleRenamings (S.toList -> vs) (S.toList -> vs') = do
  guard $ length vs == length vs'
  M.fromList . flip zip vs <$> permutations vs'

equivFactor :: Factor -> Factor -> Bool
equivFactor (Factor pvs pe pb) (Factor svs se sb) =
  flip any (possibleRenamings pvs svs) \ren ->
    let se' = renameNF ren se
        sb' = renameAtom ren sb
     in equivAtom pb sb' && equivNF pe se'

equivNF :: NF -> NF -> Bool
equivNF pat subj
  | length pat /= length subj = False
equivNF pat subj =
  flip any (permutations pat) \pat' ->
    and (zipWith equivFactor pat' subj)

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

pAtom :: Parser (Ty Name)
pAtom =
  (Var <$> pName)
    <|> try (Unit <$ symbol "()")
    <|> parens pTy
    <|> List
    <$> brackets pTy

pProd :: Parser (Ty Name)
pProd = foldr1 Prod <$> pAtom `sepBy1` symbol "*"

pArr :: Parser (Ty Name)
pArr = foldr1 Arr <$> pProd `sepBy1` symbol "->"

pTy :: Parser (Ty Name)
pTy =
  ( do
      xs <- symbol "forall" *> some pName <* symbol "."
      t <- pTy
      pure $ foldr Forall t xs
  )
    <|> pArr

parseTy :: Text -> Either (ParseErrorBundle Text Void) (Ty Name)
parseTy = parse (pTy <* eof) ""

parseSigs :: FilePath -> Text -> Either (ParseErrorBundle Text Void) [(Name, Ty Name)]
parseSigs path = flip parse path $ many ((,) <$> pName <*> (symbol ":" *> pTy)) <* eof

punctuate :: ShowS -> [ShowS] -> ShowS
punctuate sep xs = foldr (.) id (intersperse sep xs)

prettyTy :: (n -> ShowS) -> Int -> Ty n -> ShowS
prettyTy var = \p -> \case
  Var x -> var x
  Unit -> showString "()"
  a `Prod` b -> showParen (p > 5) $ prettyTy var 6 a . showString " * " . prettyTy var 5 b
  a `Arr` b -> showParen (p > 4) $ prettyTy var 5 a . showString " -> " . prettyTy var 4 b
  List a -> showChar '[' . prettyTy var 0 a . showChar ']'
  Forall x a -> goForall p [x] a
  where
    goForall p xs = \case
      Forall x a -> goForall p (x : xs) a
      a ->
        showParen (p > 0) $
          showString "forall "
            . punctuate (showChar ' ') (map var (reverse xs))
            . showString ". "
            . prettyTy var 0 a

--------------------------------------------------------------------------------

orDie :: (Exception e) => Either e a -> IO a
orDie = either (die . displayException) pure

helpText :: String
helpText = "Enter a type to query, :q to quit, or :h for help.\nType syntax:\n  <var>  ::= [a-z][a-zA-Z0-9]\n  <type> ::= <var> | () | <type> * <type> | <type> -> <type> | [<type>] | forall <var>. <type>"

main :: IO ()
main = do
  [path] <- getArgs
  sigs <- orDie . parseSigs path =<< T.readFile path
  sigs' <- for sigs \(x, close -> a) -> (x,a,) <$> reduce M.empty a
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
            query' <- liftIO $ reduce M.empty (close query)
            forM_ sigs' \(x, a, na) -> do
              when (equivNF query' na) do
                outputStrLn $ T.unpack x ++ " : " ++ prettyTy (showString . T.unpack) 0 a ""
            loop
