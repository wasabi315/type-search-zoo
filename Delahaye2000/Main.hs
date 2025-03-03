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
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as S
import Data.String
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Unique
import Data.Void
import System.Console.Haskeline
import System.Environment
import System.Exit
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

--------------------------------------------------------------------------------
-- Utils

-- Multiset equality. O(n^2).
multisetEq :: (a -> b -> Bool) -> [a] -> [b] -> Bool
multisetEq p = \cases
  [] [] -> True
  [] _ -> False
  _ [] -> False
  (x : xs) ys -> case break (p x) ys of
    (_, []) -> False
    (ys1, _ : ys2) -> multisetEq p xs (ys1 ++ ys2)

------------------------------------------------------------------------------
-- Terms

type Name = Text

data UName
  = Local Unique Name
  | Top Name -- We refer to top-level names as-is
  deriving stock (Eq, Ord)

instance Show UName where
  show = \case
    Local u n -> T.unpack n <> "$" <> show (hashUnique u)
    Top n -> T.unpack n

data Term n
  = Type
  | Var n -- x
  | Unit -- ()
  | TT -- tt : ()
  | Pi n (Type n) (Type n) -- (x : A) -> B
  | Abs n (Type n) (Term n) -- \x : A. t
  | App (Term n) (Term n) -- t u
  | Sigma n (Type n) (Type n) -- (x : A) * B
  | Pair (Term n) (Term n) -- (t, u)
  | Fst (Term n) -- π1
  | Snd (Term n) -- π2
  deriving stock (Show)

type Type = Term

instance (IsString n) => IsString (Term n) where
  fromString x = Var (fromString x)

--------------------------------------------------------------------------------

freshen :: Term Name -> IO (Term UName)
freshen = go mempty
  where
    go ren = \case
      Var x -> pure $ Var $ fromMaybe (Top x) (ren M.!? x)
      Unit -> pure Unit
      TT -> pure TT
      Type -> pure Type
      Pair a b -> Pair <$> go ren a <*> go ren b
      Fst a -> Fst <$> go ren a
      Snd a -> Snd <$> go ren a
      Pi x a b -> do
        u <- newUnique
        let x' = Local u if x == "_" then "x" else x
        Pi x' <$> go ren a <*> go (M.insert x x' ren) b
      Abs x a b -> do
        u <- newUnique
        let x' = Local u if x == "_" then "x" else x
        Abs x' <$> go ren a <*> go (M.insert x x' ren) b
      Sigma x a b -> do
        u <- newUnique
        let x' = Local u if x == "_" then "x" else x
        Sigma x' <$> go ren a <*> go (M.insert x x' ren) b
      App a b -> App <$> go ren a <*> go ren b

freeVarSet :: (Ord n) => Term n -> Set n
freeVarSet = \case
  Var x -> S.singleton x
  Unit -> S.empty
  TT -> S.empty
  Type -> S.empty
  Pi x a b -> freeVarSet a <> S.delete x (freeVarSet b)
  Abs x a b -> freeVarSet a <> S.delete x (freeVarSet b)
  Sigma x a b -> freeVarSet a <> S.delete x (freeVarSet b)
  Pair a b -> freeVarSet a <> freeVarSet b
  Fst a -> freeVarSet a
  Snd a -> freeVarSet a
  App a b -> freeVarSet a <> freeVarSet b

-- Substitute a free variable @from@ inside @t@ with @to@.
-- Assumes the Barendregt convention.
subst :: UName -> Term UName -> Term UName -> Term UName
subst from to = go
  where
    go = \case
      v@(Var x)
        | x == from -> to
        | otherwise -> v
      Unit -> Unit
      TT -> TT
      Type -> Type
      Pair a b -> Pair (go a) (go b)
      Fst a -> Fst (go a)
      Snd a -> Snd (go a)
      App a b -> App (go a) (go b)
      Pi x a b -> Pi x (go a) (go b)
      Abs x a b -> Abs x (go a) (go b)
      Sigma x a b -> Sigma x (go a) (go b)

rename :: UName -> UName -> Term UName -> Term UName
rename from to = subst from (Var to)

--------------------------------------------------------------------------------
-- Main algorithm
-- Rewriting is done in three phases to ensure confluence.
-- Assumes the Barendregt convention.

-- Eliminate nested sigmas in the domain part of sigmas/pis.
reduce1 :: Term UName -> Term UName
reduce1 = \case
  -- (x : (y : A) * B) * C ~> (x : A) (y : B[y := x]) (C[x := (x, y)])
  Sigma x (Sigma y a b) c ->
    reduce1 $ Sigma x a $ Sigma y (subst y (Var x) b) $ subst x (Pair (Var x) (Var y)) c
  -- (x : (y : A) * B) -> C ~> (x : A) (y : B[y := x]) (C[x := (x, y)])
  Pi x (Sigma y a b) c ->
    reduce1 $ Pi x a $ Pi y (subst y (Var x) b) $ subst x (Pair (Var x) (Var y)) c
  -- Recurse on the witness/codomain part (but not the domain part).
  Pi x a b -> Pi x a $ reduce1 b
  Sigma x a b -> Sigma x a $ reduce1 b
  a -> a

-- Eliminate units.
reduce2 :: Term UName -> Term UName
reduce2 = \case
  -- (x : Unit) * A ~> A[x := tt]
  Sigma x Unit a -> reduce2 $ subst x TT a
  Sigma x a b -> case reduce2 b of
    -- (x : A) * Unit ~> A
    Unit -> reduce2 a
    b' -> Sigma x a b'
  -- (x : Unit) -> A ~> A[x := tt]
  Pi x Unit a -> reduce2 $ subst x TT a
  Pi x a b -> case reduce2 b of
    -- (x : A) -> Unit ~> Unit
    Unit -> Unit
    b' -> Pi x a b'
  a -> a

-- Distribute sigmas at the codomain part of pis.
reduce3 :: Term UName -> Term UName
reduce3 = \case
  Pi x a b -> case reduce3 b of
    -- (x : A) -> (y : B) * C ~> (y : (x : A) -> B) * (x : A) -> C[y := y x]
    Sigma y c d -> reduce3 $ Sigma y (Pi x a c) $ Pi x a $ subst y (App (Var y) (Var x)) d
    b' -> Pi x a b'
  -- Recurse on the witness part (but not the domain part).
  Sigma x a b -> Sigma x a $ reduce3 b
  a -> a

reduce :: Term UName -> Term UName
reduce = reduce3 . reduce2 . reduce1

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

isKeyword :: Text -> Bool
isKeyword x =
  x == "let"
    || x == "Type"
    || x == "fst"
    || x == "snd"
    || x == "Unit"
    || x == "tt"

pName :: Parser Name
pName = try $ lexeme do
  x <- takeWhile1P (Just "name") isAlphaNum
  guard $ not $ isKeyword x
  pure x

pAtom :: Parser (Term Name)
pAtom =
  (Type <$ symbol "Type")
    <|> (Unit <$ symbol "Unit")
    <|> (TT <$ symbol "tt")
    <|> (Var <$> pName)
    <|> parens pTerm

pSpine :: Parser (Term Name)
pSpine =
  choice
    [ do
        _ <- symbol "fst"
        a <- pAtom
        foldl App (Fst a) <$> many pAtom,
      do
        _ <- symbol "snd"
        a <- pAtom
        foldl App (Snd a) <$> many pAtom,
      foldl1 App <$> some pAtom
    ]

pBinder :: Parser [([Name], Type Name)]
pBinder = some $ parens $ (,) <$> some (pName <|> symbol "_") <*> (symbol ":" *> pTerm)

pAbs :: Parser (Term Name)
pAbs = do
  _ <- symbol "\\"
  ps <- pBinder
  _ <- symbol "."
  b <- pTerm
  pure $ foldr (\(xs, a) t -> foldr (\x -> Abs x a) t xs) b ps

pQuant :: Parser (Name -> Term Name -> Term Name -> Term Name)
pQuant = (Sigma <$ symbol "*") <|> (Pi <$ symbol "->")

pPiSigma :: Parser (Term Name)
pPiSigma = do
  ps <- pBinder
  q <- pQuant
  b <- pTerm
  pure $ foldr (\(xs, a) t -> foldr (\x -> q x a) t xs) b ps

pFunPairSpine :: Parser (Term Name)
pFunPairSpine = do
  sp <- pSpine
  choice
    [ do
        q <- pQuant
        q "_" sp <$> pTerm,
      do
        _ <- symbol ","
        Pair sp <$> pTerm,
      pure sp
    ]

pTerm :: Parser (Term Name)
pTerm = pAbs <|> try pPiSigma <|> pFunPairSpine

parseTerm :: Text -> Either (ParseErrorBundle Text Void) (Term Name)
parseTerm = parse (sc *> pTerm <* eof) ""

parseSigs :: FilePath -> Text -> Either (ParseErrorBundle Text Void) [(Name, Term Name)]
parseSigs path = flip parse path do
  sc *> many ((,) <$> (symbol "let" *> pName) <*> (symbol ":" *> pTerm)) <* eof

--------------------------------------------------------------------------------
-- Pretty printing

punctuate :: ShowS -> [ShowS] -> ShowS
punctuate sep xs = foldr (.) id (intersperse sep xs)

prettyTerm :: (n -> ShowS) -> Int -> Term n -> ShowS
prettyTerm var = \p -> \case
  Type -> showString "Type"
  Unit -> showString "()"
  TT -> showString "tt"
  Var x -> var x
  Pi x a b -> showParen (p > 1) $ prettyBind x a . showChar ' ' . goPi b
  Abs x a t -> showParen (p > 0) $ showChar '\\' . prettyBind x a . goAbs t
  App t u -> showParen (p > 2) $ prettyTerm var 2 t . showChar ' ' . prettyTerm var 3 u
  Sigma x a b -> showParen (p > 1) $ prettyBind x a . showChar ' ' . goSigma b
  Pair t u -> showParen (p > 1) $ prettyTerm var 2 t . showString " , " . prettyTerm var 1 u
  Fst t -> showParen (p > 2) $ showString "fst " . prettyTerm var 3 t
  Snd t -> showParen (p > 2) $ showString "snd " . prettyTerm var 3 t
  where
    prettyBind x a = showParen True $ var x . showString " : " . prettyTerm var 0 a

    goAbs = \case
      Abs x a t -> prettyBind x a . showChar ' ' . goAbs t
      t -> prettyTerm var 0 t

    goPi = \case
      Pi x a b -> prettyBind x a . showChar ' ' . goPi b
      a -> showString "-> " . prettyTerm var 1 a

    goSigma = \case
      Sigma x a b -> prettyBind x a . showChar ' ' . goSigma b
      a -> showString "* " . prettyTerm var 1 a

--------------------------------------------------------------------------------

orDie :: (Exception e) => Either e a -> IO a
orDie = either (die . displayException) pure

helpText :: String
helpText = "Enter a type to query, :q to quit, or :h for help.\nType syntax:\n  <var>  ::= [a-z][a-zA-Z0-9]\n  <type> ::= <var> | () | <type> * <type> | <type> -> <type> | [<type>] | forall <var>. <type>"

main :: IO ()
main = do
  [path] <- getArgs
  sigs <- orDie . parseSigs path =<< T.readFile path
  sigs' <- traverse (\(x, a) -> (x,a,) . reduce <$> freshen a) sigs
  for_ sigs' \(x, _, na) -> do
    putStrLn $ T.unpack x ++ " : " ++ prettyTerm shows 0 na ""
  runInputT defaultSettings do
    outputStrLn helpText
    fix \loop -> do
      minput <- getInputLine "> "
      case minput of
        Nothing -> loop
        Just ":q" -> pure ()
        Just ":h" -> outputStrLn helpText >> loop
        Just input -> case parseTerm (T.pack input) of
          Left e -> outputStrLn (displayException e) >> loop
          Right query -> do
            query' <- liftIO $ freshen query
            outputStrLn $ prettyTerm shows 0 query' ""
            outputStrLn $ prettyTerm shows 0 (reduce query') ""
            -- query' <- liftIO $ reduce M.empty (close query)
            -- forM_ sigs' \(x, a, na) -> do
            --   when (equivNF query' na) do
            --     outputStrLn $ T.unpack x ++ " : " ++ prettyTerm 0 a ""
            loop
