module Main where

import Control.Exception (Exception (..))
import Control.Monad
import Control.Monad.IO.Class
import Data.Char
import Data.Function
import Data.List (elemIndex, intersperse, permutations)
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe)
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
  | Proj1 (Term n) -- π1
  | Proj2 (Term n) -- π2
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
      Proj1 a -> Proj1 <$> go ren a
      Proj2 a -> Proj2 <$> go ren a
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
  Proj1 a -> freeVarSet a
  Proj2 a -> freeVarSet a
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
      Proj1 a -> Proj1 (go a)
      Proj2 a -> Proj2 (go a)
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

betaReduce :: Term UName -> Term UName
betaReduce = \case
  Type -> Type
  Unit -> Unit
  TT -> TT
  v@Var {} -> v
  Pi x a b -> Pi x (betaReduce a) (betaReduce b)
  Abs x a t -> Abs x (betaReduce a) (betaReduce t)
  App t u -> case (betaReduce t, betaReduce u) of
    -- (\(x : a). t) u -> t[x<-u]
    (Abs x _ v, u') -> betaReduce $ subst x u' v
    (t', u') -> App t' u'
  Sigma x a b -> Sigma x (betaReduce a) (betaReduce b)
  Pair t u -> Pair (betaReduce t) (betaReduce u)
  Proj1 t -> case betaReduce t of
    -- π1(t, u) = t
    Pair u _ -> u
    t' -> Proj1 t'
  Proj2 t -> case betaReduce t of
    -- π2(t, u) = u
    Pair _ u -> u
    t' -> Proj2 t'

-- Eliminate nested sigmas in the domain part of sigmas/pis.
reduce1 :: Term UName -> Term UName
reduce1 t = case betaReduce t of
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
reduce2 t = case betaReduce t of
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
reduce3 t = case betaReduce t of
  Pi x a b -> case reduce3 b of
    -- (x : A) -> (y : B) * C ~> (y : (x : A) -> B) * (x : A) -> C[y := y x]
    Sigma y c d -> reduce3 $ Sigma y (Pi x a c) $ Pi x a $ subst y (App (Var y) (Var x)) d
    b' -> Pi x a b'
  -- Recurse on the witness part (but not the domain part).
  Sigma x a b -> Sigma x a $ reduce3 b
  a -> a

reduce :: Term UName -> Term UName
reduce = reduce3 . reduce2 . reduce1

-- Normal-forms

-- (x1 : A1) ... (xn : An) -> (y1 : B1) * ... * (ym : Bm) * C
-- C is the last element of the second list
data Factor n = Factor [(n, Term n)] [(n, Term n)]
  deriving stock (Show)

-- (x1 : A1) * ... * (xn : An) * B
-- B is the last element of the list
type NF n = [(n, Factor n)]

toFactor :: Term UName -> IO (Factor UName)
toFactor = \case
  Pi x a b -> do
    toFactor b >>= \case
      Factor fs fs' -> pure $ Factor ((x, a) : fs) fs'
  Sigma x a b -> do
    toFactor b >>= \case
      Factor [] fs -> pure $ Factor [] ((x, a) : fs)
      _ -> error "toFactor: not a normal form"
  t -> do
    u <- newUnique
    let x = Local u "_"
    pure $ Factor [] [(x, t)]

toNF :: Term UName -> IO (NF UName)
toNF = \case
  Sigma x a b -> do
    a' <- toFactor a
    ((x, a') :) <$> toNF b
  t -> do
    u <- newUnique
    let x = Local u "_"
    t' <- toFactor t
    pure [(x, t')]

alphaEq :: [UName] -> [UName] -> Term UName -> Term UName -> Bool
alphaEq ms ns = \cases
  Type Type -> True
  Unit Unit -> True
  TT TT -> True
  (Var x) (Var y) -> case (elemIndex x ms, elemIndex y ns) of
    (Just i, Just j) -> i == j
    (Nothing, Nothing) -> x == y
    _ -> False
  (Pi x a b) (Pi y c d) ->
    alphaEq ms ns a c && alphaEq (x : ms) (y : ns) b d
  (Abs x a b) (Abs y c d) ->
    alphaEq ms ns a c && alphaEq (x : ms) (y : ns) b d
  (App a b) (App c d) ->
    alphaEq ms ns a c && alphaEq ms ns b d
  (Sigma x a b) (Sigma y c d) ->
    alphaEq ms ns a c && alphaEq (x : ms) (y : ns) b d
  (Pair a b) (Pair c d) ->
    alphaEq ms ns a c && alphaEq ms ns b d
  (Proj1 a) (Proj1 b) -> alphaEq ms ns a b
  (Proj2 a) (Proj2 b) -> alphaEq ms ns a b
  _ _ -> False

equivFactor' :: [UName] -> [UName] -> Factor UName -> Factor UName -> Bool
equivFactor' ms ns = \cases
  (Factor [] []) (Factor [] []) -> True
  (Factor [] ((x, a) : fs)) (Factor [] ((y, b) : gs)) ->
    alphaEq ms ns a b
      && equivFactor' (x : ms) (y : ns) (Factor [] fs) (Factor [] gs)
  (Factor ((x, a) : fs) fs') (Factor ((y, b) : gs) gs') ->
    alphaEq ms ns a b
      && equivFactor' (x : ms) (y : ns) (Factor fs fs') (Factor gs gs')
  _ _ -> False

equivFactor :: [UName] -> [UName] -> Factor UName -> Factor UName -> Bool
equivFactor ms ns a (Factor fs gs) = any (equivFactor' ms ns a) do
  fs' <- permutations fs
  gs' <- permutations gs
  pure $ Factor fs' gs'

equivNF' :: [UName] -> [UName] -> NF UName -> NF UName -> Bool
equivNF' ms ns = \cases
  [] [] -> True
  ((x, a) : fs) ((y, b) : gs) ->
    equivFactor ms ns a b
      && equivNF' (x : ms) (y : ns) fs gs
  _ _ -> False

equivNF :: NF UName -> NF UName -> Bool
equivNF a b = any (equivNF' [] [] a) (permutations b)

normalize :: Term Name -> IO (NF UName)
normalize = toNF . reduce <=< freshen

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

isKeyword :: Text -> Bool
isKeyword x =
  x == "let"
    || x == "Type"
    || x == "Unit"
    || x == "tt"

pName :: Parser Name
pName = try $ lexeme do
  c <- letterChar
  cs <- takeWhileP (Just "name") isAlphaNum
  let cs' = T.cons c cs
  guard $ not $ isKeyword cs'
  pure cs'

pBind :: Parser Name
pBind = pName <|> symbol "_"

pAtom :: Parser (Term Name)
pAtom =
  (Type <$ symbol "Type")
    <|> (Unit <$ symbol "Unit")
    <|> (TT <$ symbol "tt")
    <|> (Var <$> pName)
    <|> parens pTerm

pProj :: Parser (Term Name)
pProj = pAtom >>= go
  where
    go t =
      ( do
          _ <- char '.'
          (char '1' *> go (Proj1 t)) <|> (char '2' *> go (Proj2 t))
      )
        <|> (t <$ sc)

pApp :: Parser (Term Name)
pApp = foldl1 App <$> some pProj

pSigma :: Parser (Term Name)
pSigma = do
  optional (try $ symbol "(" *> pBind <* symbol ":") >>= \case
    Nothing -> do
      t <- pApp
      (symbol "*" *> (Sigma "_" t <$> pSigma)) <|> pure t
    Just x -> do
      a <- pTerm
      _ <- symbol ")"
      _ <- symbol "*"
      b <- pSigma
      pure $ Sigma x a b

pAbs :: Parser (Term Name)
pAbs = do
  _ <- symbol "\\"
  xs <- some $ parens $ (,) <$> pBind <*> (symbol ":" *> pTerm)
  _ <- symbol "."
  t <- pAbsPi
  pure $ foldr (\(x, a) u -> Abs x a u) t xs

pPi :: Parser (Term Name)
pPi = do
  optional (try $ some $ parens $ (,) <$> some pBind <*> (symbol ":" *> pTerm)) >>= \case
    Nothing -> do
      t <- pSigma
      (symbol "->" *> (Pi "_" t <$> pPi)) <|> pure t
    Just [([x], a)] -> do
      (symbol "->" *> (Pi x a <$> pPi))
        <|> ( do
                dom <- symbol "*" *> (Sigma x a <$> pSigma)
                (symbol "->" *> (Pi "_" dom <$> pPi)) <|> pure dom
            )
    Just dom -> do
      _ <- symbol "->"
      b <- pPi
      pure $ foldr (\(xs, a) t -> foldr (\x -> Pi x a) t xs) b dom

pAbsPi :: Parser (Term Name)
pAbsPi = pAbs <|> pPi

pTerm :: Parser (Term Name)
pTerm = do
  t <- pAbsPi
  (symbol "," *> (Pair t <$> pTerm)) <|> pure t

parseTerm :: Text -> Either (ParseErrorBundle Text Void) (Term Name)
parseTerm = parse (sc *> pTerm <* eof) ""

parseSigs :: FilePath -> Text -> Either (ParseErrorBundle Text Void) [(Name, Term Name)]
parseSigs path = flip parse path do
  sc *> many ((,) <$> (symbol "let" *> pName) <*> (symbol ":" *> pTerm)) <* eof

--------------------------------------------------------------------------------
-- Pretty printing

punctuate :: ShowS -> [ShowS] -> ShowS
punctuate sep xs = foldr (.) id (intersperse sep xs)

-- Operator precedence
projP, appP, sigmaP, piP, absP, pairP :: Int
projP = 5
appP = 4
sigmaP = 3
piP = 2
absP = 1
pairP = 0

par :: Int -> Int -> ShowS -> ShowS
par p q = showParen (p > q)

prettyTerm :: Int -> Term Name -> ShowS
prettyTerm = go
  where
    go p = \case
      Type -> showString "Type"
      Unit -> showString "Unit"
      TT -> showString "tt"
      Var x -> showString (T.unpack x)
      Pi "_" a b -> par p piP $ go sigmaP a . showString " -> " . go piP b
      Pi x a b -> par p piP $ bind x a . showChar ' ' . goPi b
      Abs x a t -> par p absP $ showChar '\\' . bind x a . showChar ' ' . goAbs t
      App t u -> par p appP $ go appP t . showChar ' ' . go projP u
      Sigma "_" a b -> par p sigmaP $ go appP a . showString " * " . go sigmaP b
      Sigma x a b -> par p sigmaP $ bind x a . showString " * " . go sigmaP b
      Proj1 t -> par p projP $ go projP t . showString ".1"
      Proj2 t -> par p projP $ go projP t . showString ".2"
      Pair t u -> par p pairP $ go absP t . showString ", " . go pairP u

    bind x a = showParen True $ showString (T.unpack x) . showString " : " . go pairP a

    goAbs = \case
      Abs x a t -> bind x a . showChar ' ' . goAbs t
      t -> showString ". " . go absP t

    goPi = \case
      Pi x a t | x /= "_" -> bind x a . showChar ' ' . goPi t
      t -> showString "-> " . go piP t

--------------------------------------------------------------------------------

orDie :: (Exception e) => Either e a -> IO a
orDie = either (die . displayException) pure

helpText :: String
helpText = "Enter a type to query, :q to quit, or :h for help.\nType syntax:\n  <var>  ::= [a-z][a-zA-Z0-9]\n  <type> ::= <var> | () | <type> * <type> | <type> -> <type> | [<type>] | forall <var>. <type>"

main :: IO ()
main = do
  [path] <- getArgs
  sigs <- orDie . parseSigs path =<< T.readFile path
  sigs' <- for sigs \(x, a) -> (x,a,) <$> normalize a
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
            query' <- liftIO $ normalize query
            forM_ sigs' \(x, a, na) -> do
              when (equivNF query' na) do
                outputStrLn $ T.unpack x ++ " : " ++ prettyTerm 0 a ""
            loop
