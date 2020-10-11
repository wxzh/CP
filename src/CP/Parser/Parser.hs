module CP.Parser.Parser (parseModule) where

import           Control.Arrow (first, second)
import           Control.Monad (liftM3)
import           Data.Functor (($>))
import           Data.List (foldl', foldl1')
import           Data.Maybe (fromMaybe, maybeToList, isJust)
import           Data.Scientific (toRealFloat)
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import           Text.Megaparsec.Expr
import           Unbound.Generics.LocallyNameless

import           CP.Common
import           CP.Source.Syntax
import           CP.Util

type Parser = Parsec Void String

parseModule :: String -> Either String Module
parseModule s =
  case runParser (whole prog) "" s of
    Left err -> Left $ parseErrorPretty err
    Right e -> Right e


-- | Top-level parsers (should consume all input)
whole :: Parser a -> Parser a
whole p = sc *> p <* eof

------------------------------------------------------------------------
-- Programs
------------------------------------------------------------------------

prog :: Parser Module
prog = do
  decls <- endBy (try decl) semi
  e <- expr
  return $ Module decls e


decl :: Parser SDecl
decl = DefDecl <$> pTmBind <|> TypeDecl <$> tyBind

traitDecl :: Parser TmBind
traitDecl = do
  (tr, n) <- pTrait
  case n of
    Just n' -> return $ TmBind n' [] [] tr Nothing False
    Nothing -> fail "Need trait name"

pTmBind :: Parser TmBind
pTmBind = try tmBind <|> pPattern

tmBind :: Parser TmBind
tmBind = do
  flag <- optional $ rword "override"
  n <- luidentifier
  ts <- many (try ctyparam)
  xs <- many param
  ret <- optional (colon *> pType)
  symbol "="
  e <- expr
  return $ TmBind n (map (first s2n) ts) (map (first s2n) xs) e ret (isJust flag)

-- pPattern :: Parser TmBind
-- pPattern = do
--   (l1, xs) <- parens $ liftM2 (,) luidentifier (many tparam)
--   symbol "."
--   l2 <- lidentifier
--   symbol "="
--   e <- expr
--   return $ Patterns [Pattern l1 (map (first s2n) xs) l2 e]

-- patternBind :: Parser TmBind
-- patternBind = do
--   n <- lidentifier
--   ts <- many (try ctyparam)
--   xs <- many param
--   symbol "="
--   e <- expr
--   return $ TmBind n (map (first s2n) ts) (map (first s2n) xs) e Nothing False

pPattern :: Parser TmBind
pPattern = do
  flag <- optional $ rword "override"
  (l, xs, self) <- parens $ liftM3 (,,) luidentifier (many param) (optional (brackets pSelf))
  symbol "."
  b <- tmBind
  return $ Pattern l (map (first s2n) xs) self b (isJust flag)

tyBind :: Parser TypeBind
tyBind = do
  rword "type"
  n <- uidentifier
  ss <- optional $ sortList
  ts <- many (uidentifier >>= \x -> return (s2n x, Star))
  extend <- optional (rword "extends" >> pType)
  symbol "="
  t <- pType
  return $ TypeBind n (fromMaybe [] ss) ts extend t

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

expr :: Parser Expr
expr = do
  p <- getPosition
  Pos p <$> makeExprParser term pOperators

term :: Parser Expr
term = postfixChain factor (try bapp <|> fapp)

fapp :: Parser (Expr -> Expr)
fapp = do
  e <- factor
  return (`App` e)

bapp :: Parser (Expr -> Expr)
bapp = do
  symbol "@"
  e <- atype
  return (`TApp` e)


factor :: Parser Expr
factor = postfixChain atom (rmOperator <|> dotOperator <|> colonOperator)

dotOperator :: Parser (Expr -> Expr)
dotOperator = do
  symbol "."
  k <- luidentifier
  return (`Acc` k)

colonOperator :: Parser (Expr -> Expr)
colonOperator = do
  colon
  t <- pType
  return (`Anno` t)


rmOperator :: Parser (Expr -> Expr)
rmOperator = do
  symbol "\\"
  (l, t) <-
    braces
      (do l <- lidentifier
          colon
          t <- pType
          return (l, t))
  return (\e -> Remove e l (Just t))

atom :: Parser Expr
atom =
  choice
    [ pLambda
    , pBLambda
    , pLetrec
    , pLet
    , pIf
    , fst <$> pTrait
    , pNew
    , LitV <$> float
    , StrV <$> stringLiteral
    , topVal
    , listFunctions
    , evar <$> luidentifier
    , record
    , bconst
    , pOpen
    , parens expr
    ]

record :: Parser Expr
record = braces (mkRecds' <$> sepEndBy1 pTmBind (comma <|> semi))

bconst :: Parser Expr
bconst =
  choice
    [ rword "true" $> BoolV True
    , rword "false" $> BoolV False
    , rword "undefined" $> Bot
    ]

pLambda :: Parser Expr
pLambda = do
  symbol "\\"
  xs <- some param
  symbol "->"
  e <- expr
  return $ foldr elam e xs


pBLambda :: Parser Expr
pBLambda = do
  symbol "/\\"
  xs <- some ctyparam
  symbol "."
  e <- expr
  return $ foldr dlam e xs


pTrait :: Parser (Expr, Maybe String)
pTrait = do
  rword "trait"
  s <- optional (brackets pSelf) -- self reference
  t <- optional (symbol "implements" *> pType)
  i <- optional inherits -- optional inheritance
  symbol "=>"
  body <- expr -- trait body
  let self = fromMaybe ("*self", TopT) s
  let trait = AnonyTrait (Trait self i t body)
  return (trait, Nothing)


pSelf :: Parser (String, SType)
pSelf = do
  n <- lidentifier
  ret <- colon *> pType
  return (n, ret)


pNew :: Parser Expr
pNew = do
  rword "new"
  e <- expr
  return $ New e


inherits :: Parser Expr
inherits = do
  rword "inherits"
  expr

pLetrec :: Parser Expr
pLetrec = do
  rword "letrec"
  n <- lidentifier
  colon
  t <- pType
  symbol "="
  e1 <- expr
  rword "in"
  e2 <- expr
  return $ eletr n t e1 e2

pLet :: Parser Expr
pLet = do
  rword "let"
  n <- lidentifier
  symbol "="
  e1 <- expr
  rword "in"
  e2 <- expr
  return $ elet n e1 e2

pIf :: Parser Expr
pIf = do
  rword "if"
  a <- expr
  rword "then"
  b <- expr
  rword "else"
  c <- expr
  return $ If a b c

pOpen :: Parser Expr
pOpen = do
  rword "open"
  e1 <- expr
  rword "in"
  e2 <- expr
  return $ Open e1 e2

pOperators :: [[Operator Parser Expr]]
pOperators =
  [ [InfixN (PrimOp At <$ symbol "!!")]
  , [ InfixL (PrimOp (Arith Mul) <$ symbol "*")
    , InfixL (PrimOp (Arith Div) <$ symbol "/")
    ]
  , [ InfixL (PrimOp (Append Unknown) <$ symbol "++")
    , InfixL (PrimOp (Arith Add) <$ symbol "+")
    , InfixL (PrimOp (Arith Sub) <$ symbol "-")
    ]
  , [ InfixN (PrimOp (Comp Lt) <$ symbol "<")
    , InfixN (PrimOp (Comp Gt) <$ symbol ">")
    ]
  , [ InfixN (PrimOp (Comp Equ) <$ symbol "==")
    , InfixN (PrimOp (Comp Neq) <$ symbol "!=")
    ]
  , [InfixL (PrimOp (Logical LAnd) <$ symbol "&&")]
  , [InfixL (PrimOp (Logical LOr) <$ symbol "||")]
  , [InfixL (Merge <$ symbol ",,")]
  , [InfixN (Forward <$ symbol "^")]
  ]

listFunctions :: Parser Expr
listFunctions = choice [ listNew, listLength, listSum, listScanl, listLzw ]

listNew :: Parser Expr
listNew = do
  rword "list"
  symbol "@"
  t <- atype
  n <- factor
  f <- factor
  return $ ListNew t n f

listLength :: Parser Expr
listLength = do
  rword "length"
  l <- factor
  return $ ListLength l

listSum :: Parser Expr
listSum = do
  rword "sum"
  l <- factor
  return $ ListSum l

listScanl :: Parser Expr
listScanl = do
  rword "scanl"
  l <- factor
  return $ ListScanl l

listLzw :: Parser Expr
listLzw = do
  rword "lzw"
  symbol "@"
  t <- atype
  f <- factor
  l1 <- factor
  l2 <- factor
  return $ ListLzw t f l1 l2


------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

pType :: Parser SType
pType = makeExprParser pOpApp tOperators

pOpApp :: Parser SType
pOpApp = postfixChain atype (tOpApp <|> tOpAppS)

tOpApp :: Parser (SType -> SType)
tOpApp = do
  t <- atype
  return (`OpApp` t)

tOpAppS :: Parser (SType -> SType)
tOpAppS = do
  ts <- angles (sepBy1 sort comma)
  return $ \ty -> (foldl OpAppS ty ts)

sort :: Parser [SType]
sort = do
  t1 <- pType
  t2 <- optional (symbol "%" >> pType)
  return $ t1 : maybeToList t2


tOperators :: [[Operator Parser SType]]
tOperators =
  [ [InfixL (And <$ symbol "&")]
  , [InfixR (Arr <$ symbol "->")]
  ]

atype :: Parser SType
atype =
  choice
    [pForall, traitType, tvar <$> uidentifier, recordType, tconst, listType, parens pType]

pForall :: Parser SType
pForall = do
  rword "forall"
  xs <- some ctyparam
  symbol "."
  t <- pType
  return $ foldr tforall t xs

traitType :: Parser SType
traitType = do
  rword "Trait"
  ts <- tyList
  if length ts == 1
    then return $ TraitT TopT (head ts)
    else return $ foldl1' TraitT ts

recordType :: Parser SType
recordType = braces (mkRecdsT <$> sepEndBy1 field (comma <|> semi))

tconst :: Parser SType
tconst =
  choice
    [ rword "Double" $> NumT
    , rword "Int" $> NumT
    , rword "String" $> StringT
    , rword "Bool" $> BoolT
    , rword "Top" $> TopT
    , rword "Bot" $> BotT
    ]

listType :: Parser SType
listType = do
  rword "List"
  t <- pType
  return $ ListT t


------------------------------------------------------------------------
-- Parameters
------------------------------------------------------------------------


-- [A,B,C]
tyList :: Parser [SType]
tyList = brackets $ sepBy1 pType comma

-- [X, Y, Z]
typaramList :: Parser [(TyName, Kind)]
typaramList =
  brackets $ sepBy1 (uidentifier >>= \n -> return (s2n n, Star)) comma

-- <A,B,C>
sortList :: Parser [Label]
sortList = 
  angles $ sepBy1 uidentifier comma

-- (a, b, c)
pArgs :: Parser [Expr]
pArgs = parens $ sepBy1 expr comma

-- x : A
tparam :: Parser (Label, SType)
tparam = do
  l <- lidentifier <|> symbol "_"
  colon
  e <- pType
  return (l, e)

-- X : A
field :: Parser (Label, SType)
field = do
  l <- luidentifier
  colon
  e <- pType
  return (l, e)


-- (x : A) or x
param :: Parser (String, Maybe SType)
param =
  choice
    [ (lidentifier <|> symbol "_") >>= \n -> return (n, Nothing)
    , parens $ second Just <$> tparam
    ]


-- x * A
constrainTy :: Parser (String, SType)
constrainTy = do
  n <- uidentifier
  symbol "*"
  t <- pType
  return (n, t)

-- (x * A) or X
ctyparam :: Parser (String, SType)
ctyparam =
  choice
    [ do n <- uidentifier
         return (n, TopT)
    , parens constrainTy
    ]

------------------------------------------------------------------------
-- Misc
------------------------------------------------------------------------

sc :: Parser ()
sc = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt  = L.skipLineComment "--"
    blockCmnt = L.skipBlockComment "{-" "-}"


lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

angles :: Parser a -> Parser a
angles = between (symbol "<") (symbol ">")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

float :: Parser Double
float = lexeme (toRealFloat <$> L.scientific)

topVal :: Parser Expr
topVal = symbol "()" >> return Top

stringLiteral :: Parser String
stringLiteral = lexeme $ char '"' >> manyTill L.charLiteral (char '"')

semi :: Parser String
semi = symbol ";"

colon :: Parser String
colon = symbol ":"

comma :: Parser String
comma = symbol ","

rword :: String -> Parser ()
rword w = string w *> notFollowedBy alphaNumChar *> sc

postfixChain :: Parser a -> Parser (a -> a) -> Parser a
postfixChain p op = do
  x <- p
  rest x
  where
    rest x =
      (do f <- op
          rest $ f x) <|>
      return x

rws :: [String] -- list of reserved words
rws =
  [ "if"
  , "then"
  , "else"
  , "let"
  , "letrec"
  , "in"
  , "type"
  , "forall"
  , "trait"
  , "new"
  , "Trait"
  , "extends"
  , "inherits"
  , "implements"
  , "undefined"
  , "Double"
  , "Int"
  , "String"
  , "Bool"
  , "true"
  , "false"
  , "Top"
  , "Bot"
  , "override"
  , "open"
  , "List"
  , "list"
  , "length"
  , "sum"
  , "scanl"
  , "lzw"
  ]


identifier :: Parser Char -> Parser String
identifier s = (lexeme . try) (p >>= check)
  where
    p = (:) <$> s <*> many identChar
    check x =
      if x `elem` rws
        then fail $ "keyword " ++ show x ++ " cannot be an identifier"
        else return x

identChar :: Parser Char
identChar = alphaNumChar <|> oneOf "_#'"

lidentifier :: Parser String
lidentifier = identifier lowerChar

uidentifier :: Parser String
uidentifier = identifier upperChar

luidentifier :: Parser String
luidentifier = identifier letterChar

sigName :: Parser String
sigName = identifier (char '#')
