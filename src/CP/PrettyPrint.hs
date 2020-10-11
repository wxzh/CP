{-# LANGUAGE FlexibleInstances, ExistentialQuantification, OverloadedStrings, NoImplicitPrelude, RankNTypes #-}

module CP.PrettyPrint
  ( pprint
  , FPretty(..)
  , FDoc
  , D(..)
  ) where

import           Data.Text.Prettyprint.Doc (Doc, (<+>), Pretty)
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Unbound.Generics.LocallyNameless
import           Protolude
import           Text.Megaparsec

import           CP.Common
import qualified CP.Source.Syntax as S
import qualified Data.List

instance Pretty SourcePos where
  pretty (SourcePos _ line col) =
    Pretty.pretty (unPos line) <> Pretty.colon <> Pretty.pretty (unPos col) <>
    Pretty.colon


data FAnn = FAnn

type FDoc = Doc FAnn

class FPretty p where
  ppr :: (Applicative m, LFresh m) => p -> m FDoc


-- | Error message quoting
data D = DS FDoc -- ^ String literal
       | forall a . FPretty a => DD a -- ^ Displayable value

instance FPretty D where
  ppr (DS s) = return s
  ppr (DD d) = ppr d

instance FPretty [D] where
  ppr dl = Pretty.sep <$> mapM ppr dl


instance FPretty ArithOp where
  ppr Add = return $ "+"
  ppr Mul = return $ "*"
  ppr Sub = return $ "-"
  ppr Div = return $ "/"

instance FPretty CompOp where
  ppr Equ = return $ "=="
  ppr Neq = return $ "!="
  ppr Lt = return $ "<"
  ppr Gt = return $ ">"

instance FPretty LogicalOp where
  ppr LAnd = return $ "&&"
  ppr LOr = return $ "||"


instance FPretty Operation where
  ppr (Arith a) = ppr a
  ppr (Logical a) = ppr a
  ppr (Comp a) = ppr a
  ppr (Append _) = return $ "++"
  ppr At = return $ "!!"


instance FPretty S.Kind where
  ppr S.Star = return $ "star"
  ppr (S.KArrow k1 k2) = do
    k1' <- ppr k1
    k2' <- ppr k2
    return $ k1' <+> "->" <+> k2'

instance FPretty S.SType where
  ppr (S.Arr t1 t2) = do
    t1' <- ppr t1
    t2' <- ppr t2
    return $ Pretty.parens (t1' <+> "->" <+> t2')
  ppr S.NumT = return $ "Double"
  ppr S.BoolT = return $ "Bool"
  ppr S.StringT = return $ "String"
  ppr (S.And t1 t2) = do
    t1' <- ppr t1
    t2' <- ppr t2
    return $ Pretty.parens (t1' <+> "&" <+> t2')
  ppr (S.TVar x) = return (Pretty.pretty x)
  ppr (S.DForall b) =
    lunbind b $ \((x, Embed a), t) -> do
      a' <- ppr a
      t' <- ppr t
      return
        (Pretty.parens $
         "∀" <> Pretty.parens (Pretty.pretty x <> "*" <> a') <+>
         Pretty.dot <+> t')
  ppr (S.TraitT t1 t2) = do
    t1' <- ppr t1
    t2' <- ppr t2
    return $ "Trait" <> Pretty.brackets (t1' <> "," <> t2')
  ppr (S.SRecT l t) = do
    t' <- ppr t
    return (Pretty.braces $ Pretty.pretty l <+> Pretty.colon <+> t')
  ppr S.TopT = return $ "Top"
  ppr S.BotT = return $ "Bot"
  ppr (S.OpAbs b) =
    lunbind b $ \((x, Embed k), t) -> do
      t' <- ppr t
      k' <- ppr k
      return $
        Pretty.parens
          ("Lam" <> Pretty.parens (Pretty.pretty x <> ":" <> k') <+>
           Pretty.dot <+> t')
  ppr (S.OpApp a b) = do
    a' <- ppr a
    b' <- ppr b
    return $ Pretty.parens (a' <+> b')

  ppr (S.OpAppS t1 ts) = do
    t1' <- ppr t1
    ts' <- mapM ppr ts
    return $ t1' <+> Pretty.angles (Pretty.hcat $ Pretty.punctuate Pretty.comma ts')
  ppr (S.ListT t) = do
    t' <- ppr t
    return $ Pretty.parens ("List" <+> t')

-- deciding whether to add parens to the func of an application
wrapf :: S.Expr -> FDoc -> FDoc
wrapf f = case f of
  S.Var _         -> identity
  S.App _ _       -> identity

  S.Pos _ a       -> wrapf a
  _             -> Pretty.parens

-- deciding whether to add parens to the arg of an application
wraparg :: S.Expr -> FDoc -> FDoc
wraparg x = case x of
  S.Var _       -> identity
  S.LitV _ -> identity
  S.BoolV _ -> identity
  S.StrV _ -> identity
  S.Top -> identity
  _ -> Pretty.parens

instance FPretty S.Expr where
  ppr (S.New e) = do
    e' <- ppr e
    return $ "new " <> e'
  ppr (S.Anno e t) = do
    e' <- ppr e
    t' <- ppr t
    return $ enclose' "" "" " : " ": " (fmap duplicate ([e', t']))
  ppr (S.Var x) = return $ Pretty.pretty x
  ppr (S.App f a) = do
    df <- ppr f
    da <- ppr a
    return $ wrapf f df <+> wraparg a da
  ppr (S.TApp f a) = do
    f' <- ppr f
    a' <- ppr a
    return $ wrapf f f' <+> "@" <> a'
  ppr (S.Lam bnd) =
    lunbind bnd $ \(x, b) -> do
      b' <- ppr b
      let short = "λ(" <> Pretty.pretty x <> ")"
          d = [Pretty.group (Pretty.flatAlt short short), b']
      return $ arrows (fmap duplicate d)
  ppr (S.LamA bnd) =
    lunbind bnd $ \((x, Embed t), b) -> do
      b' <- ppr b
      t' <- ppr t
      let long =
            "λ " <>
            Pretty.align
              ("( " <> Pretty.pretty x <> Pretty.hardline <> ": " <> t' <>
               Pretty.hardline <>
               ")")
          short = "λ(" <> Pretty.pretty x <> " : " <> t' <> ")"
          d = [Pretty.group (Pretty.flatAlt long short), b']
      return $ arrows (fmap duplicate d)
    where

  ppr (S.DLam bnd) =
    lunbind bnd $ \((x, Embed t), b) -> do
      b' <- ppr b
      t' <- ppr t
      let long =
            "Λ " <>
            Pretty.align
              ("( " <> Pretty.pretty x <> Pretty.hardline <> "* " <> t' <>
               Pretty.hardline <>
               ")")
          short = "Λ(" <> Pretty.pretty x <> " * " <> t' <> ")"
          d = [Pretty.group (Pretty.flatAlt long short), b']
      return $ enclose' "" "" " . " ". " (fmap duplicate d)
  ppr (S.LitV n) = return (Pretty.pretty n)
  ppr (S.BoolV b) = return (Pretty.pretty b)
  ppr (S.StrV b) = return (Pretty.dquotes (Pretty.pretty b))
  ppr (S.PrimOp op e1 e2) = do
    e1' <- ppr e1
    op' <- ppr op
    e2' <- ppr e2
    return $
      enclose'
        ""
        ""
        (" " <> op' <> " ")
        (op' <> " ")
        (fmap duplicate [e1', e2'])
  ppr (S.Merge e1 e2) = do
    e1' <- ppr e1
    e2' <- ppr e2
    return $ enclose' "" "" " ,, " ",, " (fmap duplicate [e1', e2'])
  ppr (S.If p e1 e2) = do
    p' <- (ppr p)
    e1' <- (ppr e1)
    e2' <- (ppr e2)
    let long =
          Pretty.align ("if    " <> p' <> Pretty.hardline <> "then  " <> e1')
        short = "if " <> p' <> " then " <> e1'
        d = [Pretty.group (Pretty.flatAlt long short), e2']
    return $ enclose' "" "" " else " ("else  ") (fmap duplicate d)
  ppr (S.DRec l e _) = do
    e' <- ppr e
    return $ braces [Pretty.pretty l <+> "=" <+> e']
  ppr (S.Acc e l) = do
    e' <- ppr e
    return $ e' <> Pretty.dot <> Pretty.pretty l
  ppr (S.Remove e l t) = do
    e' <- ppr e
    t' <- maybe (return Pretty.emptyDoc) ppr t
    return $
      e' <+> Pretty.pretty '\\' <+> Pretty.braces (Pretty.pretty l <+> t')
  ppr S.Top = return $ "()"
  ppr (S.Letrec b) =
    lunbind b $ \((x, Embed t), (e, body)) -> do
      b' <- ppr body
      e' <- ppr e
      (long, short) <-
        maybe
          (let long =
                 "let " <>
                 Pretty.align
                   (Pretty.pretty x <> " =" <> Pretty.hardline <> "  " <> e')
               short = "let " <> Pretty.pretty x <> " = " <> e'
           in return (long, short))
          (\tt -> do
             t' <- ppr tt
             let long =
                   "letrec " <>
                   Pretty.align
                     (Pretty.pretty x <> Pretty.hardline <> ": " <> t' <>
                      Pretty.hardline <>
                      "= " <>
                      e')
                 short =
                   "letrec " <> Pretty.pretty x <> " : " <> t' <> " = " <> e'
             return (long, short))
          t
      let d = [Pretty.group (Pretty.flatAlt long short), b']
      return $ enclose' "" "" " in " ("in  ") (fmap duplicate d)
  ppr S.Bot = return $ "undefined"
  ppr (S.AnonyTrait (S.Trait (self,t1) e2 t2 e1)) = do
    t1' <- ppr t1
    e1' <- ppr e1
    t2' <- maybe (return Pretty.emptyDoc)
           (\t -> do
               t' <- ppr t
               return $ "implements" <+> t') t2
    e2' <- maybe (return Pretty.emptyDoc)
           (\e -> do
               e' <- ppr e
               return $ "inherits" <+> e') e2
    return $ "trait" <+> Pretty.brackets (Pretty.pretty self <> " : " <> t1') <+> t2' <+> e2' <> Pretty.hardline <+> e1'
  ppr (S.DRec' _) = return $ "fancy records"
  ppr (S.Open e1 e2) = do
    e1' <- ppr e1
    e2' <- ppr e2
    return $ "open " <> e1' <> " in " <> e2'
  ppr (S.Forward e1 e2) = do
    e1' <- ppr e1
    e2' <- ppr e2
    return $ e1' <> " ^ " <> e2'
  ppr (S.Pos _ e) = ppr e
  ppr (S.ListNew _ n f) = do
    n' <- ppr n
    f' <- ppr f
    return $ "[ " <> f' <> " | 1.." <> n' <> " ]"
  ppr (S.ListLength l) = do
    l' <- ppr l
    return $ "length" <+> l'
  ppr (S.ListSum l) = do
    l' <- ppr l
    return $ "sum" <+> l'
  ppr (S.ListScanl l) = do
    l' <- ppr l
    return $ "scanl" <+> l'
  ppr (S.ListLzw _ f l1 l2) = do
    f' <- ppr f
    l1' <- ppr l1
    l2' <- ppr l2
    return $ "lzw" <+> f' <+> l1' <+> l2'


pprint :: FPretty a => a -> FDoc
pprint = runLFreshM . ppr



-- | Pretty-print record types and literals
braces :: [Doc ann] -> Doc ann
braces   [] = "{}"
braces docs = enclose "{ " "{ " ", " ", " " }" "}" (fmap duplicate docs)


-- | Pretty-print anonymous functions and function types
arrows :: [(Doc ann, Doc ann)] -> Doc ann
arrows = enclose' "" "" " → " "→ "

{-| Format an expression that holds a variable number of elements, such as a
    list, record, or union
-}
enclose
    :: Doc ann
    -- ^ Beginning document for compact representation
    -> Doc ann
    -- ^ Beginning document for multi-line representation
    -> Doc ann
    -- ^ Separator for compact representation
    -> Doc ann
    -- ^ Separator for multi-line representation
    -> Doc ann
    -- ^ Ending document for compact representation
    -> Doc ann
    -- ^ Ending document for multi-line representation
    -> [(Doc ann, Doc ann)]
    -- ^ Elements to format, each of which is a pair: @(compact, multi-line)@
    -> Doc ann
enclose beginShort _         _        _       endShort _       []   =
    beginShort <> endShort
  where
enclose beginShort beginLong sepShort sepLong endShort endLong docs =
    Pretty.group
        (Pretty.flatAlt
            (Pretty.align
                (mconcat (zipWith combineLong (beginLong : repeat sepLong) docsLong) <> endLong)
            )
            (mconcat (zipWith combineShort (beginShort : repeat sepShort) docsShort) <> endShort)
        )
  where
    docsShort = fmap fst docs

    docsLong = fmap snd docs

    combineLong x y = x <> y <> Pretty.hardline

    combineShort x y = x <> y



{-| Format an expression that holds a variable number of elements without a
    trailing document such as nested `let`, nested lambdas, or nested `forall`s
-}
enclose'
    :: Doc ann
    -- ^ Beginning document for compact representation
    -> Doc ann
    -- ^ Beginning document for multi-line representation
    -> Doc ann
    -- ^ Separator for compact representation
    -> Doc ann
    -- ^ Separator for multi-line representation
    -> [(Doc ann, Doc ann)]
    -- ^ Elements to format, each of which is a pair: @(compact, multi-line)@
    -> Doc ann
enclose' beginShort beginLong sepShort sepLong docs =
  Pretty.group (Pretty.flatAlt long short)
  where
    longLines = zipWith (<>) (beginLong : repeat sepLong) docsLong
    long =
      Pretty.align (mconcat (Data.List.intersperse Pretty.hardline longLines))
    short = mconcat (zipWith (<>) (beginShort : repeat sepShort) docsShort)
    docsShort = fmap fst docs
    docsLong = fmap snd docs


{-| Internal utility for pretty-printing, used when generating element lists
    to supply to `enclose` or `enclose'`.  This utility indicates that the
    compact represent is the same as the multi-line representation for each
    element
-}
duplicate :: a -> (a, a)
duplicate x = (x, x)
