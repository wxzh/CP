module CP.Util where

import CP.Source.Syntax

import Data.List (foldl', foldl1')
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name

-- | Change the sort of a name.
translate :: Name a -> Name b
translate (Fn x y) = Fn x y
translate (Bn x y) = Bn x y

-- Utility for parsing

evar :: String -> Expr
evar = Var . s2n

tvar :: String -> SType
tvar = TVar . s2n

elam :: (String, Maybe SType) -> Expr -> Expr
elam (x, Nothing) e = elam1 x e
elam (x, Just t) e = elam2 (x, t) e

elam1 :: String -> Expr -> Expr
elam1 b e = Lam (bind (s2n b) e)

elam2 :: (String, SType) -> Expr -> Expr
elam2 (x, t) e = LamA (bind (s2n x, embed t) e)

dlam :: (String, SType) -> Expr -> Expr
dlam (s, t) b = DLam (bind (s2n s, embed t) b)

tforall :: (String,  SType) -> SType -> SType
tforall (s, t) b = DForall (bind (s2n s, embed t) b)

eapp :: Expr -> Expr -> Expr
eapp = App

etapp :: Expr -> SType -> Expr
etapp = TApp

mkRecds :: [(Label, Expr)] -> Expr
mkRecds [] = Top
mkRecds ((l, e):r) = foldl' (\t (l', e') -> Merge t (DRec l' e' False)) (DRec l e False) r

mkRecds' :: [TmBind] -> Expr
mkRecds' = foldl1' Merge . map DRec'

mkRecdsT :: [(Label, SType)] -> SType
mkRecdsT [] = TopT
mkRecdsT ((l, e):r) = foldl (\t (l', e') -> And t (SRecT l' e')) (SRecT l e) r

mkArr :: SType -> [SType] ->SType
mkArr = foldr Arr

mkForall :: SType -> [(TyName, Embed SType)] -> SType
mkForall = foldr (\b t -> DForall (bind b t))

eletr :: String -> SType -> Expr -> Expr -> Expr
eletr s t e b = Letrec (bind (s2n s, embed (Just t)) (e, b))


elet :: String -> Expr -> Expr -> Expr
elet s e b = Letrec (bind (s2n s, embed Nothing) (e, b))

transNew :: SType -> [Expr] -> Expr
transNew ty es =
  eletr
    "self"
    ty
    (foldl1'
       Merge
       (map
          (\tm ->
             case tm of
               Pos p (Remove e l t') -> Pos p (Remove (App e (evar "self")) l t')
               -- hack for trait excluding
               _ -> App tm (evar "self"))
          es))
    (evar "self")
