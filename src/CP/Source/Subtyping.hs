{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}

module CP.Source.Subtyping
  ( subtype
  ) where


import           Data.Sequence ((|>), Seq(..))
import qualified Data.Sequence as Q
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Data.Text.Prettyprint.Doc ((<+>))
import           Protolude
import           Unbound.Generics.LocallyNameless

import           CP.Environment
import           CP.PrettyPrint
import           CP.Source.Syntax
import           CP.Source.Desugar
import qualified CP.Target.Syntax as T

data L = LTy SType | LLa Label | LAll TyName SType

{- |

----------------------------
-- Coercion
----------------------------

-}
type Co = T.UExpr


coId :: Co
coId = T.elam "x" (T.evar "x")

coTrans :: Co -> Co -> Co
coTrans c1 c2 = T.elam "x" (T.eapp c1 (T.eapp c2 (T.evar "x")))


coTop :: Co
coTop = T.elam "x" T.UUnit

coTopArr :: Co
coTopArr = T.elam "x" (T.elam "y" T.UUnit)

coArr :: Co -> Co -> Co
coArr c1 c2 =
  let body = T.eapp c2 (T.eapp (T.evar "f") (T.eapp c1 (T.evar "x")))
  in T.elam "f" (T.elam "x" body)


coPair :: Co -> Co -> Co
coPair c1 c2 =
  T.elam "x" (T.UPair (T.eapp c1 (T.evar "x")) (T.eapp c2 (T.evar "x")))


coProj1 :: Co
coProj1 = T.elam "x" (T.UP1 (T.evar "x"))


coProj2 :: Co
coProj2 = T.elam "x" (T.UP2 (T.evar "x"))


coDistArr :: Co
coDistArr = T.elam "x" (T.elam "y" $ T.UPair
                     (T.eapp (T.UP1 (T.evar "x")) (T.evar "y"))
                     (T.eapp (T.UP2 (T.evar "x")) (T.evar "y")))



{- |

----------------------------
-- Meta-function
----------------------------

-}
calTop :: Seq L -> Co
calTop Empty = coTop
calTop (LLa _ :<| fs) = coTrans (calTop fs) coId
calTop (LTy _ :<| fs) =
  coTrans (coArr coTop (calTop fs)) coTopArr
calTop (LAll _ _ :<| fs) = coTrans (calTop fs) coId

calAnd :: Seq L -> Co
calAnd Empty = coId
calAnd (LLa _ :<| fs) = coTrans (calAnd fs) coId
calAnd (LTy _ :<| fs) = coTrans (coArr coId (calAnd fs)) coDistArr
calAnd (LAll _ _ :<| fs) = coTrans (calAnd fs) coId



{- |

----------------------------
-- A <: B ~> E
----------------------------

Subtyping (<:) is defined only between types of kind *.

WARN: They must be expanded first

-}
subtype :: Ctx -> SType -> SType -> Either FDoc T.UExpr
subtype ctx st tt = runExcept $ runFreshMT go
  where
    go :: (FreshMT (Except FDoc)) T.UExpr
    go = do
      let a = expandType ctx st
      let b = expandType ctx tt
      subtypeS Q.empty a b
    subtypeS :: Q.Seq L -> SType -> SType -> (FreshMT (Except FDoc)) T.UExpr
    -- Base cases
    subtypeS Empty NumT NumT = return coId
    subtypeS Empty BoolT BoolT = return coId
    subtypeS Empty StringT StringT = return coId
    subtypeS Empty BotT BotT = return coId
    subtypeS _ BotT _ = return T.Bot
    subtypeS fs _ TopT = return $ coTrans (calTop fs) coTop
    subtypeS Empty (TVar a) (TVar b) =
      if a /= b
        then throwError $
             "variables not equal:" <+>
             Pretty.squotes (Pretty.pretty a) <+>
             "and" <+> Pretty.squotes (Pretty.pretty b)
        else return coId
    -- NumT
    subtypeS fs (And a1 a2) NumT = do
      let c1 = do
            c <- subtypeS fs a1 NumT
            return $ coTrans c coProj1
          c2 = do
            c <- subtypeS fs a2 NumT
            return $ coTrans c coProj2
      c1 `catchError` const c2
    subtypeS (LTy a :<| fs) (Arr a1 a2) NumT = do
      c1 <- subtypeS Q.empty a a1
      c2 <- subtypeS fs a2 NumT
      return $ coArr c1 c2
    subtypeS (LLa l :<| fs) (SRecT l' a) NumT =
      if l == l'
        then subtypeS fs a NumT
        else throwError $
             "Labels" <+>
             Pretty.squotes (Pretty.pretty l) <+>
             "and" <+> Pretty.squotes (Pretty.pretty l') <+> "mismatch"
    subtypeS (LAll tv a :<| fs) (DForall b) NumT = do
        ((tv' , Embed b'),  t) <- unbind b
        subtypeS Q.empty a b'
        subtypeS fs (subst tv' (TVar tv) t) NumT
    -- BoolT
    subtypeS fs (And a1 a2) BoolT = do
      let c1 = do
            c <- subtypeS fs a1 BoolT
            return $ coTrans c coProj1
          c2 = do
            c <- subtypeS fs a2 BoolT
            return $ coTrans c coProj2
      c1 `catchError` const c2
    subtypeS (LTy a :<| fs) (Arr a1 a2) BoolT = do
      c1 <- subtypeS Q.empty a a1
      c2 <- subtypeS fs a2 BoolT
      return $ coArr c1 c2
    subtypeS (LLa l :<| fs) (SRecT l' a) BoolT =
      if l == l'
        then subtypeS fs a BoolT
        else throwError $
             "Labels" <+>
             Pretty.pretty l <+> "and" <+> Pretty.pretty l' <+> "mismatch"
    subtypeS (LAll tv a :<| fs) (DForall b) BoolT = do
        ((tv' , Embed b'),  t) <- unbind b
        subtypeS Q.empty a b'
        subtypeS fs (subst tv' (TVar tv) t) BoolT
    -- StringT
    subtypeS fs (And a1 a2) StringT = do
      let c1 = do
            c <- subtypeS fs a1 StringT
            return $ coTrans c coProj1
          c2 = do
            c <- subtypeS fs a2 StringT
            return $ coTrans c coProj2
      c1 `catchError` const c2
    subtypeS (LTy a :<| fs) (Arr a1 a2) StringT = do
      c1 <- subtypeS Q.empty a a1
      c2 <- subtypeS fs a2 StringT
      return $ coArr c1 c2
    subtypeS (LLa l :<| fs) (SRecT l' a) StringT =
      if l == l'
        then subtypeS fs a StringT
        else throwError $
             "Labels" <+>
             Pretty.squotes (Pretty.pretty l) <+>
             "and" <+> Pretty.squotes (Pretty.pretty l') <+> "mismatch"
    subtypeS (LAll tv a :<| fs) (DForall b) StringT = do
        ((tv' , Embed b'),  t) <- unbind b
        subtypeS Q.empty a b'
        subtypeS fs (subst tv' (TVar tv) t) StringT
    -- type variable
    subtypeS fs (And a1 a2) (TVar x) = do
      let c1 = do
            c <- subtypeS fs a1 (TVar x)
            return $ coTrans c coProj1
          c2 = do
            c <- subtypeS fs a2 (TVar x)
            return $ coTrans c coProj2
      c1 `catchError` const c2
    subtypeS (LTy a :<| fs) (Arr a1 a2) (TVar x) = do
      c1 <- subtypeS Q.empty a a1
      c2 <- subtypeS fs a2 (TVar x)
      return $ coArr c1 c2
    subtypeS (LLa l :<| fs) (SRecT l' a) (TVar x) =
      if l == l'
        then subtypeS fs a (TVar x)
        else throwError $
             "Labels" <+>
             Pretty.squotes (Pretty.pretty l) <+>
             "and" <+> Pretty.squotes (Pretty.pretty l') <+> "mismatch"
    subtypeS (LAll tv a :<| fs) (DForall b) (TVar x) = do
        ((tv' , Embed b'),  t) <- unbind b
        subtypeS Q.empty a b'
        subtypeS fs (subst tv' (TVar tv) t) (TVar x)
    -- Inductive cases
    subtypeS fs a (And b1 b2) = do
      c1 <- subtypeS fs a b1
      c2 <- subtypeS fs a b2
      return $ coTrans (calAnd fs) (coPair c1 c2)
    subtypeS fs a (Arr b1 b2) = subtypeS (fs |> LTy b1) a b2
    subtypeS fs a (SRecT l b) = subtypeS (fs |> LLa l) a b
    subtypeS fs a (DForall b) = do
      ((tv, Embed b'), t) <- unbind b
      subtypeS (fs |> LAll tv b') a t
    subtypeS fs (TraitT b1 b2) a = subtypeS fs (Arr b1 b2) a
    subtypeS fs a (TraitT b1 b2) = subtypeS fs a (Arr b1 b2)
    -- ListT: FIXME!!!
    subtypeS fs (ListT a) (ListT b) =
      if a == b then return coId
      else throwError $ "Lists are invariant, but found" <+>
                        Pretty.squotes (pprint a) <+> "and" <+>
                        Pretty.squotes (pprint b)
    subtypeS fs (And a1 a2) (ListT t) = do
      let c1 = do
            c <- subtypeS fs a1 (ListT t)
            return $ coTrans c coProj1
          c2 = do
            c <- subtypeS fs a2 (ListT t)
            return $ coTrans c coProj2
      c1 `catchError` const c2
    subtypeS (LTy a :<| fs) (Arr a1 a2) (ListT t) = do
      c1 <- subtypeS Q.empty a a1
      c2 <- subtypeS fs a2 (ListT t)
      return $ coArr c1 c2
    subtypeS (LLa l :<| fs) (SRecT l' a) (ListT t) =
      if l == l'
        then subtypeS fs a (ListT t)
        else throwError $
             "Labels" <+>
             Pretty.pretty l <+> "and" <+> Pretty.pretty l' <+> "mismatch"
    subtypeS _ a b =
      throwError $
      "No subtyping relation between" <+>
      Pretty.squotes (pprint a) <+> "and" <+> Pretty.squotes (pprint b)
