{-# LANGUAGE DeriveGeneric, MultiParamTypeClasses #-}

module CP.Target.Syntax where

import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)

import CP.Common


---------------------------
-- Untyped lambda calculus
---------------------------

type UName = Name UExpr

data UExpr = UVar UName
           | UApp UExpr UExpr
           | ULam (Bind UName UExpr)
           | ULet (Bind UName (UExpr, UExpr))  -- recursive let
           | UPair UExpr UExpr
           | UP1 UExpr
           | UP2 UExpr
           | ULitV Double
           | UBoolV Bool
           | UStrV String
           | UUnit
           | UPrimOp Operation UExpr UExpr
           | UIf UExpr UExpr UExpr
           | UToString UExpr
           | USqrt UExpr
           | UListNew UExpr UExpr
           | UListLength UExpr
           | UListSum UExpr
           | UListScanl UExpr
           | UListLzw UExpr UExpr UExpr
           | Bot
           deriving (Show, Generic)

instance Alpha UExpr


instance Subst UExpr ArithOp
instance Subst UExpr LogicalOp
instance Subst UExpr Operation
instance Subst UExpr CompOp
instance Subst UExpr AppendTy
instance Subst UExpr UExpr where
  isvar (UVar v) = Just (SubstName v)
  isvar _ = Nothing

evar :: String -> UExpr
evar = UVar . s2n

ebind :: String -> UExpr -> Bind UName UExpr
ebind n = bind (s2n n)

elam :: String -> UExpr -> UExpr
elam b e = ULam (ebind b e)

eapp :: UExpr -> UExpr -> UExpr
eapp = UApp

elet :: UName -> UExpr -> UExpr -> UExpr
elet n e b = ULet (bind n (e, b))
