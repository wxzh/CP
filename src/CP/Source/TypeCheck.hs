{-# LANGUAGE FlexibleContexts, PatternGuards, NoImplicitPrelude, LambdaCase, OverloadedStrings #-}

-- TODO: generate data from object algebra interfaces?
-- WARNING: Types must be expanded before desugaring

module CP.Source.TypeCheck
  ( tcModule,
  ) where

import qualified Data.Map as M
import           Data.List (foldr1)
import           Data.Maybe
import           Data.Text.Prettyprint.Doc ((<+>))
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Protolude hiding (head,ap)
import           Unbound.Generics.LocallyNameless
import           Unsafe

import           CP.Common
import           CP.Environment
import           CP.PrettyPrint
import           CP.Source.Desugar
import           CP.Source.Subtyping
import           CP.Source.Syntax
import qualified CP.Target.Syntax as T
import           CP.Util

tcModule :: Module -> TcMonad (SType, T.UExpr)
tcModule m = do
  let decls = moduleEntries m
  -- Step 1: Desugar decls
  let sdecls = desugar decls
  -- Step 2: Check module
  (ty, m') <- tcM sdecls (desugarExpr $ mainExpr m) []
  errThrow [DD $ mainExpr m']
  (_, e) <- localCtx (\_ -> emptyCtx) (tcModule2 m')
  return (ty, e)
  where
    tcM :: [SDecl] -> Expr -> [SDecl] -> TcMonad (SType, Module)
    tcM [] e decls = do
      (ty, e') <- infer2 e
      return (ty, Module decls e')

    tcM (DefDecl (TmBind n tvars vars e rt flag):xs) main decls = do
      ty <- lookupVarTy' (s2n n)
      let vars' = if (all (isJust . snd) vars || isNothing ty)
                  then vars
                  else zip (map fst vars) (map Just (flattenArr (fromJust ty)))
      let decl' = TmBind n tvars vars' e rt flag
      let (n, e) = normalizeTmDecl decl'
      lookupTmDef (s2n n) >>= \case
        Nothing -> do
          (ty, e') <- infer2 e
          ty' <- translateType ty
          let decl = DefDecl $ TmBind n [] [] e' (Just ty') False
          localCtx (extendVarCtx (s2n n) ty) (tcM xs main (decls ++ [decl]))
        Just _ -> errThrow [DS $ "Multiple definitions of" <+> Pretty.pretty n]

    tcM ((TypeDecl (TypeBind n sorts params extend rhs)):xs) main decls = do
      ctx <- askCtx
      let sorts' = concatMap (\s -> [(s2n s, Star), (s2n $ "#" ++ s, Star)]) sorts
          extend' = map (expandType $ extendSortCtxs (map s2n sorts) ctx) extend
          rhs' = distinguish sorts $ expandType ctx rhs
          ty = pullRight (sorts' ++ params) $ maybe rhs' (And rhs') extend'
      let decl = TypeDecl $ TypeBind n [] [] Nothing ty
      localCtx (addTypeSynonym (s2n n) ty Star) (tcM xs main (decls ++ [decl]))


tcModule2 :: Module -> TcMonad (SType, T.UExpr)
tcModule2 m = do
  let decls = moduleEntries m
  (ty, target) <- tcM decls (mainExpr m)
  return (ty, target)
  where
    tcM :: [SDecl] -> Expr -> TcMonad (SType, T.UExpr)
    tcM [] main = infer main
    tcM (DefDecl d:xs) main = do
      let (n, e) = normalizeTmDecl d
      (t, e') <- infer e
      second (T.elet (s2n n) e') <$>
        localCtx (extendVarCtx (s2n n) t) (tcM xs main)
    tcM ((TypeDecl (TypeBind n _ _ _ ty)):xs) main = do
      localCtx (addTypeSynonym (s2n n) ty Star) (tcM xs main)

{- |
foreach Γ, xs ⊢ trait [self : A] { l2 = e } ⇒ B ~> E
------------------------------------------
Γ ⊢ (l1 xs).l2 [self: A] = e ⇒ B ~> E
-}
-- tcTmDecl (Patterns ps) = do
  -- if all isJust (snds params)
  -- then do
  -- ctx <- askCtx
  -- res <- mapM tcPattern ps
  -- let (t, e) = foldr1 (\(t,e) (ta,ea) -> (And t ta, Merge e ea)) res
  -- -- let params' = zip (fsts params) (catMaybes $ snds params)
  -- return $ (n, foldr (\(_,t1) t -> Arr t1 t) t params, foldr (\(x,ty) e -> LamA (bind (x, Embed ty) e)) e params)
  -- else do
  --   ty <- lookupVarTy (s2n n)
  --   let tys = paramTys ty
  --   let params' = zip (fsts params) tys
  --   res <- mapM tcPattern $ map (\p -> p {patParams = zip (fsts (patParams p)) $ map Just tys}) ps
  --   let (t, e) = foldr1 (\(t,e) (ta,ea) -> (And t ta, Merge e ea)) res
  --   return $ (n, foldr (\(_,t1) t -> Arr t1 t) t params', foldr (\(x,ty) e -> LamA (bind (x, Embed ty) e)) e params')
  -- where
  --   n = patName $ head ps
  --   params = patParams $ head ps

flattenArr :: SType -> [SType]
flattenArr (Arr t1 t2) = t1 : flattenArr t2
flattenArr _ = []


-- | Kinding.
kind :: Fresh m => Ctx -> SType -> m (Maybe Kind)
kind d (TVar a) = return $ lookupTVarKindMaybe d a
kind _ NumT = return $ Just Star
kind _ BoolT = return $ Just Star
kind _ StringT = return $ Just Star
kind _ TopT = return $ Just Star
kind _ BotT = return $ Just Star
kind d (Arr t1 t2) = justStarIffAllHaveKindStar d [t1, t2]
kind d (And t1 t2) = justStarIffAllHaveKindStar d [t1, t2]
kind d (TraitT t1 t2) = justStarIffAllHaveKindStar d [t1, t2]
kind d (DForall b) = do
  ((a, _), t) <- unbind b
  kind (extendTVarCtx a Star d) t
kind d (SRecT _ t) = justStarIffAllHaveKindStar d [t]
kind d (ListT t) = justStarIffAllHaveKindStar d [t]


{- |
    Δ,x::k1 ⊢ t :: k
    -------------------- (K-Abs)
    Δ ⊢ λx:k1. t :: k1 -> k
-}
kind d (OpAbs b) = do
  ((x, Embed k1), t) <- unbind b
  maybe_k <- kind (extendTVarCtx x k1 d) t
  case maybe_k of
    Nothing -> return Nothing
    Just k  -> return $ Just (KArrow k1 k)

{- |
    Δ ⊢ t1 :: k11 -> k12  Δ ⊢ t2 :: k11
    ------------------------------------ (K-App)
    Δ ⊢ t1 t2 :: k12
-}
kind d (OpApp t1 t2) = do
  maybe_k1 <- kind d t1
  maybe_k2 <- kind d t2
  case (maybe_k1, maybe_k2) of
    (Just (KArrow k11 k12), Just k2)
      | k2 == k11 -> return (Just k12)
    _ -> return Nothing

kind _ _ = return Nothing


justStarIffAllHaveKindStar :: Fresh m => Ctx -> [SType] -> m (Maybe Kind)
justStarIffAllHaveKindStar d ts = do
  ps <- mapM (hasKindStar d) ts
  if and ps
    then return $ Just Star
    else return Nothing

hasKindStar :: Fresh m => Ctx -> SType -> m Bool
hasKindStar d t = do
  k <- kind d t
  return (k == Just Star)



-- | "Pull" the type params at the LHS of the equal sign to the right.
-- A (high-level) example:
--   A B t  ->  \A. \B. t
pullRight :: [(TyName, Kind)] -> SType -> SType
pullRight params t = foldr (\(n, k) t' -> OpAbs (bind (n, embed k) t')) t params


infer2 :: Expr -> TcMonad (SType, Expr)

infer2 Top = return (TopT, Top)

infer2 (LitV n) = return (NumT, LitV n)

infer2 (BoolV b) = return (BoolT, BoolV b)

infer2 (StrV b) = return (StringT, StrV b)

infer2 (Var x) = do
  t <- lookupVarTy x
  return (t, Var x)

infer2 (Anno e a) = do
  ctx <- askCtx
  let a' = expandType ctx a
  -- errThrow [DS "DEBUG: infer anno", DD a']
  e' <- fillType a' e
  e'' <- localCtx (extendCtxRcd a') $ tcheck2 e' a'
  a'' <- translateType a'
  return (a, Anno e'' a'')

infer2 (App e1 e2) = do
  (arr, e1') <- infer2 e1
  c <- askCtx
  case expandType c arr of
    Arr a1 a2 -> do
      (t2,_) <- infer2 e2
      e2' <- tcheck2 e2 a1
      return (a2, App e1' e2')
    _ ->
      errThrow [DS "infer2: Applying to a non function type", DD arr]

infer2 (Forward e1 e2) = do
  (arr, e1') <- infer2 e1
  c <- askCtx
  case expandType c arr of
    TraitT a1 a2 -> do
      e2' <- tcheck2 e2 a1
      return (a2, App e1' e2')
    _ ->
      errThrow [DS "Forwarding on a non trait type", DD e1]

infer2 (TApp e a) = do
  wf a
  (t, e') <- infer2 e
  ctx <- askCtx
  case expandType ctx t of
    DForall t' -> do
      ((x, Embed b), c) <- unbind t'
      disjoint ctx (expandType ctx a) (expandType ctx b)
      a' <- translateType a
      return (subst x a c, TApp e' a')
    t' -> errThrow [DS "SType application mismatch", DD t']

{- |

Γ ⊢ e1 ⇒ Trait[B1,A1] ~> E1
Γ ⊢ e2 ⇒ Trait[B2,A2] ~> E2
Γ ⊢ A1∗A2
Γ ⊢ lam (self: B1 & B2) E1 self ,, E2 self
------------------------------------------
Γ ⊢ e1,,e2 ⇒ A&B ~> (E1, E2)

-}
-- infer2 (Merge e1@(AnonyTrait t1) e2@(AnonyTrait t2)) = do
--   (TraitT b1 a1, e1') <- infer2 e1
--   (TraitT b2 a2, e2') <- infer2 e2
--   ctx <- askCtx
--   disjoint ctx (expandType ctx a1) (expandType ctx a2)
--   return (TraitT (And b1 b2) (And a1 a2), e1')

infer2 (Merge e1 e2) = do
  (a, e1') <- infer2 e1
  (b, e2') <- infer2 e2
  ctx <- askCtx
  case (a,b) of
    (TraitT b1 a1, TraitT b2 a2) -> do
      disjoint ctx (expandType ctx a1) (expandType ctx a2)
      b1' <- translateType b1
      b2' <- translateType b2
      return (TraitT (And b1 b2) (And a1 a2), (elam2 ("*self", And b1' b2') (Merge (e1' `eapp` evar "*self") (e2' `eapp` evar "*self"))))
    _ -> do
      disjoint ctx (expandType ctx a) (expandType ctx b)
      return (And a b, Merge e1' e2')

--TODO: use a fresh var to capture E1
{- |
Γ ⊢ e1 ⇒ {l1 : A1} & ... & {ln : An} ~> E1  Γ, l1 : A1 ... ln : An ⊢ E2 ⇒ t2
-----------------------------------------------------------------------
Γ ⊢ open e1 e2 ⇒ t2 ~> let l1 = E1.l1 in ... let ln = E1.ln in E2

-}
infer2 (Open e1 e2) = do
  (t1, e1') <- infer2 e1
  ctx <- askCtx
  let t1' = expandType ctx t1
  -- errThrow [DS $ "Open: ", DD t1']
  (t2, e2') <- localCtx (extendCtxRcd t1') $ infer2 e2
  return (t2, M.foldrWithKey (\l _ e -> elet l (Acc e1' l) e) e2' (recordFields t1'))

infer2 (New e) = do
  (ty,e') <- infer2 e
  ctx <- askCtx
  case expandType ctx ty of
    TraitT t1 t2 -> do
      case subtype ctx t2 t1 of
        Right _ -> do
          t2' <- translateType t2
          return (t2, eletr "self" t2' (eapp e' (evar "self")) (evar "self"))
        Left er ->
          errThrow [DS $ "Subtyping failed in new:" <+> er]
    t ->
      errThrow [DS $ "New expected a Trait type:", DD t]

infer2 (AnonyTrait trait) = do
  let (self,b) = selfType trait
  let body = traitBody trait
  wf b
  ctx <- askCtx
  let ty = expandType ctx $ fromMaybe TopT (implements trait)
  wf ty
  b' <- translateType b
  case (traitSuper trait) of
    Just ep -> do
      (tp, ep') <- localCtx (extendVarCtx (s2n self) b) $ infer2 ep
      case tp of
        TraitT bp ap ->
          case subtype ctx b bp of
            Right _ -> do
              (c,e) <- localCtx (extendCtxRcd ty . extendVarCtxs [(s2n self,b),(s2n "super",ap)]) $ infer2 body
              ap' <- tcOverrides (expandType ctx ap) (collectOverrides body)
              disjoint ctx c ap'
              case subtype ctx (And c ap') ty of
                Right _ ->
                  return (TraitT b (And ap' c), elam2 (self, b') (elet "super" (eapp ep' (evar self)) (Merge (Anno (evar "super") ap') e)))
                Left er -> errThrow [DS $ "Unsatisfied implementation:" <+> er, DD (And c ap'), DD ty]
            Left er -> errThrow [DS $ "Subtyping failed in self type:" <+> er]
        _ -> errThrow [DS $ "Inherits expect a Trait type:" <+> pprint tp]
    _ -> do
      (c,e) <- localCtx (extendCtxRcd ty . extendVarCtx (s2n self) b) $ infer2 body
      case subtype ctx c ty of
        Right _ -> return (TraitT b c, elam2 (self, b') e)
        Left er -> errThrow [DS $ "Unsatisfied implemented:" <+> er, DD c, DD ty]

infer2 (If e1 e2 e3) = do
  e1' <- tcheck2 e1 BoolT
  (t2, e2') <- infer2 e2
  (t3, e3') <- infer2 e3
  ctx <- askCtx
  let t2' = expandType ctx t2
  let t3' = expandType ctx t3
  if aeq t2' t3'
    then return (t2, If e1' e2' e3')
    else errThrow [DS "If branch type mismatch"]

infer2 (DLam t) = do
  ((x, Embed a), e) <- unbind t
  wf a
  (b, e') <- localCtx (extendConstrainedTVarCtx x a) $ infer2 e
  a' <- translateType a
  return (DForall (bind (x, embed a) b), DLam (bind (x, Embed a') e'))

infer2 (DRec l e b) = do
  lookupVarTy' (s2n l) >>= \case
    Nothing -> do
      (a, e') <- infer2 e
      return (SRecT l a, DRec l e' b)
    Just ty -> do
      e' <- fillType ty e
      (a, e'') <- infer2 e'
      return (SRecT l a, DRec l e'' b)

infer2 (PrimOp op e1 e2) =
  case op of
    Arith _ -> do
      e1' <- tcheck2 e1 NumT
      e2' <- tcheck2 e2 NumT
      return (NumT, PrimOp op e1' e2')
    Logical _ -> do
      e1' <- tcheck2 e1 BoolT
      e2' <- tcheck2 e2 BoolT
      return (BoolT, PrimOp op e1' e2')
    Comp cop | cop == Equ || cop == Neq -> do
      let res1 = do
            e1' <- tcheck2 e1 NumT
            e2' <- tcheck2 e2 NumT
            return (e1', e2')
          res2 = do
            e1' <- tcheck2 e1 StringT
            e2' <- tcheck2 e2 StringT
            return (e1', e2')
          res3 = do
            e1' <- tcheck2 e1 BoolT
            e2' <- tcheck2 e2 BoolT
            return (e1', e2')
      (e1', e2') <- res1 `catchError` const (res2 `catchError` const res3)
      return (BoolT, PrimOp op e1' e2')
    Comp _ -> do
      e1' <- tcheck2 e1 NumT
      e2' <- tcheck2 e2 NumT
      return (BoolT, PrimOp op e1' e2')
    Append Unknown -> do
      (t, e1') <- infer2 e1
      case t of
        StringT -> do
          e2' <- tcheck2 e2 StringT
          return (StringT, PrimOp (Append Str) e1' e2')
        ListT t' -> do
          e2' <- tcheck2 e2 (ListT t')
          return (ListT t', PrimOp (Append Lst) e1' e2')
        _ -> errThrow [DS "(++) expected String or List, but got:", DD t]
    At -> do
      (t, e1') <- infer2 e1
      case t of
        ListT t' -> do
          e2' <- tcheck2 e2 NumT
          return (t', PrimOp op e1' e2')
        _ -> errThrow [DS "(!!) expected List, but got:", DD t]

infer2 (Letrec b) = do
  ((x, Embed ty), (e1, e2)) <- unbind b
  (e1', e2', t') <-
    maybe
      (do (t, e1') <- infer2 e1
          (t', e2') <- localCtx (extendVarCtx x t) $ infer2 e2
          return (e1', e2', t'))
      (\t -> do
         e1' <- localCtx (extendVarCtx x t) $ tcheck2 e1 t
         (t', e2') <- localCtx (extendVarCtx x t) $ infer2 e2
         return (e1', e2', t'))
      ty
  return (t', Letrec (bind (x, Embed ty) (e1', e2')))

infer2 (LamA t) = do
  ((x, Embed a), e) <- unbind t
  wf a
  (b, e') <- localCtx (extendVarCtx x a) $ infer2 e
  a' <- translateType a
  return (Arr a b, LamA (bind (x, Embed a') e'))

infer2 (Acc e "toString") = do
  (_, e') <- infer2 e
  return (StringT, Acc e' "toString")

infer2 (Acc e "sqrt") = do
  e' <- tcheck2 e NumT
  return (NumT, Acc e' "sqrt")

infer2 (Acc e l) = do
  (t, e') <- infer2 e
  ctx <- askCtx
  case select (expandType ctx t) l of
    [] -> errThrow [DS $ "Expected a record with label" <+> Pretty.squotes (Pretty.pretty l) <+> "but got:", DD t]
    ls -> -- non-empty list, safe to use unsafe features
      let (tys, cs) = unzip ls
      in return
           (unsafeFromJust (foldl1May And tys), Acc e' l)

infer2 (Remove e l lt) = do
  (t, e') <- infer2 e
  ctx <- askCtx
  let t' = expandType ctx t
  case restrict2 t' l lt of
    Just a -> do
      a' <- translateType a
      return (a, Anno e' a')
    _ -> errThrow [DS $ "Remove: Expected a record with label" <+> Pretty.squotes (Pretty.pretty l) <+> "but got:", DD t']

infer2 Bot = return (BotT, Bot)

infer2 (Pos p tm) = extendSourceLocation p tm $ infer2 tm

infer2 (ListNew t n f) = do
  n' <- tcheck2 n NumT
  f' <- tcheck2 f (Arr NumT t)
  return (ListT t, ListNew t n' f')

infer2 (ListLength l) = do
  (t, l') <- infer2 l
  case t of
    ListT _ -> return (NumT, ListLength l')
    _ -> errThrow [DS "length expected List, but got:", DD t]

infer2 (ListSum l) = do
  l' <- tcheck2 l (ListT NumT)
  return (NumT, ListSum l')

infer2 (ListScanl l) = do
  l' <- tcheck2 l (ListT NumT)
  return (ListT NumT, ListScanl l')

infer2 (ListLzw t f l1 l2) = do
  f' <- tcheck2 f (Arr t (Arr t t))
  l1' <- tcheck2 l1 (ListT t)
  l2' <- tcheck2 l2 (ListT t)
  return (ListT t, ListLzw t f' l1' l2')

infer2 a = errThrow [DS "Infer2 not implemented:", DD a]


tcheck2 :: Expr -> SType -> TcMonad Expr
tcheck2 (Lam l) (Arr a b) = do
  (x, e) <- unbind l
  wf a
  e' <- localCtx (extendVarCtx x a) $ tcheck2 e b
  return $ Lam (bind x e')

tcheck2 (DLam l) (DForall b) =
  unbind2 l b >>= \case
    Just ((x, Embed a), e, _, t') -> do
      wf a
      e' <- localCtx (extendConstrainedTVarCtx x a) $ tcheck2 e t'
      return $ DLam (bind (x, Embed a) e')
    Nothing -> errThrow [DS "Patterns have different binding variables"]

tcheck2 (DRec l e b) (SRecT l' a) = do
  when (l /= l') $
    errThrow [DS $ "Labels not equal" <+> Pretty.pretty l <+> "and" <+> Pretty.pretty l']
  e' <- tcheck2 e a
  return (DRec l e' b)

tcheck2 (Pos p tm) ty = extendSourceLocation p tm $ tcheck2 tm ty

tcheck2 e b = checkMode2 e b

checkMode2 :: Expr -> SType -> TcMonad Expr
checkMode2 e b = do
  wf b
  (a, e') <- infer2 e
  ctx <- askCtx
  case subtype ctx a b of
    Right c -> return e'
    Left er -> errThrow [DS $ "Subtyping failed in checkmode2:" <+> er]

---------------------------
-- Γ ⊢ e ⇒ A ~> E
---------------------------

infer :: Expr -> TcMonad (SType, T.UExpr)

{- |

Γ ⊢ ⊤ ⇒ ⊤  ~> ()

-}
infer Top = return (TopT, T.UUnit)

infer (LitV n) = return (NumT, T.ULitV n)

infer (BoolV b) = return (BoolT, T.UBoolV b)

infer (StrV b) = return (StringT, T.UStrV b)

{- |

   x:A ∈ Γ
---------------
Γ ⊢ x ⇒ A ~> x

-}
infer (Var x) = do
  t <- lookupVarTy x
  return (t, T.UVar (translate x)) -- Change the sort of a name

{- |

Γ ⊢ e ⇐ A  ~> E
------------------
Γ ⊢ e : A ⇒ A ~> E

-}
infer (Anno e a) = do
  c <- askCtx
  let a' = expandType c a
  e' <- tcheck e a'
  return (a, e')

{- |

Γ ⊢ e1 ⇒ A1 -> A2  ~> E1
Γ ⊢ e2 ⇐ A1        ~> E2
----------------------------
Γ ⊢ e1 e2 ⇒ A2     ~> E1 E2

-}
infer (App e1 e2) = do
  (arr, e1') <- infer e1
  c <- askCtx
  case expandType c arr of
    Arr a1 a2 -> do
      e2' <- tcheck e2 a1
      return (a2, T.UApp e1' e2')
    t ->
      errThrow [DS "Term application mismatch", DD (App e1 e2), DD t]
        -- (Pretty.hang 2 $
        --   <+>
        --  Pretty.squotes (pprint inp) <> Pretty.colon <> Pretty.line <> "function" <+>
        --  Pretty.squotes (pprint e1) <+> "has type" <+> Pretty.squotes (pprint arr))

{- |

Γ ⊢ e ⇒ ∀(α ∗ B). C  ~> E
Γ ⊢ A
Γ ⊢ A ∗ B
-------------------------------
Γ ⊢ e A ⇒ [α := A] C  ~> E

-}
infer (TApp e a) = do
  wf a
  (t, e') <- infer e
  ctx <- askCtx
  case expandType ctx t of
    DForall t' -> do
      ((x, Embed b), c) <- unbind t'
      disjoint ctx (expandType ctx a) (expandType ctx b)
      return (subst x a c, e')
    _ -> errThrow [DS "SType application mismatch"]
      -- throwError
      --   (Pretty.hang 2 $
      --    "type of application mismatch in" <+>
      --    Pretty.squotes (pprint inp) <> Pretty.colon <> Pretty.line <> "type-level function" <+>
      --    Pretty.squotes (pprint e) <+> "has type" <+> Pretty.squotes (pprint t))

{- |

Γ ⊢ e1 ⇒ A ~> E1
Γ ⊢ e2 ⇒ B ~> E2
Γ ⊢ A∗B
------------------------------
Γ ⊢ e1,,e2 ⇒ A&B ~> (E1, E2)

-}
infer (Merge e1 e2) = do
  (a, e1') <- infer e1
  (b, e2') <- infer e2
  ctx <- askCtx
  disjoint ctx (expandType ctx a) (expandType ctx b)
  return (And a b, T.UPair e1' e2')


{- |

Γ ⊢ e ⇒ A ~> E
----------------------
Γ ⊢{l=e} ⇒ {l:A} ~> E

-}
infer (DRec l e _) = do
  (a, e') <- infer e
  return (SRecT l a, e')

{- |

Γ ⊢ e ⇒ {l : A} ~> E
----------------------
Γ ⊢ e.l ⇒ A ~> E

The above is what is shown in the paper. In the implementation, we'd like to
avoid annotating a record before projection. The following is the modified rule:

Γ ⊢ e ⇒ t ~> E
t • l = t1 ~> c
-----------------------
Γ ⊢ e.l ⇒ t1 ~> c E

-}

-- ad-hoc extension of toString method
infer (Acc e "toString") = do
  (_, e') <- infer e
  return (StringT, T.UToString e')

infer (Acc e "sqrt") = do
  e' <- tcheck e NumT
  return (NumT, T.USqrt e')

infer (Acc e l) = do
  (t, e') <- infer e
  ctx <- askCtx
  case select (expandType ctx t) l of
    [] -> errThrow [DS $ "Expected a record with label" <+> Pretty.squotes (Pretty.pretty l) <+> "but got:", DD t]
      -- throwError
      --   (Pretty.hang 2 $
      --    "expect a record type with label" <+>
      --    Pretty.squotes (Pretty.pretty l) <+>
      --    "for" <+>
      --    Pretty.squotes (pprint e) <> Pretty.line <> "but got" <+> Pretty.squotes (pprint t))
    ls -> -- non-empty list, safe to use unsafe features
      let (tys, cs) = unzip ls
      in return
           ( unsafeFromJust (foldl1May And tys)
           , unsafeFromJust (foldl1May T.UPair (map (`T.UApp` e') cs)))


{- |


Γ ⊢ e ⇒ t ~> E
t \ l = t1 ~> c
-----------------------
Γ ⊢ e \ l ⇒ t1 ~> c E

-}

infer (Remove e l lt) = do
  (t, e') <- infer e
  ctx <- askCtx
  let t' = expandType ctx t
  case restrict t' l lt of
    Just (a, c) -> return (a, T.UApp c e')
    -- Silently... like nothing happened
    _ -> -- return (t, e')
      errThrow [DS $ "Expected a record with label" <+> Pretty.squotes (Pretty.pretty l) <+> "but got:", DD t', DD e]
      -- throwError
      --   (Pretty.hang 2 $
      --    "expect a record type with label" <+>
      --    Pretty.squotes (Pretty.pretty l) <+>
      --    "for" <+>
      --    Pretty.squotes (pprint e) <> Pretty.line <> "but got" <+> Pretty.squotes (pprint t))




{- |

Γ ⊢ A
Γ , a * A ⊢ e ⇒ B ~> E
a fresh
---------------------------------
Γ ⊢ Λ(α∗A).e ⇒ ∀(α∗A).B ~> E

-}
infer (DLam t) = do
  ((x, Embed a), e) <- unbind t
  wf a
  (b, e') <- localCtx (extendConstrainedTVarCtx x a) $ infer e
  return (DForall (bind (x, embed a) b), e')

infer (PrimOp op e1 e2) =
  case op of
    Arith _ -> do
      e1' <- tcheck e1 NumT
      e2' <- tcheck e2 NumT
      return (NumT, T.UPrimOp op e1' e2')
    Logical _ -> do
      e1' <- tcheck e1 BoolT
      e2' <- tcheck e2 BoolT
      return (BoolT, T.UPrimOp op e1' e2')
    Comp cop | cop == Equ || cop == Neq -> do
      let res1 = do
            e1' <- tcheck e1 NumT
            e2' <- tcheck e2 NumT
            return (e1', e2')
          res2 = do
            e1' <- tcheck e1 StringT
            e2' <- tcheck e2 StringT
            return (e1', e2')
          res3 = do
            e1' <- tcheck e1 BoolT
            e2' <- tcheck e2 BoolT
            return (e1', e2')
      (e1', e2') <- res1 `catchError` const (res2 `catchError` const res3)
      return (BoolT, T.UPrimOp op e1' e2')
    Comp _ -> do
      e1' <- tcheck e1 NumT
      e2' <- tcheck e2 NumT
      return (BoolT, T.UPrimOp op e1' e2')
    Append Str -> do
      e1' <- tcheck e1 StringT
      e2' <- tcheck e2 StringT
      return (StringT, T.UPrimOp op e1' e2')
    Append Lst -> do
      (t, e1') <- infer e1
      case t of
        ListT t' -> do
          e2' <- tcheck e2 (ListT t')
          return (ListT t', T.UPrimOp op e1' e2')
        _ -> errThrow [DS "(++) expected List, but got:", DD t]
    At -> do
      (t, e1') <- infer e1
      case t of
        ListT t' -> do
          e2' <- tcheck e2 NumT
          return (t', T.UPrimOp op e1' e2')
        _ -> errThrow [DS "(!!) expected List, but got:", DD t]


infer (If e1 e2 e3) = do
  e1' <- tcheck e1 BoolT
  (t2, e2') <- infer e2
  (t3, e3') <- infer e3
  ctx <- askCtx
  let t2' = expandType ctx t2
  let t3' = expandType ctx t3
  if aeq t2' t3'
    then return (t2, T.UIf e1' e2' e3')
    else errThrow [DS "If branch type mismatch"]
    -- throwError
    --      (Pretty.hang 2 $
    --       "if branches type mismatch in" <+>
    --       Pretty.squotes (pprint inp) <> Pretty.colon <> Pretty.line <> Pretty.squotes (pprint e2) <+>
    --       "has type" <+>
    --       Pretty.squotes (pprint t2) <> Pretty.line <> Pretty.squotes (pprint e3) <+>
    --       "has type" <+> Pretty.squotes (pprint t3))

{- |

Γ, x:t ⊢ e1 ⇐ t ~> e1'
Γ, x:t ⊢ e2 ⇒ t' ~> e2'
-----------------------------------------------------
Γ ⊢ letrec x : t = e1 in e2 ⇒ t' ~> let x = e1' in e2'

Γ ⊢ e1 ⇒ t ~> e1'
Γ, x:t ⊢ e2 ⇒ t' ~> e2'
-----------------------------------------------------
Γ ⊢ let x = e1 in e2 ⇒ t' ~> let x = e1' in e2'

-}
infer (Letrec b) = do
  ((x, Embed ty), (e1, e2)) <- unbind b
  (e1', e2', t') <-
    maybe
      (do (t, e1') <- infer e1
          (t', e2') <- localCtx (extendVarCtx x t) $ infer e2
          return (e1', e2', t'))
      (\t -> do
         e1' <- localCtx (extendVarCtx x t) $ tcheck e1 t
         (t', e2') <- localCtx (extendVarCtx x t) $ infer e2
         return (e1', e2', t'))
      ty
  return (t', T.ULet (bind (translate x) (e1', e2')))


infer (LamA t) = do
  ((x, Embed a), e) <- unbind t
  wf a
  (b, e') <- localCtx (extendVarCtx x a) $ infer e
  return (Arr a b, T.ULam (bind (translate x) e'))

infer (Pos p tm) = extendSourceLocation p tm $ infer tm

infer (ListNew t n f) = do
  n' <- tcheck n NumT
  f' <- tcheck f (Arr NumT t)
  return (ListT t, T.UListNew n' f')

infer (ListLength l) = do
  (t, l') <- infer l
  case t of
    ListT _ -> return (NumT, T.UListLength l')
    _ -> errThrow [DS "length expected List, but got:", DD t]

infer (ListSum l) = do
  l' <- tcheck l (ListT NumT)
  return (NumT, T.UListSum l')

infer (ListScanl l) = do
  l' <- tcheck l (ListT NumT)
  return (ListT NumT, T.UListScanl l')

infer (ListLzw t f l1 l2) = do
  f' <- tcheck f (Arr t (Arr t t))
  l1' <- tcheck l1 (ListT t)
  l2' <- tcheck l2 (ListT t)
  return (ListT t, T.UListLzw f' l1' l2')

infer Bot = return (BotT, T.Bot)

infer a = errThrow [DS "Infer not implemented:", DD a]


------------------------
-- Γ ⊢ e ⇐ A ~> E
------------------------

tcheck :: Expr -> SType -> TcMonad T.UExpr

{- |

Γ ⊢ A
Γ , x:A ⊢ e ⇐ B ~> E
---------------------------
Γ ⊢ λx. e ⇐ A → B ~> λx. E

-}
tcheck (Lam l) (Arr a b) = do
  (x, e) <- unbind l
  wf a
  e' <- localCtx (extendVarCtx x a) $ tcheck e b
  return (T.ULam (bind (translate x) e'))

{- |

Γ ⊢ A
Γ , a * A ⊢ e ⇐ B ~> E
---------------------------------
Γ ⊢ Λ(α∗A).e ⇐ ∀(α∗A).B ~> E

-}
tcheck (DLam l) (DForall b) =
  unbind2 l b >>= \case
    Just ((x, Embed a), e, _, t') -> do
      wf a
      localCtx (extendConstrainedTVarCtx x a) $ tcheck e t'
    Nothing -> errThrow [DS "Patterns have different binding variables"]

{- |

TODO: This is not correct, not sure how to do properly

Γ ⊢ e1 ⇐ A ~> E1
Γ ⊢ e2 ⇐ B ~> E2
Γ ⊢ A∗B
------------------------------
Γ ⊢ e1,,e2 ⇐ A&B ~> (E1, E2)

-}
-- tcheck e@(Merge e1 e2) b@(And a' b') = do
--   ctx <- askCtx
--   let re1 = checkMode e b
--       re2 = do
--         e1' <- tcheck e1 a'
--         e2' <- tcheck e2 b'
--         let aa = expandType ctx a'
--         let bb = expandType ctx b'
--         disjoint ctx aa bb
--         return (T.UPair e1' e2')
--   re2 `catchError` const re1



{- |

Γ ⊢ e ⇐ A ~> E
----------------------
Γ ⊢{l=e} ⇐ {l:A} ~> E

-}

tcheck (DRec l e _) (SRecT l' a) = do
  when (l /= l') $
    errThrow [DS $ "Labels not equal" <+> Pretty.pretty l <+> "and" <+> Pretty.pretty l']
  tcheck e a


tcheck (Pos p tm) ty = extendSourceLocation p tm $ tcheck tm ty


{- |

Γ ⊢ e ⇒ A ~> E
A <: B ~> c
Γ ⊢ B
-------------------
Γ ⊢ e ⇐ B ~> c E

-}

tcheck e b = checkMode e b

-- fields :: SType -> Map Label [SType]
-- fields (SRecT l ty) = M.fromList [(l,[ty])]
-- fields (And ty1 ty2) = M.unionWith (++) (fields ty1) (fields ty2)
-- fields ty = M.empty

-- fieldType :: SType -> Label -> [SType]
-- fieldType ty l = fromMaybe [] (M.lookup l (fields ty))

checkMode :: Expr -> SType -> TcMonad T.UExpr
checkMode e b = do
  wf b
  (a, e') <- infer e
  ctx <- askCtx
  let res = subtype ctx a b
  case res of
    Right c -> return (T.UApp c e')
    Left er -> errThrow [DS $ "Subtyping failed in checkmode:" <+> er, DD e, DD a, DD b]


-- | Check that a (expanded) type is well-formed
wf :: SType -> TcMonad ()
wf ty = do
  ctx <- askCtx
  let t' = expandType ctx ty
  maybe_kind <- kind ctx t'
  case maybe_kind of
    Nothing ->
      errThrow [DS $ Pretty.squotes (pprint ty) <+> "is not well-kinded", DD t']
    Just Star -> go t'
    Just k ->
      errThrow
        [ DS
            (Pretty.hang 2 $
             "expect type" <+>
             Pretty.squotes (pprint ty) <+>
             "has kind star" <> Pretty.line <> "but got" <+>
             Pretty.squotes (pprint k))
        ]
  where
    go NumT = return ()
    go BoolT = return ()
    go StringT = return ()
    go (Arr a b) = go a >> go b
    go (And a b) = do
      go a
      go b
    go (TVar x) = void $ lookupTVarConstraint x
    go (DForall t) = do
      ((x, Embed a), b) <- unbind t
      go a
      localCtx (extendConstrainedTVarCtx x a) $ go b
    go (SRecT _ t) = go t
    go TopT = return ()
    go BotT = return ()
    go (TraitT a b) = go a >> go b
    go (ListT t) = go t
    go t = errThrow [DS $ "type" <+> Pretty.squotes (pprint t) <+> "is not well-formed"]


{-

WARN: This is the most critical component!!!

Anything new added in the types, we should double check how it
affects the disjointess relation

-}


topLike :: Fresh m => SType -> m Bool
topLike TopT = return True
topLike (And a b) = (&&) <$> (topLike a) <*> (topLike b)
topLike (Arr a b) = topLike b
topLike (SRecT _ t) = topLike t
topLike (DForall b) = do
  ((_, _), t) <- unbind b
  topLike t
topLike (TraitT a b) = topLike b
topLike _ = return False

disjoint :: Ctx -> SType -> SType -> TcMonad ()
disjoint _ TopT _ = return ()
disjoint _ _ TopT = return ()

disjoint _ BotT a = do
  isTop <- topLike a
  if isTop
    then return ()
    else errThrow
           [ DS $
             "Bottom is only disjoint to top-like types, but" <+>
             Pretty.squotes (pprint a) <+> "is not top-like"
           ]
disjoint _ a BotT = do
  isTop <- topLike a
  if isTop
    then return ()
    else errThrow
           [ DS $
             "Bottom is only disjoint to top-like types, but" <+>
             Pretty.squotes (pprint a) <+> "is not top-like"
           ]

disjoint ctx (TVar x) b
  | Just a <- lookupTVarConstraintMaybe ctx x
  , Right _ <- subtype ctx a b = return ()
disjoint ctx b (TVar x)
  | Just a <- lookupTVarConstraintMaybe ctx x
  , Right _ <- subtype ctx a b = return ()
disjoint _ (TVar x) (TVar y) =
  errThrow
    [ DS $
      "SType variables" <+>
      Pretty.pretty x <+> "and" <+> Pretty.pretty y <+> "are not disjoint"
    ]

disjoint ctx (DForall t) (DForall t') =
  unbind2 t t' >>= \case
    Just ((x, Embed a1), b, (_, Embed a2), c) ->
      disjoint (extendConstrainedTVarCtx x (And a1 a2) ctx) b c
    _ -> errThrow [DS "Patterns have different binding variables"]

disjoint ctx tm1@(SRecT l a) tm2@(SRecT l' b) =
  when (l == l') $
  disjoint ctx a b `catchError`
  const
    (errThrow
       [ DS $
         Pretty.squotes (pprint tm1) <+>
         "and" <+> Pretty.squotes (pprint tm2) <+> "are not disjoint"
       ])

disjoint ctx (Arr _ a2) (Arr _ b2) = disjoint ctx a2 b2
disjoint ctx (And a1 a2) b = do
  disjoint ctx a1 b
  disjoint ctx a2 b
disjoint ctx a (And b1 b2) = do
  disjoint ctx a b1
  disjoint ctx a b2
disjoint ctx (TraitT _ a) (TraitT _ b) = disjoint ctx a b
disjoint ctx (TraitT _ a) (Arr _ b) = disjoint ctx a b
disjoint ctx (Arr _ a) (TraitT _ b) = disjoint ctx a b
disjoint _ a b =
  unless (disjointAx a b) $
  errThrow
    [ DS $
      Pretty.squotes (pprint a) <+>
      "and" <+> Pretty.squotes (pprint b) <+> "are not disjoint"
    ]


disjointAx :: SType -> SType -> Bool
disjointAx t1 t2 =
  type2num t1 < 6 && type2num t2 < 6 && type2num t1 /= type2num t2
  where
    type2num :: SType -> Int
    type2num NumT = 0
    type2num BoolT = 1
    type2num StringT = 2
    type2num Arr {} = 3
    type2num DForall {} = 4
    type2num SRecT {} = 5
    -- The above are basic type
    type2num TopT {} = 6
    type2num And {} = 7
    type2num TVar {} = 8
    type2num OpAbs {} = 9
    type2num OpApp {} = 10
    type2num BotT {} = 11
    type2num TraitT {} = 12
    type2num ListT {} = 13





--------------------
-- τ1 • l = τ2  ~> C
--------------------

-- | Select a label l from t
-- Return a list of possible types with their projections
select :: SType -> Label -> [(SType, T.UExpr)]
select t l =
  fromMaybe [] (M.lookup l m)
  where
    m = recordFields t

recordFields :: SType -> Map Label [(SType, T.UExpr)]
recordFields = go identity
  where
    go :: (T.UExpr -> T.UExpr) -> SType -> Map Label [(SType, T.UExpr)]
    go cont (And t1 t2) =
      M.unionWith (++) (go (T.UP1 . cont) t1) (go (T.UP2 . cont) t2)
    go cont (SRecT l' t') =
      M.fromList [(l', [(t', T.elam "x" (cont (T.evar "x")))])]
    go _ _ = M.empty

----------------------
-- τ1 \ l = τ2 ~> C
----------------------

restrict2 :: SType -> Label -> Maybe SType -> Maybe SType
restrict2 t l lt = go t
  where
    go (TraitT t1 t2) =
      fmap (\tt -> TraitT t1 tt) (go t2)
    go (SRecT l' t') = if l == l' && maybe True (`aeq` t') lt then Just TopT else Nothing
    go (And t1 t2) =
      let m1 = go t1
          m2 = go t2
          m1' = fmap (\tt -> And tt t2) m1
          m2' = fmap (\tt -> And t1 tt) m2
      in m1' <|> m2'
    go _ = Nothing
--TODO: define a beautify function that removes all Tops from an And type

restrict :: SType -> Label -> Maybe SType -> Maybe (SType, T.UExpr)
restrict t l lt = go t
  where
    go (SRecT l' t') = if l == l' && maybe True (`aeq` t') lt then Just (TopT, T.elam "x" T.UUnit) else Nothing
    go (And t1 t2) =
      let m1 = go t1
          m2 = go t2
          m1' = fmap (\(tt, c) -> (And tt t2, T.elam "x" (T.UPair (T.UApp c (T.UP1 (T.evar "x"))) (T.UP2 (T.evar "x"))))) m1
          m2' = fmap (\(tt, c) -> (And t1 tt, T.elam "x" (T.UPair (T.UP1 (T.evar "x")) (T.UApp c (T.UP2 (T.evar "x")))))) m2
      in m1' <|> m2'
    go _ = Nothing

extendCtxRcd :: SType -> Ctx -> Ctx
extendCtxRcd ty ctx =
  M.foldrWithKey (\l xs c -> extendVarCtx (s2n l) (foldr1 And $ map fst xs) c) ctx (recordFields ty)

collectOverrides :: Expr -> [Label]
collectOverrides (Pos _ e) = collectOverrides e
collectOverrides (Open _ e) = collectOverrides e
collectOverrides (Merge e1 e2) = collectOverrides e1 ++ collectOverrides e2
collectOverrides (DRec n _ True) = [n]
collectOverrides e = []

tcOverrides :: SType -> [Label] -> TcMonad SType
tcOverrides ty ls = do
  foldM (\t l -> do
      case restrict2 t l Nothing of
        Just t' -> return t'
        Nothing -> errThrow [DS "override nothing"]) ty ls

fillType :: SType -> Expr -> TcMonad Expr
fillType (Arr t1 t2) (Lam b) = do
  (x,e) <- unbind b
  e' <- fillType t2 e
  return $ LamA (bind (x,embed t1) e')
fillType _ e = return e


translateType :: SType -> TcMonad SType
translateType ty =
  do
    ctx <- askCtx
    go $ expandType ctx ty
  where
    go (TraitT a b) = do
      a' <- go a
      b' <- go b
      return $ Arr a' b'
    go (Arr a b) = do
      a' <- go a
      b' <- go b
      return $ Arr a' b'
    go (And a b) = do
      a' <- go a
      b' <- go b
      return $ And a' b'
    go (SRecT l a) = do
      a' <- go a
      return $ SRecT l a'
    go (DForall t) = do
      ((x, Embed b), a) <- unbind t
      b' <- go b
      a' <- go a
      return $ DForall (bind (x, embed b') a')
    go a = return a
