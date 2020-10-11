{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}


module CP.Source.Desugar
  ( desugar
  , desugarExpr
  , desugarTmBind
  , distinguish
  , normalizeTmDecl
  , expandType
  ) where

import Protolude
import Unbound.Generics.LocallyNameless
import Data.Char (isUpper, isLower)
import Data.List ((!!), foldl1',last)

import CP.Environment
import CP.Source.Syntax
import CP.Util

desugar :: [SDecl] -> [SDecl]
desugar = map go
  where
    go (DefDecl decl) = DefDecl $ desugarTmBind decl
    go x = x

-- output type : for { L : E } or { L : T -> E }, E -> Trait[E,#E] otherwise #E
distinguish :: [Label] -> SType -> SType
distinguish sorts = runFreshM . (go True False)
  where
    go :: Fresh m => Bool -> Bool -> SType -> m SType
    go True t (TVar n)
      | (name2String n) `elem` sorts =
        if t
        then return $ TraitT (TVar n) (TVar $ s2n $ "#" ++ name2String n)
        else return $ TVar $ s2n $ "#" ++ name2String n
    go p c (Arr t1 t2) = do
      t1' <- go (not p) c t1
      t2' <- go p c t2
      return $ Arr t1' t2'
    go p c (TraitT t1 t2) = do
      t1' <- go (not p) c t1
      t2' <- go p c t2
      return $ TraitT t1' t2'
    go p c (And t1 t2) = do
      t1' <- go p c t1
      t2' <- go p c t2
      return $ And t1' t2'
    go p c (SRecT l t) = do
      t' <- go p (isUpper (l !! 0)) t
      return $ SRecT l t'
    go p c (DForall b) = do
      (a, t) <- unbind b
      t' <- go p c t
      return $ DForall (bind a t')
    go _ _ t = return t

desugarTmBind :: TmBind -> TmBind
desugarTmBind b@TmBind{} = b {bindRhs = desugarExpr (bindRhs b)}
desugarTmBind (Pattern l xs Nothing b flag)
  | isLower (l !! 0) = TmBind l [] xs (desugarExpr $ DRec' b) Nothing flag
desugarTmBind (Pattern n xs self b flag) = TmBind n [] xs (desugarExpr $ AnonyTrait (Trait (fromMaybe ("*self", TopT) self) Nothing Nothing (DRec' b))) Nothing flag

isOverride :: TmBind -> Bool
isOverride b@TmBind{}  = bindOverridden b
isOverride b@Pattern{} = patOverridden b

desugarExpr :: Expr -> Expr
desugarExpr = runFreshM . go
  where
    go :: Fresh m => Expr -> m Expr
    -- Interesting cases
    go (DRec' b) =
      let (l, e) = normalizeTmDecl (desugarTmBind b)
      in return $ DRec l e (isOverride b)
    go (AnonyTrait (Trait (name,ty) super implements body)) =
      return $ AnonyTrait $ Trait (name,ty) (map desugarExpr super) implements (Open (evar name) (desugarExpr body))
    -- Routine
    go (Anno e t) = do
      e' <- go e
      return $ Anno e' t
    go (App e1 e2) = do
      e1' <- go e1
      e2' <- go e2
      return $ App e1' e2'
    go (Lam t) = do
      (n, body) <- unbind t
      body' <- go body
      return $ Lam (bind n body')
    go (Letrec t) = do
      ((n, pt), (e, body)) <- unbind t
      bind' <- go e
      body' <- go body
      return $ Letrec (bind (n, pt) (bind', body'))
    go (DLam b) = do
      ((n, t), body) <- unbind b
      body' <- go body
      return $ DLam (bind (n, t) body')
    go (TApp e t) = do
      e' <- go e
      return $ TApp e' t
    go (DRec l e b) = do
      e' <- go e
      return $ DRec l e' b
    go (Acc e l) = do
      e' <- go e
      return $ Acc e' l
    go (Remove e l t) = do
      e' <- go e
      return $ Remove e' l t
    go (Merge e1 e2) = do
      e1' <- go e1
      e2' <- go e2
      return $ Merge e1' e2'
    go (PrimOp op e1 e2) = do
      e1' <- go e1
      e2' <- go e2
      return $ PrimOp op e1' e2'
    go (If e1 e2 e3) = do
      e1' <- go e1
      e2' <- go e2
      e3' <- go e3
      return $ If e1' e2' e3'
    go (LamA b) = do
      ((n, t), body) <- unbind b
      body' <- go body
      return $ LamA (bind (n, t) body')
    go (Pos p e) = do
      e' <- go e
      return (Pos p e')
    go (Open e1 e2) = do
      e1' <- go e1
      e2' <- go e2
      return $ Open e1' e2'
    go (New e) = do
      e' <- go e
      return (New e')
    go (ListNew t n f) = do
      n' <- go n
      f' <- go f
      return (ListNew t n' f')
    go (ListLength l) = go l >>= \l' -> return $ ListLength l'
    go (ListSum l) = go l >>= \l' -> return $ ListSum l'
    go (ListScanl l) = do go l >>= \l' -> return $ ListScanl l'
    go (ListLzw t f l1 l2) = do
      f' <- go f
      l1' <- go l1
      l2' <- go l2
      return (ListLzw t f' l1' l2')
    go e = return e


-- After parsing, earlier declarations appear first in the list
-- Substitute away all type declarations
-- resolveDecls :: [SDecl] -> [TmBind]
-- resolveDecls decls = map (substs substPairs) [decl | (DefDecl decl) <- decls]
--   where
--     tydecls =
--       foldl'
--         (\ds t -> substs (toSubst ds) t : ds)
--         []
--         [decl | decl@TypeDecl {} <- decls]
--     substPairs = toSubst tydecls
--     toSubst ds = [(s2n n, t) | TypeDecl (TypeBind n _ t) <- ds]

{- |


(1): Translate

f [(A, T1), (B, T2)] [(x, A), (y, B)] = e

to

(f, /\ A*T1. B*T2. \x : A .\y : B . e)


(2): Translate

f [(A, T1), (B, T2)] [(x, A), (y, B)] C = e

to

(f, letrec f : forall (A * T1) (B * T2) . A -> B -> C = /\ A*T1. B*T2. \x y . e in f)


-}


normalizeTmDecl :: TmBind -> (RawName, Expr)
normalizeTmDecl decl =
  ( bindName decl
  , maybe ex (\t -> eletr (bindName decl) t ex (evar (bindName decl))) typ)
  where
    (ex, typ) =
      normalize
        (bindTyParams decl)
        (bindParams decl)
        (bindRhs decl)
        (bindRhsTyAscription decl)

{- |

Note: Make sure everything is desugarred before normalizing

Normalize

[(A, T1), (B, T2)] [(x, A), (y, B)] C e

to

\/ A*T1. B*T2. A -> B -> C

and

/\ A*T1. B*T2. \x.\y.e

-}
normalize :: [(TyName, SType)] -> [(TmName, Maybe SType)] -> Expr -> Maybe SType -> (Expr, Maybe SType)
normalize tyParams params e ret = (body, tbody)
  where
    tbody =
      maybe
        Nothing
        (\arr' ->
           Just
             (foldr (\(n, s) tm -> DForall (bind (n, Embed s) tm)) arr' tyParams))
        arr
    arr =
      maybe
        Nothing
        (\t ->
           foldrM
             (\(_, x) y -> maybe Nothing (\x' -> Just $ Arr x' y) x)
             t
             params)
        ret
    body = foldr (\(n, s) tm -> DLam (bind (n, Embed s) tm)) fun tyParams
    fun =
      foldr
        (\(n, t) tm ->
           maybe (Lam (bind n tm)) (\t' -> LamA (bind (n, Embed t') tm)) t)
        (maybe e (Anno e) ret)
        params


-- | Recursively expand all type synonyms. The given type must be well-kinded.
expandType :: Ctx -> SType -> SType
expandType ctx ty = runFreshM (go ctx ty)
  where
    go :: Ctx -> SType -> FreshM SType
    -- Interesting cases:
    go d (TVar a) =
      case lookupTVarSynMaybe d a of
        Nothing -> return $ TVar a
        Just t -> go d t
    go d (OpAbs b) = do
      ((x, Embed k), t) <- unbind b
      t' <- go (extendTVarCtx x k d) t
      return $ OpAbs (bind (x, embed k) t')
    go d typ@(OpApp t1 t2) =
      go d t1 >>= \case
        OpAbs b -> do
          t2' <- go d t2
          ((x, Embed _), t) <- unbind b
          go d (subst x t2' t)
        _ -> return typ
    go _ NumT = return NumT
    go _ BoolT = return BoolT
    go _ StringT = return StringT
    go d (Arr t1 t2) = do
      t1' <- go d t1
      t2' <- go d t2
      return $ Arr t1' t2'
    go d (And t1 t2) = do
      t1' <- go d t1
      t2' <- go d t2
      return $ And t1' t2'
    go d (DForall b) = do
      ((a, Embed t1), t2) <- unbind b
      t1' <- go d t1
      t2' <- go d t2
      return $ DForall (bind (a, embed t1') t2')
    go d (SRecT l t) = do
      t' <- go d t
      return $ SRecT l t'
    go d (TraitT t1 t2) = do
      t1' <- go d t1
      t2' <- go d t2
      return $ TraitT t1' t2'
    go d (OpAppS t1 ts) =
      go d $ foldl OpApp t1 (translateSort d ts)
    go d (ListT t) = do
      t' <- go d t
      return $ ListT t'
    go _ TopT = return TopT
    go _ BotT = return BotT

-- 1. A -> (A, #A) if A is a sort
-- 2. A -> (A, A)
-- 3.(A,B) -> (A & B, B)
translateSort :: Ctx -> [SType] -> [SType]
translateSort ctx [TVar x]
  | lookupSort ctx x = [TVar x, TVar $ s2n $ "#" ++ name2String x]
translateSort _ xs = [foldl1' And xs, last xs]
