{-# LANGUAGE GADTs, OverloadedStrings, FlexibleContexts, NoImplicitPrelude, RankNTypes #-}

module CP.Environment
  ( lookupVarTy
  , lookupVarTy'
  , lookupTVarConstraint
  , lookupTVarConstraintMaybe
  , lookupTVarSynMaybe
  , lookupTmDef
  , lookupTVarKindMaybe
  , lookupSort
  , runTcMonad
  , TcMonad
  , askCtx
  , localCtx
  , ctxMap
  , extendVarCtx
  , extendTVarCtx
  , extendVarCtxs
  , extendSortCtxs
  , extendConstrainedTVarCtx
  , addTypeSynonym
  , addTypeSynonyms
  , Ctx(..)
  , Err(..)
  , emptyCtx
  , extendSourceLocation
  , errThrow
  ) where


import qualified Data.Map.Strict as M
import           Data.Text.Prettyprint.Doc ((<+>))
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Protolude
import           Text.Megaparsec
import           Unbound.Generics.LocallyNameless

import           CP.Source.Syntax
import           CP.PrettyPrint

type TcMonad = FreshMT (ReaderT Ctx (ExceptT Err IO))


runTcMonad :: Ctx -> TcMonad a -> IO (Either Err a)
runTcMonad env m = runExceptT $ runReaderT (runFreshMT m) env

-- | `TypeValue` is what's put inside a type context.
data TypeValue
  = TerminalType
  -- ^ Terminal types, e.g., the `a` of `forall a. `
  | NonTerminalType SType
    -- ^ Non-terminal types, i.e. type synoyms. `SType` holds the RHS to the
    -- equal sign of type synonym definitions.
  deriving Show

type VarCtx = M.Map TmName SType
type BndCtx = M.Map TmName Expr
type TyCtx = M.Map TyName (Kind, SType, TypeValue)
type SortCtx = [TyName]

-- | Environment manipulation and accessing functions
data Ctx = Ctx
  { varCtx :: VarCtx
  , tyCtx :: TyCtx
  , bndCtx :: BndCtx
  , sortCtx :: SortCtx
  , sourceLocation :: [SourceLocation]
  }

-- instance FPretty Ctx where
--   ppr ctx = foldr (\(k,_,_) acc ->
--                      do
--                        k' <- ppr k
--                        return k' <+> acc
--                   ) Pretty.emptyDoc $ tyCtx ctx
  -- ppr ctx = M.foldrWithKey (\(n,v,doc) -> doc) Pretty.emptyDoc (tyCtx ctx)

askCtx :: TcMonad Ctx
askCtx = ask

localCtx :: (Ctx -> Ctx) -> TcMonad a -> TcMonad a
localCtx = local

emptyCtx :: Ctx
emptyCtx =
  Ctx {varCtx = M.empty, tyCtx = M.empty, bndCtx = M.empty, sortCtx = [], sourceLocation = []}

ctxMap :: (VarCtx -> VarCtx)
      -> (TyCtx -> TyCtx)
      -> (BndCtx -> BndCtx)
      -> (SortCtx -> SortCtx)
      -> Ctx
      -> Ctx
ctxMap f1 f2 f3 f4 ctx =
  Ctx
  { varCtx = f1 (varCtx ctx)
  , tyCtx = f2 (tyCtx ctx)
  , bndCtx = f3 (bndCtx ctx)
  , sortCtx = f4 (sortCtx ctx)
  , sourceLocation = sourceLocation ctx
  }

extendSortCtxs :: [TyName] -> Ctx -> Ctx
extendSortCtxs vs = ctxMap identity identity identity (vs++)

extendVarCtx :: TmName -> SType -> Ctx -> Ctx
extendVarCtx v t = ctxMap (M.insert v t) identity identity identity

extendTVarCtx :: TyName -> Kind -> Ctx -> Ctx
extendTVarCtx v k = ctxMap identity (M.insert v (k, TopT, TerminalType)) identity identity

extendConstrainedTVarCtx :: TyName -> SType -> Ctx -> Ctx
extendConstrainedTVarCtx v t = ctxMap identity (M.insert v (Star, t, TerminalType)) identity identity

extendVarCtxs :: [(TmName, SType)] -> Ctx -> Ctx
extendVarCtxs = flip $ foldr (uncurry extendVarCtx)

addTypeSynonym :: TyName -> SType -> Kind -> Ctx -> Ctx
addTypeSynonym v t k = ctxMap identity (M.insert v (k, t, NonTerminalType t)) identity identity

addTypeSynonyms :: [(TyName, SType, Kind)] -> Ctx -> Ctx
addTypeSynonyms = flip $ foldr (\(v, t, k) ctx -> addTypeSynonym v t k ctx)

lookupSort :: Ctx -> TyName -> Bool
lookupSort ctx v = v `elem` (sortCtx ctx)

lookupVarTy
  :: (MonadReader Ctx m, MonadError Err m)
  => TmName -> m SType
lookupVarTy v = do
  env <- asks varCtx
  case M.lookup v env of
    Nothing -> errThrow [DS $ "Not in scope:" <+> Pretty.pretty v]
    Just res -> return res

lookupVarTy'
  :: (MonadReader Ctx m, MonadError Err m)
  => TmName -> m (Maybe SType)
lookupVarTy' v = M.lookup v <$> asks varCtx

lookupTVarConstraint
  :: (MonadReader Ctx m, MonadError Err m)
  => TyName -> m SType
lookupTVarConstraint v = do
  env <- asks tyCtx
  case M.lookup v env of
    Nothing  -> errThrow [DS $ "Not in scope:" <+> Pretty.pretty v]
    Just (_, c, _) -> return c

lookupTVarKindMaybe :: Ctx -> TyName -> Maybe Kind
lookupTVarKindMaybe ctx v =  (\(k, _, _) -> k) <$> M.lookup v (tyCtx ctx)

lookupTVarConstraintMaybe :: Ctx -> TyName -> Maybe SType
lookupTVarConstraintMaybe ctx v =
  (\(_, t, _) -> t) <$> M.lookup v (tyCtx ctx)

lookupTVarSynMaybe :: Ctx -> TyName -> Maybe SType
lookupTVarSynMaybe ctx v =
  case (\(_, _, t) -> t) <$> M.lookup v (tyCtx ctx) of
    Nothing -> Nothing
    Just TerminalType -> Nothing
    Just (NonTerminalType t) -> Just t

lookupTmDef
  :: (MonadReader Ctx m)
  => TmName -> m (Maybe Expr)
lookupTmDef v = M.lookup v <$> asks bndCtx

-- | Push a new source position on the location stack.
extendSourceLocation ::
     (MonadReader Ctx m, FPretty t) => SourcePos -> t -> m a -> m a
extendSourceLocation p t =
  local (\ e@Ctx {sourceLocation = locs} -> e {sourceLocation = SourceLocation p t:locs})


-- | Marked locations in the source code
data SourceLocation where
  SourceLocation :: forall a. FPretty a => SourcePos -> a -> SourceLocation


-- | An error that should be reported to the user
data Err = Err [SourceLocation] FDoc

instance Semigroup Err where
  (Err src1 d1 ) <> (Err src2 d2) = Err (src1 ++ src2) (d1 <> d2)

instance Monoid Err where
  mempty = Err [] mempty
  mappend = (<>)


instance FPretty Err where
  ppr (Err [] msg) = return msg
  ppr (Err (SourceLocation p term:_) msg) = do
    trm <- ppr term
    return $
      Pretty.vsep [Pretty.pretty p, msg, "In the expression:", trm]


-- | Throw an error
errThrow :: (FPretty a, MonadError Err m, MonadReader Ctx m) => a -> m b
errThrow d = do
  loc <- getSourceLocation
  throwError $ Err loc (pprint d)


-- | access current source location
getSourceLocation :: MonadReader Ctx m => m [SourceLocation]
getSourceLocation = asks sourceLocation
