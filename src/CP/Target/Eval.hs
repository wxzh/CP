{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecursiveDo #-}

module CP.Target.Eval (evaluate) where

import           Control.Monad.Except
import           Data.IORef
import qualified Data.Map.Strict as M
import           Unbound.Generics.LocallyNameless

import           CP.Target.Syntax
import           CP.Common

-- call-by-need environment
type Env = M.Map UName Thunk

type EvalM a = FreshMT (ExceptT String IO) a

newtype Thunk = Thunk { force :: EvalM Value }

instance Show Thunk where
  show _ = "<Thunk>"

mkThunk :: EvalM Value -> EvalM Thunk
mkThunk ev = do
  ref <- liftIO $ newIORef Nothing
  return $
    Thunk $ do
      mv <- liftIO $ readIORef ref
      case mv of
        Nothing -> do
          v <- ev
          liftIO $ writeIORef ref (Just v)
          return v
        Just v -> return v



data Value
  = VLit !Double
  | VBool !Bool
  | VStr !String
  | VPair !Thunk !Thunk
  | VUnit
  | VLam !(Thunk -> EvalM Value)
  | VList ![Thunk]

instance Show Value where
  show (VLit n) = show n
  show (VBool True) = "true"
  show (VBool False) = "false"
  show (VPair _ _) = "<Pair>"
  show VUnit = "()"
  show (VStr s) = show s
  show (VLam _) = "<Lambda>"
  show (VList _) = "<List>"


runEvalM :: EvalM a -> IO (Either String a)
runEvalM = runExceptT . runFreshMT


evaluate :: UExpr -> IO (Either String Value)
evaluate e = runEvalM (eval M.empty e)

-- | Lazy evaluation
eval :: Env -> UExpr -> EvalM Value
eval env (UVar n) = lookupValue env n >>= force
eval env (UApp f x) = do
  f' <- eval env f
  x' <- mkThunk (eval env x)
  evalApp f' x'
eval env (ULam b) = do
  (n, e) <- unbind b
  return $ VLam $ \x -> eval (M.insert n x env) e
eval env (ULet b) = mdo
  (n, (e1, e2)) <- unbind b
  e1' <- mkThunk (eval (M.insert n e1' env) e1)
  eval (M.insert n e1' env) e2
eval env (UPair e1 e2) = do
  e1' <- mkThunk (eval env e1)
  e2' <- mkThunk (eval env e2)
  return $ VPair e1' e2'
eval env (UP1 e) = do
  e' <- eval env e
  evalP1 e'
eval env (UP2 e) = do
  e' <- eval env e
  evalP2 e'
eval _ (ULitV n) = return (VLit n)
eval _ (UBoolV n) = return (VBool n)
eval _ (UStrV n) = return (VStr n)
eval _ UUnit = return VUnit
eval env (UPrimOp op e1 e2) = do
  e1' <- eval env e1
  e2' <- eval env e2
  evalOp op e1' e2'
eval env (UIf e1 e2 e3) = do
  e1' <- eval env e1
  case e1' of
    VBool b ->
      if b
        then eval env e2
        else eval env e3
    v -> throwError $ "Expected a Boolean, but got: " ++ show v
eval env (UToString e) = do
  e' <- eval env e
  return (VStr (show e'))
eval env (USqrt e) = do
  e' <- eval env e
  case e' of
    VLit n -> return $ VLit (sqrt n)
    v -> throwError $ "Expected a number, but got: " ++ show v
eval env (UListNew n f) = do
  n' <- eval env n
  case n' of
    VLit 0 -> return $ VList []
    VLit len -> do
      f' <- eval env f
      list <- app f' (truncate len)
      return $ VList list
    v -> throwError $ "Expected a number, but got: " ++ show v
  where
    app :: Value -> Int -> EvalM [Thunk]
    app _ 0 = return []
    app fn i = do
      arg <- mkThunk . return $ VLit (fromIntegral i - 1)
      ret <- mkThunk $ evalApp fn arg
      list <- app fn (i - 1)
      return $ list ++ [ret]
eval env (UListLength l) = do
  l' <- eval env l
  let VList list = l'
  return $ VLit (fromIntegral $ length list)
eval env (UListSum l) = do
  l' <- eval env l
  let VList list = l'
  s <- foldl plus (return 0) list
  return $ VLit s
  where
    plus x y = do
      total <- x
      value <- force y
      let VLit num = value
      return $ total + num
eval env (UListScanl l) = do
  l' <- eval env l
  let VList list = l'
  cum <- scan list 0
  return $ VList cum
  where
    scan :: [Thunk] -> Double -> EvalM [Thunk]
    scan [] _ = return $ []
    scan (x:xs) s = do
      x' <- force x
      let VLit n = x'
      thunk <- mkThunk . return $ VLit (s + n)
      list <- scan xs (s + n)
      return $ thunk : list
eval env (UListLzw f l1 l2) = do
  f' <- eval env f
  l1' <- eval env l1
  let VList list1 = l1'
  l2' <- eval env l2
  let VList list2 = l2'
  list <- lzw f' list1 list2
  return $ VList list
  where
    lzw :: Value -> [Thunk] -> [Thunk] -> EvalM [Thunk]
    lzw _ [] ys = return ys
    lzw _ xs [] = return xs
    lzw fun (x:xs) (y:ys) = do
      curried <- evalApp fun x
      z <- mkThunk $ evalApp curried y
      list <- lzw fun xs ys
      return $ z : list
eval _ Bot = throwError "Damn it, it's an infinite loop!"



evalApp :: Value -> Thunk -> EvalM Value
evalApp (VLam f) t  = f t
evalApp v _ = throwError $ "Expected a function, but got: " ++ show v


evalP1 :: Value -> EvalM Value
evalP1 (VPair v1 _)   = force v1
evalP1 v = throwError $ "Expected a pair, but got: " ++ show v


evalP2 :: Value -> EvalM Value
evalP2 (VPair _ v2)   = force v2
evalP2 v = throwError $ "Expected a pair, but got: " ++ show v

evalOp :: Operation -> Value -> Value -> EvalM Value
evalOp (Arith Add) (VLit x) (VLit y) = return $ VLit $ x + y
evalOp (Arith Sub) (VLit x) (VLit y) = return $ VLit $ x - y
evalOp (Arith Mul) (VLit x) (VLit y) = return $ VLit $ x * y
evalOp (Arith Div) (VLit x) (VLit y) = return $ VLit $ x / y
evalOp (Comp Equ) (VLit x) (VLit y) = return $ VBool $ x == y
evalOp (Comp Equ) (VStr x) (VStr y) = return $ VBool $ x == y
evalOp (Comp Equ) (VBool x) (VBool y) = return $ VBool $ x == y
evalOp (Comp Lt) (VLit x) (VLit y) = return $ VBool $ x < y
evalOp (Comp Gt) (VLit x) (VLit y) = return $ VBool $ x > y
evalOp (Comp Neq) (VLit x) (VLit y) = return $ VBool $ x /= y
evalOp (Comp Neq) (VStr x) (VStr y) = return $ VBool $ x /= y
evalOp (Comp Neq) (VBool x) (VBool y) = return $ VBool $ x /= y
evalOp (Logical LAnd) (VBool x) (VBool y) = return $ VBool $ x && y
evalOp (Logical LOr) (VBool x) (VBool y) = return $ VBool $ x || y
evalOp (Append Str) (VStr x) (VStr y) = return $ VStr $ x ++ y
evalOp (Append Lst) (VList x) (VList y) = return $ VList $ x ++ y
evalOp At (VList x) (VLit y) = force $ x !! truncate y
evalOp _ _ _ = throwError "Impossible happened in evalOp"

lookupValue :: Env -> UName -> EvalM Thunk
lookupValue env n = maybe err return $ M.lookup n env
  where
    err = throwError $ "Not found: " ++ show (name2String n)
