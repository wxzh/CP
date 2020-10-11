{-# LANGUAGE DeriveGeneric, MultiParamTypeClasses, NoImplicitPrelude #-}

module CP.Common where

import Unbound.Generics.LocallyNameless
import Protolude


data Operation = Arith ArithOp
               | Comp CompOp
               | Logical LogicalOp
               | Append AppendTy
               | At
               deriving (Eq, Show, Generic)


data ArithOp = Add | Sub | Mul | Div deriving (Eq, Show, Generic)

data CompOp = Lt | Gt | Equ | Neq deriving (Eq, Show, Generic)

data LogicalOp =  LAnd | LOr deriving (Eq, Show, Generic)

data AppendTy = Unknown | Str | Lst deriving (Eq, Show, Generic)

instance Alpha ArithOp
instance Alpha LogicalOp
instance Alpha Operation
instance Alpha CompOp
instance Alpha AppendTy
