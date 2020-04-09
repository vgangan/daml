-- Copyright (c) 2020 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
-- SPDX-License-Identifier: Apache-2.0

module DA.Daml.LF.Evaluator.Exp
  ( Exp(..), Alt(..), Var, Prog(..), Defs, DefKey(..), FieldName,
  ) where

import qualified DA.Daml.LF.Ast as LF
import DA.Daml.LF.Evaluator.Value(Value,FieldName,Tag)
import Data.Map.Strict (Map)

data Exp
  = Lit Value
  | Var Var
  | App Exp Exp
  | Lam Var Exp
  | Let Var Exp Exp
  | Rec [(FieldName,Exp)]
  | Dot Exp FieldName
  | Con Tag [Exp]
  | Match { scrut :: Exp, alts :: [Alt] }
  | Ref Int
  | Located Exp
  deriving (Show)

type Var = LF.ExprVarName

data Alt = Alt {tag :: Tag, bound :: [Var], rhs :: Exp}
  deriving (Show)

data Prog = Prog { defs :: Defs, main :: Exp }
  deriving (Show)

type Defs = Map Int (DefKey,Exp)

newtype DefKey = DefKey (LF.PackageId, LF.ModuleName, LF.ExprValName)
  deriving (Eq,Ord,Show)

