-- Copyright (c) 2020 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
-- SPDX-License-Identifier: Apache-2.0

{-# LANGUAGE GADTs #-}

module DA.Daml.LF.Optimize
  ( World(..), optimizeWorld, optimize
  ) where

import Control.Monad (ap,liftM,forM)
import Data.Map.Strict (Map)
import Data.Set (Set)
import qualified DA.Daml.LF.Ast as LF
import qualified Data.Map.Strict as Map
import qualified Data.NameMap as NM
import qualified Data.Set as Set
import qualified Data.Text as Text


optimizeWorld :: World -> IO World
optimizeWorld world = do
  let World {mainId,packageMap} = world
  let mainPkg =
        case Map.lookup mainId packageMap of
          Just v -> v
          Nothing -> error $ "lookup mainId failed, " <> show mainId
  -- we only optimize (and replace) the main package here
  mainPkgO <- optimize world mainPkg
  let otherPairs = [ (pid,pkg) | (pid,pkg) <- Map.toList packageMap, pid /= mainId ]
  let packageMapO = Map.fromList $ (mainId,mainPkgO) : otherPairs
  return World{mainId,packageMap = packageMapO}


optimize :: World -> LF.Package -> IO LF.Package
optimize world pkg =
  run world $ normPackage pkg


data World = World
  { mainId :: LF.PackageId
  , packageMap :: Map LF.PackageId LF.Package
  }

type Exp = LF.Expr
type Alt = LF.CaseAlternative
type FieldName = LF.FieldName

-- hmm, not great to use these as set items because the qualPackage can be implicit(Self) or explicit
-- would be better to normalise these first
type QVal = LF.Qualified LF.ExprValName

type Var = LF.ExprVarName
type Env = Map Var Norm


normPackage :: LF.Package -> Effect LF.Package
normPackage pkg = do
  let LF.Package{packageModules} = pkg
  packageModules <- NM.traverse normModule packageModules
  return $ pkg {LF.packageModules}

normModule :: LF.Module -> Effect LF.Module
normModule mod = do
  let LF.Module{moduleName,moduleValues} = mod -- TODO: also traverse over templates?
  moduleValues <- NM.traverse (normDef moduleName) moduleValues
  return mod {LF.moduleValues}

normDef :: LF.ModuleName -> LF.DefValue -> Effect LF.DefValue
normDef moduleName dval = do
  let LF.DefValue{dvalBinder=(name,_),dvalBody=expr} = dval
  let qval = LF.Qualified{qualPackage=LF.PRSelf, qualModule=moduleName, qualObject=name}
  expr <- (WithDontInline qval $ norm expr) >>= reify "DEF"
  return dval {LF.dvalBody=expr}


explicateSelfPid :: QVal -> Effect QVal
explicateSelfPid qval = do
  let LF.Qualified{qualPackage=pref, qualModule=moduleName, qualObject=name} = qval
  pid <- case pref of
    LF.PRSelf -> GetPid
    LF.PRImport pid -> return pid
  let pref = LF.PRImport pid
  return $ LF.Qualified{qualPackage=pref, qualModule=moduleName, qualObject=name}

normQualifiedExprValName :: QVal -> Effect Norm
normQualifiedExprValName qval = do
  let LF.Qualified{qualPackage=pref, qualModule=moduleName, qualObject=name} = qval
  pid <- case pref of
    LF.PRSelf -> GetPid
    LF.PRImport pid -> return pid
  WithPid pid $ do
    expr <- getExprValName pid moduleName name
    norm expr

getExprValName :: LF.PackageId -> LF.ModuleName -> LF.ExprValName -> Effect Exp
getExprValName pid moduleName name = do
  mod <- getModule pid moduleName
  let LF.Module{moduleValues} = mod
  case NM.lookup name moduleValues of
    Nothing -> error $ "simpExprValName, " <> show name
    Just dval -> do
      let LF.DefValue{dvalBody=expr} = dval
      return expr

getModule :: LF.PackageId -> LF.ModuleName -> Effect LF.Module
getModule pid moduleName = do
  package <- GetPackage pid
  let LF.Package{packageModules} = package
  case NM.lookup moduleName packageModules of
    Nothing -> error $ "getModule, " <> show (pid,moduleName)
    Just mod -> return mod


norm :: Exp -> Effect Norm
norm = \case

  LF.EVar name -> do
    env <- GetEnv
    case Map.lookup name env of
      Just v -> return v
      Nothing ->
        -- TODO: We ought to be able to error here.
        -- When normalizing under lambda, we should always rename vars (and add them to the env)
        -- and then we can this error should be ok.
        --error $ "norm, " <> show name
        return $ Syntax $ LF.EVar name

  LF.EVal qval -> do
    ShouldInline qval >>= \case
      True -> do
        WithDontInline qval $
          normQualifiedExprValName qval
      False -> do
        qval <- explicateSelfPid qval
        return $ Syntax $ LF.EVal qval

  x@LF.EBuiltin{} -> return $ Syntax x

  LF.ERecCon{recTypeCon,recFields} -> do
    recFields <- forM recFields $ \(fieldName,expr) -> do
      expr <- norm expr >>= reify "RC"
      return (fieldName,expr)
    return $ Syntax $ LF.ERecCon{recTypeCon,recFields} -- TODO: be special here? (like structs)

  LF.ERecProj{recTypeCon,recField=fieldName,recExpr=expr} -> do
    expr <- norm expr >>= reify "RP"
    return $ Syntax $ LF.ERecProj{recTypeCon,recField=fieldName,recExpr=expr} -- TODO: be special here

  LF.ERecUpd{recTypeCon,recField,recExpr=e,recUpdate=u} -> do
    e <- norm e >>= reify "RE"
    u <- norm u >>= reify "RU"
    return $ Syntax $ LF.ERecUpd{recTypeCon,recField,recExpr=e,recUpdate=u}

  LF.EVariantCon{varTypeCon,varVariant,varArg=expr} -> do
    expr <- norm expr >>= reify "VC"
    return $ Syntax $ LF.EVariantCon{varTypeCon,varVariant,varArg=expr}

  x@LF.EEnumCon{} -> return $ Syntax x

  LF.EStructCon{structFields} -> do
    rp <- Save
    structFields <- forM structFields $ \(fieldName,expr) -> do
      expr <- norm expr -- >>= reify
      return (fieldName,expr)
    --return $ Syntax $ LF.EStructCon{structFields} -- not special
    return $ Struct rp structFields -- be special

  LF.EStructProj{structField=field,structExpr=expr} -> do
    expr <- norm expr -- >>= reify
    --return $ Syntax $ LF.EStructProj{structField=field,structExpr=expr} -- not special
    normProjectStruct field expr -- be special

  LF.EStructUpd{} -> undefined

  LF.ETmApp{tmappFun=e1,tmappArg=e2} -> do
    v1 <- norm e1
    v2 <- norm e2
    apply (v1,v2) -- be special

  LF.ETyApp{tyappExpr=expr,tyappType=_ty} -> do
    -- TEMP IGNORE/DROP type-apps...
    --expr <- norm expr >>= reify "TA"
    --return $ Syntax $ LF.ETyApp{tyappExpr=expr,tyappType=_ty}
    norm expr

  LF.ETmLam{tmlamBinder=binder,tmlamBody=body} -> do
    let (name,_typ) = binder
    rp <- Save
    return $ Macro $ \arg -> -- be special
      Restore rp $
      ModEnv (Map.insert name arg) $ norm body

  LF.ETyLam{tylamBinder=_ty, tylamBody=expr} -> do
    -- Think Type lambdas are blocking normalization. Just drop them for now!
    -- TODO: will need to add as a variant to Norm
    -- expr <- norm expr >>= reify "TL"
    -- return $ Syntax $ LF.ETyLam{tylamBinder=_ty, tylamBody=expr}
    norm expr

  LF.ECase{casScrutinee=expr, casAlternatives=alts} -> do
    -- TODO: special handling here?...
    expr <- norm expr >>= reify "CASE"
    alts <- mapM normAlt alts
    return $ Syntax $ LF.ECase{casScrutinee=expr, casAlternatives=alts}

  LF.ELet{letBinding=bind,letBody=expr} -> do
    -- TODO: special handling? inline the let? (see old code)
    bind <- normBinding bind
    expr <- norm expr >>= reify "LET"
    return $ Syntax $ LF.ELet{letBinding=bind,letBody=expr}

  x@LF.ENil{} -> return $ Syntax x

  LF.ECons{consType,consHead=h,consTail=t} -> do
    h <- norm h >>= reify "CH"
    t <- norm t >>= reify "CT"
    return $ Syntax $ LF.ECons{consType,consHead=h,consTail=t}

  LF.ESome{someType,someBody=expr} -> do
    expr <- norm expr >>= reify "SOME"
    return $ Syntax $ LF.ESome{someType,someBody=expr}

  x@LF.ENone{} -> return $ Syntax x

  LF.EToAny{} -> undefined
  LF.EFromAny{} -> undefined
  LF.ETypeRep{} -> undefined

  -- TODO: we must traverse deeply on any structure which contains nested expressions
  -- this is because any free vars must be converted via the env
  -- free vars can occur because we do normalization under lambdas
  -- and when we go under a lambda, vars get uniquely renamed
  -- actually for simple lambdas, we normalize to a Macro which can get multiply-applied
  -- and in this case the var can get renamed into multiple fresh instances

  x@LF.EUpdate{} -> return $ Syntax x -- TODO: traverse deeply
  x@LF.EScenario{} -> return $ Syntax x -- TODO: traverse deeply

  -- TODO: to preserve location info we need a new variant for `Norm` expressions
  LF.ELocation _loc expr -> do
    norm expr


normBinding :: LF.Binding -> Effect LF.Binding
normBinding = \case
  LF.Binding{bindingBinder,bindingBound=rhs} -> do
    rhs <- norm rhs >>= reify "RHS"
    return $ LF.Binding{bindingBinder,bindingBound=rhs}


normAlt :: Alt -> Effect Alt
normAlt = \case
  LF.CaseAlternative{altPattern=pat,altExpr=expr} -> do
    expr <- norm expr >>= reify "ALT"
    return $ LF.CaseAlternative{altPattern=pat,altExpr=expr}

{-
normAlt = \case
  Exp.Alt{tag,bound,rhs} -> do
    nameMapping <- do
      forM bound $ \x -> do
        y <- Fresh
        return (x,y)
    let bound = map snd nameMapping
    let f env = foldr (\(x,y) -> Map.insert x (Syntax $ Exp.Var y)) env nameMapping
    rhs <- ModEnv f $ norm rhs >>= reify
    return $ Exp.Alt{tag,bound,rhs}
-}

data Norm -- Normalized Expression
  = Syntax Exp
  | Struct RestorePoint [(FieldName,Norm)]
  | Macro (Norm -> Effect Norm)


apply :: (Norm,Norm) -> Effect Norm
apply = \case
  (Syntax func, arg) -> do
    arg <- reify "UNKNOWN_FUNC" arg
    return $ Syntax $ LF.ETmApp{tmappFun=func,tmappArg=arg}
  (Struct _ _, _) -> error "Norm,apply,struct"
  (Macro func, arg) -> do
    let doInline = duplicatable arg
    if doInline
    then func arg
    else do -- never called at the moment
      name <- Fresh "_gg"
      rhs <- reify "SHARE_ARG" arg
      body <- func (Syntax (LF.EVar name)) >>= reify "SHARE_BODY"
      let typ = undefined -- TODO: comes from where?
      let bind = LF.Binding{bindingBinder=(name,typ),bindingBound=rhs}
      return $ Syntax $ LF.ELet{letBinding=bind,letBody=body}


-- A normalized-expression can be duplicated if it has no computation effect
duplicatable :: Norm -> Bool
duplicatable = \case
  -- TODO: for Record, we should only consider is duplicatable, if all fields are
  Struct{} -> True
  Macro{} -> True
  Syntax exp -> case exp of
    LF.EBuiltin{} -> True
    LF.EVar{} -> True
    _ -> False


-- every call to `reify` is a barrier to normalization
reify :: String -> Norm -> Effect Exp
reify tag = \case
  Syntax exp -> return exp

  Struct rp xs -> do
    Restore rp $ do
      structFields <- forM xs $ \(name,n) -> do
        exp <- reify "STRUCT_FIELD" n
        return (name,exp)
      return $ LF.EStructCon{structFields}

  Macro f -> do
    name <- Fresh $ "_rm" <> tag <> "_"
    body <- f (Syntax (LF.EVar name)) >>= reify "MB"
    let typ = undefined --TODO comes from where?
    return $ LF.ETmLam{tmlamBinder=(name,typ),tmlamBody=body}


normProjectStruct :: FieldName -> Norm -> Effect Norm
normProjectStruct field = \case
  Macro _ -> error "normProjectStruct,Macro" -- badly typed
  Syntax expr -> return $ Syntax $ LF.EStructProj{structField=field,structExpr=expr}
  Struct _ xs -> do -- TODO: dont loose restire-point
    case lookup field xs of
      Nothing -> error $ "normProjectStruct, " <> show field -- badly typed
      Just v -> return v -- insert restore-point here. Dont have example which goes wrong yet


data Effect a where
  Ret :: a -> Effect a
  Bind :: Effect a -> (a -> Effect b) -> Effect b
  Save :: Effect RestorePoint
  Restore :: RestorePoint -> Effect a -> Effect a
  GetEnv :: Effect Env
  ModEnv :: (Env -> Env) -> Effect a -> Effect a
  Fresh :: String -> Effect Var
  GetPid :: Effect LF.PackageId
  WithPid :: LF.PackageId -> Effect a -> Effect a
  GetPackage :: LF.PackageId -> Effect LF.Package
  ShouldInline :: QVal -> Effect Bool
  WithDontInline :: QVal -> Effect a -> Effect a


instance Functor Effect where fmap = liftM
instance Applicative Effect where pure = return; (<*>) = ap
instance Monad Effect where return = Ret; (>>=) = Bind


run :: World -> Effect a -> IO a -- Only in IO for debug!
run world eff = do
  (v,_state) <- loop pid0 scope0 env0 state0 eff
  return v

  where
    World{mainId,packageMap} = world

    pid0 = mainId
    scope0 = Set.empty
    env0 = Map.empty
    state0 = State { unique = 0 }

    loop :: LF.PackageId -> InlineScope -> Env -> State -> Effect a -> IO (a,State)
    loop pid scope env state = \case
      Ret x -> return (x,state)
      Bind eff f -> do (v,state') <- loop pid scope env state eff; loop pid scope env state' (f v)

      -- TODO: pid/scope/env -- always travel together? so keep as 1 arg?
      Save -> return (RestorePoint pid scope env, state)
      Restore (RestorePoint pid scope env) eff -> loop pid scope env state eff

      GetEnv -> return (env,state)
      ModEnv f eff -> loop pid scope (f env) state eff

      Fresh _ignored_tag -> do -- take original name as a base which we can uniquify
        let tag = "_g"
        let State{unique} = state
        let state' = state { unique = unique + 1 }
        let x = LF.ExprVarName $ Text.pack (tag <> show unique)
        return (x,state')

      GetPid -> do
        return (pid,state)

      WithPid pid eff -> do
        loop pid scope env state eff

      GetPackage pid -> do
        return (getPackage pid, state)

      ShouldInline qval -> do
        -- TODO : not isDirectlyRecursive -- need to see body
        let answer = not (Set.member qval scope)
        return (answer, state)

      WithDontInline qval eff -> do
        loop pid (Set.insert qval scope) env state eff

    getPackage k =
      case Map.lookup k packageMap of
        Just v -> v
        Nothing -> error $ "getPackage, " <> show k


data RestorePoint = RestorePoint LF.PackageId InlineScope Env

data State = State { unique :: Unique }
type Unique = Int
type InlineScope = Set QVal
