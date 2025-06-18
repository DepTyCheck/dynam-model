module Dynam.Pretty.Base.Utils

import Dynam.Model.Base

import Data.List
import public Data.So
import Data.DPair

public export
data UniqNames : (funs : ListOfFunctions) -> (vars : ListOfBasicTypes) -> Type
public export
data NameIsNew : (funs : ListOfFunctions) ->
                 (vars : ListOfBasicTypes) ->
                 UniqNames funs vars ->
                 String -> Type

public export
data UniqNames : (funs : ListOfFunctions) -> (vars : ListOfBasicTypes) -> Type where
    [search funs vars]
    Empty   : UniqNames [] []
    JustNew : (prevNames : UniqNames funs vars) =>
              (newName : String) ->
              (0 _ : NameIsNew funs vars prevNames newName) =>
              UniqNames funs vars
    NewFun  : (prevNames : UniqNames funs vars) =>
              (newName : String) ->
              (0 _ : NameIsNew funs vars prevNames newName) =>
              {default False isInfix : Bool} ->
            --   {default False isPure : Bool} ->
              UniqNames (fun :: funs) vars
    NewVar  : (prevNames : UniqNames funs vars) =>
              (newName : String) ->
              (0 _ : NameIsNew funs vars prevNames newName) =>
              UniqNames funs ((::) var vars)

public export
data NameIsNew : (funs : ListOfFunctions) -> (vars : ListOfBasicTypes) -> UniqNames funs vars -> String -> Type where
    E : NameIsNew [] [] Empty curr

    J : (0 _ : So $ curr /= newName) -> NameIsNew funs vars prevNames curr ->
        NameIsNew funs vars (JustNew @{prevNames} newName @{sub}) curr

    F : (0 _ : So $ curr /= newName) -> NameIsNew funs vars prevNames curr ->
        NameIsNew (fun :: funs) vars (NewFun @{prevNames} {isInfix} newName @{sub}) curr

    V : (0 _ : So $ curr /= newName) -> NameIsNew funs vars prevNames curr ->
        NameIsNew funs (var :: vars) (NewVar @{prevNames} newName @{sub}) curr


public export
genVarName : UniqNames funs vars -> IndexIn vars -> String
genVarName (JustNew @{ss} _) i         = genVarName ss i
genVarName (NewFun @{ss} _)  i         = genVarName ss i
genVarName (NewVar @{ss} _)  (There i) = genVarName ss i
genVarName (NewVar s)        Here      = s

public export
genFunName : UniqNames funs vars -> IndexIn funs -> String
genFunName (JustNew @{ss} _) i         = genFunName ss i
genFunName (NewFun s)        Here      = s
genFunName (NewFun @{ss} _)  (There i) = genFunName ss i
genFunName (NewVar @{ss} _)  i         = genFunName ss i

public export
isFunInfix : UniqNames funs vars -> IndexIn funs -> Bool
isFunInfix (JustNew @{ss} _)    i         = isFunInfix ss i
isFunInfix (NewFun {isInfix} _) Here      = isInfix
isFunInfix (NewFun @{ss} s)     (There i) = isFunInfix ss i
isFunInfix (NewVar @{ss} s)     i         = isFunInfix ss i

public export
getExprs : ExprList casts funs vars argTys -> List $ Exists $ Expr casts funs vars
getExprs [] = []
getExprs (x :: xs) = Evidence _ x :: getExprs xs


||| See AddCast (Runner)
public export
data CastMock : Type where
  Mock : CastMock

public export
toList : ListOfBasicTypes -> List BasicType
toList Nil = Nil
toList (x :: xs) = x :: (toList xs)
