module Dynam.Pretty.Utils

import Dynam.Model.Stmts
import Dynam.Model.Primitives

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
varName : UniqNames funs vars -> IndexIn vars -> String
varName (JustNew @{ss} _) i         = varName ss i
varName (NewFun @{ss} _)  i         = varName ss i
varName (NewVar @{ss} _)  (There i) = varName ss i
varName (NewVar s)        Here      = s

public export
funName : UniqNames funs vars -> IndexIn funs -> String
funName (JustNew @{ss} _) i         = funName ss i
funName (NewFun s)        Here      = s
funName (NewFun @{ss} _)  (There i) = funName ss i
funName (NewVar @{ss} _)  i         = funName ss i

public export
isFunInfix : UniqNames funs vars -> IndexIn funs -> Bool
isFunInfix (JustNew @{ss} _)    i         = isFunInfix ss i
isFunInfix (NewFun {isInfix} _) Here      = isInfix
isFunInfix (NewFun @{ss} s)     (There i) = isFunInfix ss i
isFunInfix (NewVar @{ss} s)     i         = isFunInfix ss i

public export
getExprs : ExprList hofs hots hotvars casts funs vars argTys -> List $ Exists $ Expr hofs hots hotvars casts funs vars
getExprs [] = []
getExprs (x :: xs) = Evidence _ x :: getExprs xs


||| See AddCast (Runner)
public export
data CastMock : Type where
  Mock : CastMock
