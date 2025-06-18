module Dynam.Pretty.Objects.Utils

import Dynam.Model.Objects

import Data.List
import public Data.So
import Data.DPair

public export
data UniqNames : (meths : VectOfFuns dim)    ->
                 (clss  : ListOfClasses dim) ->
                 (objs  : ListOfClasses dim) ->
                 (funs  : ListOfFunctions)   ->
                 (vars  : ListOfBasicTypes)  -> Type
public export
data NameIsNew : (meths : VectOfFuns dim)    ->
                 (clss  : ListOfClasses dim) ->
                 (objs  : ListOfClasses dim) ->
                 (funs  : ListOfFunctions)   ->
                 (vars  : ListOfBasicTypes)  ->
                 UniqNames meths clss objs funs vars ->
                 String -> Type

public export
data UniqNames : (meths : VectOfFuns dim)    ->
                 (clss  : ListOfClasses dim) ->
                 (objs  : ListOfClasses dim) ->
                 (funs  : ListOfFunctions)   ->
                 (vars  : ListOfBasicTypes)  -> Type where
    [search funs vars]
    Empty   : UniqNames [] [] [] [] []
    JustNew : (prevNames : UniqNames meths clss objs funs vars) =>
              (newName : String) ->
              (0 _ : NameIsNew meths clss objs funs vars prevNames newName) =>
              UniqNames meths clss objs funs vars
    NewFun  : (prevNames : UniqNames meths clss objs funs vars) =>
              (newName : String) ->
              (0 _ : NameIsNew meths clss objs funs vars prevNames newName) =>
              {default False isInfix : Bool} ->
              UniqNames meths clss objs (fun :: funs) vars
    NewVar  : (prevNames : UniqNames meths clss objs funs vars) =>
              (newName : String) ->
              (0 _ : NameIsNew meths clss objs funs vars prevNames newName) =>
              UniqNames meths clss objs funs (var :: vars)
    NewCls  : (prevNames : UniqNames meths clss objs funs vars) =>
              (newName : String) ->
              (0 _ : NameIsNew meths clss objs funs vars prevNames newName) =>
              UniqNames meths (cls :: clss) objs funs vars
    NewObj  : (prevNames : UniqNames meths clss objs funs vars) =>
              (newName : String) ->
              (0 _ : NameIsNew meths clss objs funs vars prevNames newName) =>
              UniqNames meths clss (obj :: objs) funs vars
    -- NewMet  : (prevNames : UniqNames meths clss objs funs vars) =>
    --           (newName : String) ->
    --           (0 _ : NameIsNew meths clss objs funs vars prevNames newName) =>
    --           UniqNames (meth :: meths) clss objs funs vars

public export
data NameIsNew : (meths : VectOfFuns dim)    ->
                 (clss  : ListOfClasses dim) ->
                 (objs  : ListOfClasses dim) ->
                 (funs  : ListOfFunctions)   ->
                 (vars  : ListOfBasicTypes)  ->
                 UniqNames meths clss objs funs vars ->
                 String -> Type where
    E : NameIsNew [] [] [] [] [] Empty curr

    J : (0 _ : So $ curr /= newName) -> NameIsNew meths clss objs funs vars prevNames curr ->
        NameIsNew meths clss objs funs vars (JustNew @{prevNames} newName @{sub}) curr

    F : (0 _ : So $ curr /= newName) -> NameIsNew meths clss objs funs vars prevNames curr ->
        NameIsNew meths clss objs (fun :: funs) vars (NewFun @{prevNames} {isInfix} newName @{sub}) curr

    V : (0 _ : So $ curr /= newName) -> NameIsNew meths clss objs funs vars prevNames curr ->
        NameIsNew meths clss objs funs (var :: vars) (NewVar @{prevNames} newName @{sub}) curr
    
    C : (0 _ : So $ curr /= newName) -> NameIsNew meths clss objs funs vars prevNames curr ->
        NameIsNew meths (cls :: clss) objs funs vars (NewCls @{prevNames} newName @{sub}) curr

    O : (0 _ : So $ curr /= newName) -> NameIsNew meths clss objs funs vars prevNames curr ->
        NameIsNew meths clss (obj :: objs) funs vars (NewObj @{prevNames} newName @{sub}) curr


public export
genVarName : UniqNames meths clss objs funs vars -> IndexIn vars -> String
genVarName (JustNew @{ss} _) i         = genVarName ss i
genVarName (NewFun @{ss} _)  i         = genVarName ss i
genVarName (NewCls @{ss} _)  i         = genVarName ss i
genVarName (NewObj @{ss} _)  i         = genVarName ss i
genVarName (NewVar @{ss} _)  (There i) = genVarName ss i
genVarName (NewVar s)        Here      = s

public export
genFunName : UniqNames meths clss objs funs vars -> IndexIn funs -> String
genFunName (JustNew @{ss} _) i         = genFunName ss i
genFunName (NewCls @{ss} _)  i         = genFunName ss i
genFunName (NewObj @{ss} _)  i         = genFunName ss i
genFunName (NewVar @{ss} _)  i         = genFunName ss i
genFunName (NewFun @{ss} _)  (There i) = genFunName ss i
genFunName (NewFun s)        Here      = s

public export
genObjName : UniqNames meths clss objs funs vars -> IndexIn objs -> String
genObjName (JustNew @{ss} _) i         = genObjName ss i
genObjName (NewCls @{ss} _)  i         = genObjName ss i
genObjName (NewFun @{ss} _)  i         = genObjName ss i
genObjName (NewVar @{ss} _)  i         = genObjName ss i
genObjName (NewObj @{ss} _)  (There i) = genObjName ss i
genObjName (NewObj s)        Here      = s

public export
genClsName : UniqNames meths clss objs funs vars -> IndexIn clss -> String
genClsName (JustNew @{ss} _) i         = genClsName ss i
genClsName (NewFun @{ss} _)  i         = genClsName ss i
genClsName (NewObj @{ss} _)  i         = genClsName ss i
genClsName (NewVar @{ss} _)  i         = genClsName ss i
genClsName (NewCls @{ss} _)  (There i) = genClsName ss i
genClsName (NewCls s)        Here      = s

public export
isFunInfix : UniqNames meths clss objs funs vars -> IndexIn funs -> Bool
isFunInfix (JustNew @{ss} _)    i         = isFunInfix ss i
isFunInfix (NewVar @{ss} s)     i         = isFunInfix ss i
isFunInfix (NewCls @{ss} s)     i         = isFunInfix ss i
isFunInfix (NewObj @{ss} s)     i         = isFunInfix ss i
isFunInfix (NewFun @{ss} s)     (There i) = isFunInfix ss i
isFunInfix (NewFun {isInfix} _) Here      = isInfix

public export
getExprs : ExprList meths clss objs casts funs vars argTys -> List $ Exists $ Expr meths clss objs casts funs vars
getExprs [] = []
getExprs (x :: xs) = Evidence _ x :: getExprs xs


