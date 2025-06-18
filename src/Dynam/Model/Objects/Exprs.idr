module Dynam.Model.Objects.Exprs

import Dynam.Model.Primitives.Objects

import Data.So
import Data.Fin

-- casts -> funs -> 
public export
data ExprList : (meths : VectOfFuns dim) ->
                (clss  : ListOfClasses dim) ->
                (objs  : ListOfClasses dim) -> 
                (casts : ListOfSupportedCasts) ->
                (funs  : ListOfFunctions)  ->
                (vars  : ListOfBasicTypes) ->
                (retTy : ListOfBasicTypes) -> Type


-- available casts -> functions' scope -> variables' scope -> type
-- Must be non-Void
public export
data Expr : (meths : VectOfFuns dim) ->
            (clss  : ListOfClasses dim) ->
            (objs  : ListOfClasses dim) -> 
            (casts : ListOfSupportedCasts) ->
            (funs  : ListOfFunctions)  ->
            (vars  : ListOfBasicTypes) ->
            (retTy : BasicType) -> Type where
    Literal : (ty : BasicType) -> Castable casts ty resTy => Expr meths clss objs casts funs vars resTy

    Var : {0 ty : BasicType} ->
          (n : IndexIn vars) ->
          AtIndex n ty =>
          Castable casts ty resTy => 
          Expr meths clss objs casts funs vars resTy

    Invoke : (fun : IndexIn funs) ->
             AtIndex fun argTypes (NonVoidable to) =>
             (actualArgs : ExprList casts funs vars argTypes) ->
             Castable casts to resTy =>
             Expr meths clss objs casts funs vars resTy

    InvokeMethod : (this : IndexIn objs) ->
                   (method : Fin dim) ->
                   AtIndex this allowedMethods =>
                   TrueIn allowedMethods method => 
                   AtIndex {methods} method args (NonVoidable to) =>
                   (actualArgs : ExprList methods clss objs casts funs vars args) ->
                   Castable casts to resTy =>
                   Expr methods clss objs casts funs vars resTy

public export
data ExprList : (meths : VectOfFuns dim) ->
                (clss  : ListOfClasses dim) ->
                (objs  : ListOfClasses dim) -> 
                (casts : ListOfSupportedCasts) ->
                (funs  : ListOfFunctions)  ->
                (vars  : ListOfBasicTypes) ->
                (retTy : ListOfBasicTypes) -> Type where
    Nil  : ExprList meths clss objs casts funs vars []
    (::) : Expr meths clss objs casts funs vars ty ->
           ExprList meths clss objs casts funs vars sx ->
           ExprList meths clss objs casts funs vars (ty :: sx)
