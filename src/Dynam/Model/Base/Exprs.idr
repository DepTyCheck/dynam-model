module Dynam.Model.Base.Exprs

import public Dynam.Model.Primitives.Base

import Data.So
import Data.Fin


public export
data ExprList : (casts : ListOfSupportedCasts) ->
                (funs  : ListOfFunctions)  ->
                (vars  : ListOfBasicTypes) ->
                (retTy : ListOfBasicTypes) -> Type

public export
data Expr : (casts : ListOfSupportedCasts) ->
            (funs  : ListOfFunctions)  ->
            (vars  : ListOfBasicTypes) ->
            (retTy : BasicType) -> Type where
    Literal : (ty : BasicType) -> Castable casts ty resTy => Expr casts funs vars resTy
    Var : {0 ty : BasicType} ->
          (n : IndexIn vars) ->
          AtIndex n ty =>
          Castable casts ty resTy => 
          Expr casts funs vars resTy
    Invoke : (fun : IndexIn funs) ->
        AtIndex fun argTypes (NonVoidable to) =>
        (actualArgs : ExprList casts funs vars argTypes) ->
        Castable casts to resTy =>
        Expr casts funs vars resTy

public export
data ExprList : (casts : ListOfSupportedCasts) ->
                (funs  : ListOfFunctions)  ->
                (vars  : ListOfBasicTypes) ->
                (retTy : ListOfBasicTypes) -> Type where
    Nil  : ExprList casts funs vars []
    (::) : Expr casts funs vars ty -> ExprList casts funs vars xs -> ExprList casts funs vars (ty :: xs)
