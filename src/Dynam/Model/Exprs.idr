module Dynam.Model.Exprs

import Dynam.Model.Primitives
import Dynam.Model.Primitives.HighOrder

import Data.So
import Data.Fin

-- casts -> funs -> 
public export
data ExprList : (hofs  : VectOfHOF dim dim) ->
                (hots  : ListOfHOT dim) ->
                (hotvars : ListOfHOT dim) ->
                (casts : ListOfSupportedCasts) ->
                (funs  : ListOfFunctions)  ->
                (vars  : ListOfBasicTypes) ->
                (retTy : ListOfBasicTypes) -> Type


-- available casts -> functions' scope -> variables' scope -> type
-- Must be non-Void
public export
data Expr : (hofs  : VectOfHOF dim dim) ->
            (hots  : ListOfHOT dim) ->
            (hotvars : ListOfHOT dim) ->
            (casts : ListOfSupportedCasts) ->
            (funs  : ListOfFunctions)  ->
            (vars  : ListOfBasicTypes) ->
            (retTy : BasicType) -> Type where
    Literal : (x : TypeDeclaration ty) -> Castable casts ty resTy => Expr hofs hots hotvars casts funs vars resTy
    -- var _
    Var : {0 ty : _} ->
        (n : IndexIn vars) ->
        AtIndex n ty =>
        Castable casts ty resTy =>
        Expr hofs hots hotvars casts funs vars resTy
    -- function () => {}
    Invoke : (fun : IndexIn funs) ->
        AtIndex fun argTypes (NonVoidable to) =>
        (actualArgs : ExprList hofs hots hotvars casts funs vars argTypes) ->
        -- Castable casts to resTy =>
        Expr hofs hots hotvars casts funs vars to
    -- InvokeHOF : (hof : Fin _) ->
    --     (thisIdx : IndexIn hotvars) ->
    --     AtIndex hotvars thisIdx (HasMethods methods) =>
    --     TrueIn methods hof =>
    --     AtIndex hofs hof this args to =>
    --     (actualArgs : ExprList hofs hots hotvars casts funs vars args) ->
    --     Castable casts to retTy =>
    --     Expr hofs hots hotvars casts funs vars retTy

public export
data ExprList : VectOfHOF dim dim -> ListOfHOT dim -> ListOfHOT dim -> ListOfSupportedCasts -> ListOfFunctions -> ListOfBasicTypes -> ListOfBasicTypes -> Type where
    Nil  : ExprList hofs hots hotvars casts funs vars []
    (::) : Expr hofs hots hotvars casts funs vars ty -> ExprList hofs hots hotvars casts funs vars sx -> ExprList hofs hots hotvars casts funs vars (ty :: sx)
