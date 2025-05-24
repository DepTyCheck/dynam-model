module Dynam.Model.Exprs

import Dynam.Model.Primitives
import Dynam.Model.Primitives.HighOrder

import Data.So
import Data.Fin

-- casts -> funs -> 
public export
data ExprList : (hod : HOData dim) ->
                (casts : ListOfSupportedCasts) ->
                (funs  : ListOfFunctions)  ->
                (vars  : ListOfBasicTypes) ->
                (retTy : ListOfBasicTypes) -> Type


-- available casts -> functions' scope -> variables' scope -> type
-- Must be non-Void
public export
data Expr : (hod : HOData dim) ->
            (casts : ListOfSupportedCasts) ->
            (funs  : ListOfFunctions)  ->
            (vars  : ListOfBasicTypes) ->
            (retTy : BasicType) -> Type where
    Literal : (x : TypeDeclaration ty) -> Castable casts ty resTy => Expr hod casts funs vars resTy
    -- var _
    -- Var : (n : IndexIn vars {-ty-}) ->
    --     AtIndex n ty1 =>
    --     Castable casts ty1 resTy =>
    --     Expr hofs hots hotvars casts funs vars resTy
    Var : {0 ty : BasicType} -> (n : IndexIn vars) ->
          AtIndex n ty =>
          Castable casts ty resTy => 
          Expr hod casts funs vars resTy


    -- function () => {}
    -- Invoke : (fun : IndexIn funs argTypes (NonVoidable to)) ->
    --     -- AtIndex fun argTypes (NonVoidable to) =>
    --     (actualArgs : ExprList hofs hots hotvars casts funs vars argTypes) ->
    --     Castable casts to resTy =>
    --     Expr hofs hots hotvars casts funs vars resTy
    -- InvokeHOF : (hof : Fin _) ->
    --     (thisIdx : IndexIn hotvars) ->
    --     AtIndex hotvars thisIdx (HasMethods methods) =>
    --     TrueIn methods hof =>
    --     AtIndex hofs hof this args to =>
    --     (actualArgs : ExprList hofs hots hotvars casts funs vars args) ->
    --     Castable casts to retTy =>
    --     Expr hofs hots hotvars casts funs vars retTy

public export
data ExprList : (hod : HOData dim) ->
                (casts : ListOfSupportedCasts) ->
                (funs  : ListOfFunctions)  ->
                (vars  : ListOfBasicTypes) ->
                (retTy : ListOfBasicTypes) -> Type where
    Nil  : ExprList hod casts funs vars []
    (::) : Expr hod casts funs vars ty -> ExprList hod casts funs vars sx -> ExprList hod casts funs vars (ty :: sx)
