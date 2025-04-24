module Dynam.Model.Exprs

import Dynam.Model.Primitives

import Data.So

-- casts -> funs -> 
public export
data ExprList : ListOfSupportedCasts
                -> ListOfFunctions
                -> ListOfBasicTypes
                -> ListOfBasicTypes
                -> Type


-- available casts -> functions' scope -> variables' scope -> type
-- Must be non-Void
public export
data Expr : ListOfSupportedCasts -> ListOfFunctions -> ListOfBasicTypes -> BasicType -> Type where
    -- const _
    Literal : (x : TypeDeclaration ty) -> Castable casts ty resTy => Expr casts funs vars resTy
    -- var _
    Var : (n : IndexIn vars) ->
        AtIndex n ty =>
        Castable casts ty resTy => 
        Expr casts funs vars resTy
    -- function () => {}
    Invoke : (n : IndexIn funs) ->
        AtIndex n argTypes (NonVoidable to) =>
        (actualArgs : ExprList casts funs vars argTypes) ->
        Expr casts funs vars to        

public export
data ExprList : ListOfSupportedCasts -> ListOfFunctions -> ListOfBasicTypes -> ListOfBasicTypes -> Type where
    Nil  : ExprList casts vars funs []
    (::) : Expr casts funs vars ty -> ExprList casts funs vars sx -> ExprList casts funs vars (ty :: sx)
