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
public export
data Expr : ListOfSupportedCasts -> ListOfFunctions -> ListOfBasicTypes -> BasicType -> Type where
    -- const _
    Const : (x : TypeDeclaration ty) -> Expr casts funs vars ty
    -- var _
    Var : (n : IndexIn vars) -> -- rename
        AtIndex n ty =>
        Expr casts funs vars ty
    -- function () => {}
    Invoke : (n : IndexIn funs) ->
        AtIndex n (argTypes ==> to) =>
        So (isNo $ decEq Void to) => --FIXME
        (actualArgs : ExprList casts funs vars retTypes) ->
        ArgsCastable casts retTypes argTypes => 
        Expr casts funs vars to        

public export
data ExprList : ListOfSupportedCasts -> ListOfFunctions -> ListOfBasicTypes -> ListOfBasicTypes -> Type where
    Nil  : ExprList casts vars funs []
    (::) : Expr casts funs vars ty -> ExprList casts funs vars sx -> ExprList casts funs vars (ty :: sx)