module Dynam.Run.StdConfig

import Dynam.Model.Main
import Dynam.Model.Primitives

import Dynam.Pretty.Pretty
import Dynam.Pretty.Utils


public export
record NamedCtxt where
  constructor MkNamedCtxt
  typecasts : ListOfSupportedCasts
  functions : ListOfFunctions
  variables : ListOfBasicTypes
  fvNames   : UniqNames functions variables

public export %inline
AddFun : (isInfix : Bool) -> (s : String) -> (fun : Function) ->
        --  (lCond : LanguageToCondition fun isInfix isPure) =>
         (ctx : NamedCtxt) ->
         (0 _ : NameIsNew ctx.functions ctx.variables ctx.fvNames s) =>
         NamedCtxt
AddFun isInfix s fun $ MkNamedCtxt casts funs vars names =
  MkNamedCtxt casts (fun :: funs) vars $ NewFun @{names} {isInfix} {fun} s

public export %inline
AddCast : (cast : SupportedTypecast) ->
        --  (lCond : LanguageToCondition fun isInfix isPure) =>
         (ctx : NamedCtxt) ->
         (0 _ : CastMock) =>
         NamedCtxt
AddCast cast $ MkNamedCtxt casts funs vars names =
  MkNamedCtxt (cast :: casts) funs vars names


public export %inline
Enough : NamedCtxt
Enough = MkNamedCtxt [] [] [] Empty

public export %inline
(>>) : {0 arg : NamedCtxt -> Type}  ->
       ((ctx : NamedCtxt) -> (0 _ : arg ctx) => NamedCtxt) ->
       (ctx : NamedCtxt) -> (0 _ : arg ctx) => NamedCtxt
(>>) f x = f x

----------------
--  STD FUNS  --
----------------

public export
stdLib : NamedCtxt
stdLib = do
    AddFun False "println" $ [Number] ==> Void
    AddFun True  "+"       $ [Number, Number] ==> (NonVoidable Number)
    AddFun True  "*"       $ [Number, Number] ==> (NonVoidable Number)
    AddFun False "-"       $ [Number] ==> (NonVoidable Number)
    AddFun True  "<"       $ [Number, Number] ==> (NonVoidable Boolean)
    AddFun True  "<="      $ [Number, Number] ==> (NonVoidable Boolean)
    AddFun True  "=="      $ [Number, Number] ==> (NonVoidable Boolean)
    AddFun True  "||"      $ [Boolean, Boolean] ==> (NonVoidable Boolean)
    AddFun True  "&&"      $ [Boolean, Boolean] ==> (NonVoidable Boolean)
    AddFun False "!"       $ [Boolean] ==> (NonVoidable Boolean)
    
    AddCast $ Number  %= Boolean
    AddCast $ Boolean %= Number
    Enough

