module Dynam.Run.StdConfig

import Dynam.Model.Base
import Dynam.Pretty.Base


public export
record NamedCtxt where
    constructor MkNamedCtxt
    typecasts : ListOfSupportedCasts
    functions : ListOfFunctions
    variables : ListOfBasicTypes
    fvNames   : UniqNames functions variables

public export %inline
AddFun : (isInfix : Bool) ->
         (s : String) ->
         (fun : Function) ->
         (ctx : NamedCtxt) ->
         (0 _ : NameIsNew ctx.functions ctx.variables ctx.fvNames s) =>
         NamedCtxt
AddFun isInfix s fun $ MkNamedCtxt casts funs vars names =
    MkNamedCtxt casts (fun :: funs) vars $ NewFun @{names} {isInfix} {fun} s

public export %inline
AddCast : (cast : SupportedTypecast) ->
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
stdGroovy : NamedCtxt
stdGroovy = do
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
    
    AddCast $ Number %= Boolean
    AddCast $ Str    %= Boolean
    Enough

public export
stdJS : NamedCtxt
stdJS = do
    AddFun False "console.log" $ [Str] ==> Void
    AddFun False "console.info" $ [Str] ==> Void
    AddFun False "console.error" $ [Str] ==> Void
    AddFun False "console.warn" $ [Str] ==> Void

    AddFun True  "+"       $ [Number, Number] ==> (NonVoidable Number)
    AddFun True  "*"       $ [Number, Number] ==> (NonVoidable Number)
    AddFun False "-"       $ [Number] ==> (NonVoidable Number)
    AddFun True  "<"       $ [Number, Number] ==> (NonVoidable Boolean)
    AddFun True  "<="      $ [Number, Number] ==> (NonVoidable Boolean)
    AddFun True  "=="      $ [Number, Number] ==> (NonVoidable Boolean)
    AddFun True  "||"      $ [Boolean, Boolean] ==> (NonVoidable Boolean)
    AddFun True  "&&"      $ [Boolean, Boolean] ==> (NonVoidable Boolean)
    AddFun False "!"       $ [Boolean] ==> (NonVoidable Boolean)
    
    AddCast $ Boolean %= Number
    AddCast $ Number  %= Boolean
    AddCast $ Number  %= Str
    AddCast $ Str  %= Number
    AddCast $ Str  %= Boolean
    AddCast $ Boolean  %= Str
    Enough

public export
stdLua : NamedCtxt
stdLua = do
    AddFun False "print" $ [Str] ==> Void

    AddFun True  "+"       $ [Number, Number] ==> (NonVoidable Number)
    AddFun True  "*"       $ [Number, Number] ==> (NonVoidable Number)
    AddFun False "-"       $ [Number] ==> (NonVoidable Number)
    AddFun True  "<"       $ [Number, Number] ==> (NonVoidable Boolean)
    AddFun True  "<="      $ [Number, Number] ==> (NonVoidable Boolean)
    AddFun True  "=="      $ [Number, Number] ==> (NonVoidable Boolean)
    AddFun True  "or"      $ [Boolean, Boolean] ==> (NonVoidable Boolean)
    AddFun True  "and"     $ [Boolean, Boolean] ==> (NonVoidable Boolean)
    AddFun False "not"     $ [Boolean] ==> (NonVoidable Boolean)

    AddCast $ Number  %= Boolean
    AddCast $ Number  %= Str
    AddCast $ Str  %= Number
    AddCast $ Str  %= Boolean
    AddCast $ Boolean  %= Str
    Enough

public export
stdPy : NamedCtxt
stdPy = do
    AddFun False "print" $ [Str] ==> Void

    AddFun True  "+"       $ [Number, Number] ==> (NonVoidable Number)
    AddFun True  "*"       $ [Number, Number] ==> (NonVoidable Number)
    AddFun False "-"       $ [Number] ==> (NonVoidable Number)
    AddFun True  "<"       $ [Number, Number] ==> (NonVoidable Boolean)
    AddFun True  "<="      $ [Number, Number] ==> (NonVoidable Boolean)
    AddFun True  "=="      $ [Number, Number] ==> (NonVoidable Boolean)
    AddFun True  "or"      $ [Boolean, Boolean] ==> (NonVoidable Boolean)
    AddFun True  "and"     $ [Boolean, Boolean] ==> (NonVoidable Boolean)
    AddFun False "not"     $ [Boolean] ==> (NonVoidable Boolean)

    AddCast $ Number  %= Boolean
    AddCast $ Number  %= Str
    AddCast $ Str  %= Boolean
    AddCast $ Boolean  %= Str
    Enough

public export
shared : NamedCtxt
shared = do
    AddFun False "sout" $ [Str] ==> Void

    AddFun True  "+"       $ [Number, Number] ==> (NonVoidable Number)
    -- AddFun True  "*"       $ [Str, Number] ==> (NonVoidable Str)
    -- AddFun True  "or"      $ [Boolean, Boolean] ==> (NonVoidable Boolean)
    AddFun False "invert"       $ [Boolean] ==> (NonVoidable Boolean)
    
    AddCast $ Number  %= Boolean
    AddCast $ Str     %= Boolean
    AddCast $ Number  %= Str
    AddCast $ Boolean %= Str
    Enough

