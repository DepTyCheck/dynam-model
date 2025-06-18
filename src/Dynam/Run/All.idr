module Dynam.Run.All

import Data.SortedMap

import public Dynam.Run.Config
import public Dynam.Run.ParseInput
-- import public Dynam.Run.StmtsDerive
import public Dynam.Run.StdConfig

import public Dynam.Run.Derive.BaseNameDerive
import public Dynam.Run.Derive.BaseDerive


import public Dynam.Model.Base
import public Dynam.Pretty.Base

public export
0 PP : Type
PP = {casts : _} -> {funs : _} -> {vars : _} -> {opts : _} ->
     (names : UniqNames funs vars) =>
     Fuel ->
     Stmts casts funs vars -> Gen0 $ Doc opts

public export
supportedLanguages : SortedMap String (NamedCtxt, PP)
supportedLanguages = fromList [ 
      ("groovy", (stdGroovy, printGroovy))
    , ("js",     (stdJS,     printJS))
    , ("py",     (stdPy,     printPy))
    , ("lua",    (stdLua,    printLua))
]

public export
supportedLanguagesShared : SortedMap String (NamedCtxt, PP)
supportedLanguagesShared = fromList [ 
      ("groovy", (shared, printGroovy))
    , ("js",     (shared, printJS))
    , ("py",     (shared, printPy))
]

