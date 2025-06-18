module Dynam.Model.Example.Base

import Dynam.Model.Example.DSL

import Data.Nat
import Data.Fin
import Data.So

StdF : ListOfFunctions
StdF = [    
      [Str] ==> Void -- print
    , [Boolean] ==> (NonVoidable Boolean) -- pred
    , [Number, Boolean] ==> (NonVoidable Number) -- +
    , [Number, Number] ==> Void   -- dum
    -- , []
]


StdC : ListOfSupportedCasts
StdC = [
    Boolean %= Number,
    Number  %= Boolean,
    Str     %= Boolean
]

Log : IndexIn StdF
Log = 3

Pred : IndexIn StdF
Pred = 2

Plus : IndexIn StdF
Plus = 1

Dum : IndexIn StdF
Dum = 0

program : Stmts StdC StdF []
program = do
{- 0 -} NewV Number  $ Literal 10
{- 1 -} NewV Boolean $ Literal 11
{- 2 -} NewV Boolean $ Literal 12
        2 #= Literal 14
        -- 0 #= Var 2
        1 #= Literal True
        2 #= Invoke Plus [ Var 0, Var 1 ]
        -- NewV Void $ Invoke Dum [ Var 0, Var 1 ]


        Call Dum [ Literal 6, Literal 9 ]
        If  ( Literal False )
            (do
                1 #= Var 0
                Ret)
            (do
                1 #= Literal True
                Ret)
        2 #= Var 1

{- 3 -} NewV Str $ Literal "89"
        While ( Invoke Pred [Var 3] )
            (do
                Call Log [ Var 3 ]
                Ret
            )
        Ret
