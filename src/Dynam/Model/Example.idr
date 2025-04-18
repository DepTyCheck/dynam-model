module Dynam.Model.Example

import Dynam.Model.Main
import Dynam.Model.Primitives
import Dynam.Model.DSL

import Data.Nat
import Data.So

StdF : ListOfFunctions
StdF = [    
      [Number] ==> (NonVoidable Boolean)
    , [Number, Boolean] ==> (NonVoidable Number) -- +
    , [Number, Number] ==> Void   -- dum
    -- , []
]


StdC : ListOfSupportedCasts
StdC = [
    Boolean %= Number,
    Number  %= Boolean
]

Pred : IndexIn StdF
Pred = 2

Plus : IndexIn StdF
Plus = 1

Dum : IndexIn StdF
Dum = 0

program : Stmts StdC StdF []
program = do
{- 0 -} NewV Number $ Literal (I 10)
{- 1 -} NewV Number $ Literal (I 11)
{- 2 -} NewV Boolean $ Literal (B True)
        0 #= Literal (I 14)
--         0 #= Var 1
--         0 #= Var 2
        2 #= Invoke Plus [ Var 0, Var 2 ]
        -- NewV Void $ Invoke Dum [ Var 0, Var 1 ]

        Call Dum [ Literal (I 6), Literal (B False) ]
        If  ( Literal (B True) )
            (do
                1 #= Var 0
                Ret)
            (do
                1 #= Literal (B True)
                Ret)
        2 #= Var 1

{- 3 -} NewV Number $ Literal (I 10)
        While ( Invoke Pred [Var 3] )
            (do
                3 #= Invoke Plus [ Var 3, Literal (I 1) ]
                Ret
            )
        Ret

-- export
-- main : IO ()
-- main = do
--     -- let seed <- conf.usedSeed
--     -- let vals = unGenTryN conf.testsCnt seed $
--     --             genStmts conf.modelFuel ctxt.typecasts ctxt.functions ctxt.variables Void >>=
--     --                 printGroovy @{ctxt.fvNames} conf.ppFuel
--     putStr $ render



