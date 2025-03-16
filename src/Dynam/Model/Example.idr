module Dynam.Model.Example

import Dynam.Model.Main
import Dynam.Model.Primitives
import Dynam.Model.DSL

import Data.Nat
import Data.So

StdF : ListOfFunctions
StdF = [
      [Number] ==> Boolean
    , [Number, Number] ==> Number -- +
    , [Number, Number] ==> Void   -- dum
    -- , []
]


StdC : ListOfSupportedCasts
StdC = [
    Boolean %= [Number]
]

Pred : IndexIn StdF
Pred = 2

Plus : IndexIn StdF
Plus = 1

Dum : IndexIn StdF
Dum = 0

-- ss : Contains [Number] Number
-- ss = Single

-- check : IsCastable (Boolean %= [Number]) Boolean Number
-- check = MakeCast Single -- (Boolean %= [Number]) Boolean Number

-- ch : Match StdC Boolean Number
-- ch = FirstCast check

program : Stmts StdC StdF [] Void
program = do
{- 0 -} NewV Number $ Const (I 10)
{- 1 -} NewV Number $ Const (I 11)
{- 2 -} NewV Boolean $ Const (B True)
        0 #= Const (I 14)
--         0 #= Var 1
--         0 #= Var 2
--         1 #= Invoke Plus [ Var 0, Var 2 ]

--         -- Call Dum [ Const (I 6), Const (B False) ]
--         If  ( Const (B True) )
--             (do
--                 1 #= Var 0
--                 Ret)
--             (do
--                 1 #= Const (B True)
--                 Ret)
--         -- 2 #= Var 1

-- {- 3 -} NewV Number $ Const (I 10)
--         While ( Invoke Pred [Var 3] )
--             (do
--                 3 #= Invoke Plus [ Var 3, Const (I 1) ]
--                 Ret
--             )

        Ret

-- export
-- main : IO ()
-- main = do
--     -- let seed <- conf.usedSeed
--     -- let vals = unGenTryN conf.testsCnt seed $
--     --             genStmts conf.modelFuel ctxt.typecasts ctxt.functions ctxt.variables Void >>=
--     --                 printGroovy @{ctxt.fvNames} conf.ppFuel
--     putStr $ render



