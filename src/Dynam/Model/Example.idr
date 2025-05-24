module Dynam.Model.Example

import Dynam.Model.Stmts
import Dynam.Model.Primitives
import Dynam.Model.DSL

import Data.Nat
import Data.Fin
import Data.So

TyA : HighOrderType 3
TyA = HasMethods [ True, False, True ]

TyB : HighOrderType 3
TyB = HasMethods [ False, False, True ]

StdHOT : ListOfHOT 3
StdHOT = [
    TyA,
    TyB
]

F1 = Signature TyA [] Boolean
F2 = Signature TyB [] Boolean
F3 = Signature TyA [Number] Number

StdMet : VectOfHOF 3 3
StdMet = [
    F1, F2, F3
]

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

program : Stmts StdMet StdHOT [] StdC StdF []
program = do
{- 0 -} NewV $ Literal (I 10)
{- 1 -} NewV $ Literal (I 11)
{- 2 -} NewV $ Literal (B True)
        There Here #= Literal (I 14)
        0 #= Var 1
        0 #= Var 2
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

{- 3 -} NewV $ Literal (I 10)
        While ( Invoke Pred [Var 3] )
            (do
                3 #= Invoke Plus [ Var 3, Literal (I 1) ]
                Ret
            )

        -- NewHotVar 0 -- HotVar 0

        -- While ( InvokeHOF (FS $ FS FZ) 0 [Literal (I 7)] )
        --     (do
        --         Ret
        --     )

        Ret
