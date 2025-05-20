module Dynam.Model.Primitives.HighOrder.Funs

import Dynam.Model.Primitives.HighOrder.Types
import Dynam.Model.Primitives.HighOrder.Casts

import Dynam.Model.Primitives.Types

import Data.Fin

export infix 1 ==>

public export
record HighOrderFunction (dim : Nat) where
    constructor Signature
    This : HighOrderType dim
    From : ListOfBasicTypes
    To   : BasicType

public export
Injective Signature where
    injective Refl = Refl

public export
data VectOfHOF : (dim : Nat) -> (size : Nat) -> Type where
    Nil  : VectOfHOF dim 0
    (::) : HighOrderFunction dim -> VectOfHOF dim size -> VectOfHOF dim (S size)

public export
data AtIndex : (sx : VectOfHOF totalCnt size)  ->
               (idx : Fin size)                ->
               (this : HighOrderType totalCnt) ->
               (args : ListOfBasicTypes)       -> 
               (retTy : BasicType)             -> Type where
    [search sx idx]
    Here  : AtIndex ((Signature this args retTy) :: sx) FZ this args retTy
    There : AtIndex sx i this args retTy -> AtIndex (x :: sx) (FS i) this args retTy

-- public export
-- data Contains : ListOfFunctions -> Function -> Type where
--     Single : Contains (fun :: _) fun
--     Multiple : Contains funs fun -> Contains (_ :: funs) fun

-- public export
-- length : VectOfHOF n -> Nat
-- length {VectOfHOF n} = n

-- public export
-- (.length) : VectOfHOF -> Nat
-- (.length) = length
