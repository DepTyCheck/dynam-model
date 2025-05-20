module Dynam.Model.Primitives.HighOrder.Types

import public Data.List
import public Data.List.Quantifiers

import public Decidable.Equality
import public Decidable.Decidable

import Dynam.Model.Primitives.Funs
import Dynam.Model.Primitives.Types

namespace Bool

namespace BoolMonomorphic
    public export
    data VectOfBool : Nat -> Type where
        Nil  : VectOfBool 0
        (::) : Bool -> VectOfBool n -> VectOfBool (S n)

    public export
    Biinjective BoolMonomorphic.(::) where
        biinjective Refl = (Refl, Refl)
    
    public export
    DecEq (VectOfBool n) where
        decEq Nil Nil = Yes Refl
        decEq (x :: xs) (y :: ys) = decEqCong2 (decEq x y) (decEq xs ys)

public export
data HighOrderType : (hofCnt : Nat) -> Type where
    HasMethods : VectOfBool hofCnt -> HighOrderType hofCnt
 
public export
data ListOfHOT : (hofCnt : Nat) -> Type where
    Nil  : ListOfHOT hofCnt
    (::) : HighOrderType hofCnt -> ListOfHOT hofCnt -> ListOfHOT hofCnt

public export
length : ListOfHOT _ -> Nat
length Nil = Z
length (_ :: xs) = S (length xs)

public export
data Contains : ListOfHOT hofCnt -> HighOrderType hofCnt -> Type where
    Single   : Contains (ty :: other) ty
    Multiple : Contains tys ty -> Contains (new :: tys) ty

public export
data IndexIn : ListOfHOT hofCnt -> Type where
    Here  : IndexIn $ x :: sx
    There : IndexIn sx -> IndexIn $ x :: sx

public export
data AtIndex : (sx : ListOfHOT hofCnt) ->
               (idx : IndexIn sx) ->
               (to : HighOrderType hofCnt) -> Type where
    [search sx idx]
    Here'  : AtIndex (to :: sx) Here to
    There' : AtIndex sx i to -> AtIndex (x :: sx) (There i) to

-- public export
-- Injective HasMethods where
--     injective Refl = Refl

-- public export
-- DecEq (HighOrderType hofCnt) where
--     decEq (HasMethods l1) (HasMethods l2) = decEqCong $ decEq l1 l2

-- public export
-- Biinjective Dynam.Model.Primitives.HighOrder.Types.(::) where
--     biinjective Refl = (Refl, Refl)

-- public export
-- DecEq (ListOfHOT) where
--     decEq Nil Nil = Yes Refl
--     decEq Nil (_ :: _) =  No $ \case Refl impossible
--     decEq (_ :: _) Nil =  No $ \case Refl impossible
--     decEq (x :: xs) (y :: ys) = decEqCong2 (decEq x y) (decEq xs ys)

