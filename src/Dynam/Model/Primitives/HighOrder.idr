module Dynam.Model.Primitives.HighOrder

import public Dynam.Model.Primitives.HighOrder.Types
import public Dynam.Model.Primitives.HighOrder.Funs
import public Dynam.Model.Primitives.HighOrder.Casts

import Dynam.Model.Primitives

import Data.Fin

public export
record HOData where
    constructor MkHOD
    dim  : Nat
    hofs : VectOfHOF dim dim
    hots : ListOfHOT dim
    objs : ListOfHOT dim

-- export
-- DecEq HighOrderFunction where
--     decEq (f ==> ty1) (f' ==> ty2) = decEqCong2 (decEq f f') (decEq ty1 ty2)

public export
data UnifiedType : (dim : Nat) -> Type where
    HOT : HighOrderType dim -> UnifiedType dim
    BT  : BasicType -> UnifiedType dim

public export
data Castable : {dim : Nat} -> (casts : ListOfSupportedCasts) -> (from : UnifiedType dim) -> (to : UnifiedType dim) -> Type where
    HOTcast : Castable from to -> Castable casts (HOT from) (HOT to)
    BTcast  : Castable casts from to -> Castable casts (BT from) (BT to)

public export
data ListOfUnifiedTypes : Type where
    Nil : ListOfUnifiedTypes
    (::) : BasicType -> ListOfUnifiedTypes -> ListOfUnifiedTypes

public export
Biinjective Dynam.Model.Primitives.HighOrder.(::) where
    biinjective Refl = (Refl, Refl)

public export
data IndexIn : ListOfUnifiedTypes -> Type where
    Here  : IndexIn $ x :: sx
    There : IndexIn sx -> IndexIn $ x :: sx

public export
data AtIndex : {sx : ListOfUnifiedTypes} -> (idx : IndexIn sx) -> (ty : BasicType) -> Type where
    [search sx idx]
    Here'  : AtIndex {sx = ty :: sx} Here ty
    There' : AtIndex {sx} i ty -> AtIndex {sx = x :: sx} (There i) ty

public export
data Contains : ListOfUnifiedTypes -> BasicType -> Type where
    Single   : Contains (ty :: other) ty
    Multiple : Contains tys ty -> Contains (new :: tys) ty

public export
length : ListOfUnifiedTypes -> Nat
length [] = Z
length (_ :: sx) = S (length sx)

public export
(.length) : ListOfUnifiedTypes -> Nat
(.length) = length

public export
data TrueIn : VectOfBool dim -> Fin dim -> Type where
    True  : TrueIn (True :: other) FZ
    False : TrueIn other idx -> TrueIn (_ :: other) (FS idx)
