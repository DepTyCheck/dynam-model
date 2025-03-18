module Dynam.Model.Primitives

import public Data.List
import public Data.List.Quantifiers

import public Decidable.Equality
import public Decidable.Decidable

import public Dynam.Model.Primitives.Types
import public Dynam.Model.Primitives.Casts
import public Dynam.Model.Primitives.Funs

public export
[FunR] {r : BasicType voidIs} -> Injective (\l => l ==> r) where
    injective Refl = Refl

export
DecEq Function where
    decEq (f ==> Void) (f' ==> Void   ) = decEqCong @{FunR} $ decEq f f'
    decEq (f ==> Void) (f' ==> Number ) = No $ \case Refl impossible
    decEq (f ==> Void) (f' ==> Boolean) = No $ \case Refl impossible

    decEq (f ==> Boolean) (f' ==> Void   ) = No $ \case Refl impossible
    decEq (f ==> Boolean) (f' ==> Number ) = No $ \case Refl impossible
    decEq (f ==> Boolean) (f' ==> Boolean) = decEqCong @{FunR} $ decEq f f'

    decEq (f ==> Number) (f' ==> Void   ) = No $ \case Refl impossible
    decEq (f ==> Number) (f' ==> Number ) = decEqCong @{FunR} $ decEq f f'
    decEq (f ==> Number) (f' ==> Boolean) = No $ \case Refl impossible