module Dynam.Model.Primitives

import public Data.List
import public Data.List.Quantifiers

import public Decidable.Equality
import public Decidable.Decidable

import public Dynam.Model.Primitives.Types
import public Dynam.Model.Primitives.Casts
import public Dynam.Model.Primitives.Funs

public export
[FunR] {r : MaybeVoidableType} -> Injective (\l => l ==> r) where
    injective Refl = Refl

export
DecEq Function where
    decEq (f ==> Void) (f' ==> Void   ) = decEqCong @{FunR} $ decEq f f'
    decEq (f ==> Void) (f' ==> NonVoidable _) = No $ \case Refl impossible

    decEq (f ==> NonVoidable _) (f' ==> Void   ) = No $ \case Refl impossible
    decEq (f ==> NonVoidable ty1) (f' ==> NonVoidable ty2) = decEqCong2 (decEq f f') (decEqCong @{nvoid} $ decEq ty1 ty2)