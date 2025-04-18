module Dynam.Model.Primitives.HighOrderTypes

import public Data.List
import public Data.List.Quantifiers

import public Decidable.Equality
import public Decidable.Decidable

import Dynam.Model.Primitives.Funs
import Dynam.Model.Primitives.Types


data AnyType : Type where
    Primitive : BasicType     -> AnyType
    Complex   : ListOfFunctions -> AnyType

data VoidableAnyType : Type where
    Pure : AnyType -> VoidableAnyType
    Void : VoidableAnyType

data ListOfAnyTypes : Type where
    Nil  : ListOfAnyTypes
    (::) : AnyType -> ListOfAnyTypes -> ListOfAnyTypes

data Contains : ListOfAnyTypes -> AnyType -> Type where
    Single   : Contains (ty :: other) ty
    Multiple : Contains tys ty -> Contains (new :: tys) ty

namespace Casts
    export infix 1 %=

    record SupportedTypecast where
        constructor (%=)
        From : AnyType
        Tos  : ListOfAnyTypes

    data ListOfSupportedCasts : Type where
        Nil : ListOfSupportedCasts
        (::) : SupportedTypecast -> ListOfSupportedCasts -> ListOfSupportedCasts

    data Castable : ListOfSupportedCasts -> (from : AnyType) -> (to : AnyType) -> Type where
        ReflCast  : Castable _ ty ty
        FirstCast : Contains tos to -> Castable ((from %= tos) :: _) from to
        NextCast  : Castable casts from to -> Castable (_ :: casts) from to


