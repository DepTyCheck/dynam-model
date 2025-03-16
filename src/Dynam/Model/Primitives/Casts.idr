module Dynam.Model.Primitives.Casts

import Dynam.Model.Primitives.Types

export infix 1 %=

public export
record SupportedTypecast where
    constructor (%=)
    MainType : BasicType
    ConvertableTo : ListOfBasicTypes

public export
data ListOfSupportedCasts : Type where
    Nil : ListOfSupportedCasts
    (::) : SupportedTypecast -> ListOfSupportedCasts -> ListOfSupportedCasts

public export
data IsCastable : SupportedTypecast -> BasicType -> BasicType -> Type where
    MakeCast : Contains tos to -> IsCastable (from %= tos) from to

public export
data Castable : ListOfSupportedCasts -> BasicType -> BasicType -> Type where
    ReflCast  : Castable _ ty ty
    FirstCast : IsCastable cst from to -> Castable (cst :: _) from to
    NextCast  : Castable casts from to -> Castable (_ :: casts) from to

public export
data ArgsCastable : ListOfSupportedCasts -> ListOfBasicTypes -> ListOfBasicTypes -> Type where
    ReflListCast : ArgsCastable _ args args
    DistructCast : Castable casts from to ->
                    ArgsCastable casts otherFrom otherTo ->
                    ArgsCastable casts (from :: otherFrom) (to :: otherTo)