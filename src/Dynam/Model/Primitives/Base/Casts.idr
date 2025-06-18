module Dynam.Model.Primitives.Base.Casts

import Dynam.Model.Primitives.Base.Types

export infix 1 %=

public export
record SupportedTypecast where
    constructor (%=)
    MainType : BasicType
    ConvertableTo : BasicType

public export
data ListOfSupportedCasts : Type where
    Nil : ListOfSupportedCasts
    (::) : SupportedTypecast -> ListOfSupportedCasts -> ListOfSupportedCasts

public export
data Castable : ListOfSupportedCasts -> (from : BasicType) -> (to : BasicType) -> Type where
    ReflCast  : Castable _ ty ty
    FirstCast : Castable ((from %= to) :: _) from to
    NextCast  : Castable casts from to -> Castable (_ :: casts) from to

