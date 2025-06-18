module Dynam.Model.Primitives.Base.Funs

import Dynam.Model.Primitives.Base.Types


export infix 1 ==>

public export
record Function where
    constructor (==>)
    From : ListOfBasicTypes
    To : MaybeVoidableType

public export
Biinjective (==>) where
    biinjective Refl = (Refl, Refl)

public export
Injective (==>) where
    injective Refl = Refl

public export
data ListOfFunctions : Type where
    Nil : ListOfFunctions
    (::) : Function -> ListOfFunctions -> ListOfFunctions

public export
data IndexIn : (list : ListOfFunctions) -> Type where
    Here  : IndexIn (x :: _)
    There : IndexIn xs -> IndexIn (_ :: xs)

public export
data AtIndex : {xs : ListOfFunctions}    ->
               (idx : IndexIn xs)        ->
               (from : ListOfBasicTypes) -> 
               (to : MaybeVoidableType) -> Type where
    [search xs idx]
    Here'  : AtIndex {xs = (from ==> to) :: xs} Here from to
    There' : AtIndex {xs} i from to -> AtIndex {xs = x :: xs} (There i) from to
