module Dynam.Model.Primitives.Funs

import Dynam.Model.Primitives.Types


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
data IndexIn : (list : ListOfFunctions) -> (args : ListOfBasicTypes) -> (resTy : MaybeVoidableType) -> Type where
    Here  : IndexIn ((args ==> resTy) :: _) args resTy
    There : IndexIn xs args resTy -> IndexIn (_ :: xs) args resTy

-- public export
-- data AtIndex : {sx : ListOfFunctions}    ->
--                (idx : IndexIn sx)        ->
--                (from : ListOfBasicTypes) -> 
--                (to : MaybeVoidableType) -> Type where
--     [search sx idx]
--     Here'  : {voidable : Bool} -> {to : MaybeVoidableType} -> AtIndex {sx = (from ==> to) :: sx} Here from to
--     There' : AtIndex {sx} i from to -> AtIndex {sx = x :: sx} (There i) from to

-- public export
-- data Contains : ListOfFunctions -> Function -> Type where
--     Single : Contains (fun :: _) fun
--     Multiple : Contains funs fun -> Contains (_ :: funs) fun

public export
length : ListOfFunctions -> Nat
length [] = Z
length (_ :: sx) = S (length sx)

public export
(.length) : ListOfFunctions -> Nat
(.length) = length