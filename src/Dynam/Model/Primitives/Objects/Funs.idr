module Dynam.Model.Primitives.Objects.Funs

import Dynam.Model.Primitives.Base
import Dynam.Model.Primitives.Objects.Classes

import public Control.Function
import public Decidable.Equality
import public Data.Fin

public export
data VectOfFuns : (size : Nat) -> Type where
    Nil  : VectOfFuns 0
    (::) : Function -> VectOfFuns n -> VectOfFuns (S n)

public export
Biinjective Dynam.Model.Primitives.Objects.Funs.(::) where
    biinjective Refl = (Refl, Refl)

public export
DecEq (VectOfFuns dim) where
    decEq Nil Nil = Yes Refl
    decEq (x :: xs) (y :: ys) = decEqCong2 (decEq x y) (decEq xs ys)

public export
data TrueIn : (vect : VectOfBool dim) -> (idx : Fin dim) -> Type where
    Curr : TrueIn (True :: other) FZ
    Next : TrueIn other idx -> TrueIn (_ :: other) (FS idx)

public export
data AtIndex : {methods : VectOfFuns dim} ->
               (idx     : Fin dim) ->
               (args    : ListOfBasicTypes) ->
               (ret     : MaybeVoidableType) -> Type where
    [search methods idx]
    Here  : AtIndex {methods = (args ==> ret) :: xs} FZ args ret 
    There : AtIndex {methods} idx args ret -> AtIndex {methods = _ :: methods} (FS idx) args ret

