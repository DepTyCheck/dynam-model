module Dynam.Model.Primitives.Objects.Casts

import Dynam.Model.Primitives.Objects.Classes


data Implies : {dim : Nat} -> (lhs : VectOfBool dim) -> (rhs : VectOfBool dim) -> Type where
    Null   : Nil `Implies` Nil
    True   : xs `Implies` ys -> (True :: xs)  `Implies` (True :: ys)
    False  : xs `Implies` ys -> (False :: xs) `Implies` (_ :: ys)

public export
data Castable : {dim : Nat} -> (from : Class dim) -> (to : Class dim) -> Type where
    ReflCast  : Castable ty ty
    NonRefl   : {lhs : VectOfBool dim} ->
                {rhs : VectOfBool dim} ->
                rhs `Implies` lhs  ->
                Castable (NewClass lhs) (NewClass rhs)
