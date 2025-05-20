module Dynam.Model.Primitives.HighOrder.Casts

import Dynam.Model.Primitives.HighOrder.Types


data Implies : {dim : Nat} -> (lhs : VectOfBool dim) -> (rhs : VectOfBool dim) -> Type where
    Null   : Nil `Implies` Nil
    True   : xs `Implies` ys -> (True :: xs)  `Implies` (True :: ys)
    False  : xs `Implies` ys -> (False :: xs) `Implies` (_ :: ys)

public export
data Castable : {dim : Nat} -> (from : HighOrderType dim) -> (to : HighOrderType dim) -> Type where
    ReflCast  : Castable ty ty
    NonRefl   : {lhs : VectOfBool dim} ->
                {rhs : VectOfBool dim} ->
                rhs `Implies` lhs  ->
                Castable (HasMethods lhs) (HasMethods rhs)
