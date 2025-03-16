module Dynam.Model.Primitives

import public Data.List
import public Data.List.Quantifiers

import public Decidable.Equality
import public Decidable.Decidable

import public Dynam.Model.Primitives.Types
import public Dynam.Model.Primitives.Casts
import public Dynam.Model.Primitives.Funs


export
DecEq Function where
    decEq (f ==> t) (f' ==> t') = decEqCong2 (decEq f f') (decEq t t')
