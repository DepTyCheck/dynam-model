module Dynam.Model.Primitives.Objects.Classes

import public Data.List
import public Data.List.Quantifiers

import public Decidable.Equality
import public Decidable.Decidable

import public Dynam.Model.Base

namespace Bool

namespace BoolMonomorphic
    public export
    data VectOfBool : Nat -> Type where
        Nil  : VectOfBool 0
        (::) : Bool -> VectOfBool n -> VectOfBool (S n)

    public export
    Biinjective BoolMonomorphic.(::) where
        biinjective Refl = (Refl, Refl)
    
    public export
    DecEq (VectOfBool n) where
        decEq Nil Nil = Yes Refl
        decEq (x :: xs) (y :: ys) = decEqCong2 (decEq x y) (decEq xs ys)

public export
data Class : (dim : Nat) -> Type where
    NewClass : VectOfBool dim -> Class dim
 
public export
data ListOfClasses : (dim : Nat) -> Type where
    Nil  : ListOfClasses dim
    (::) : Class dim -> ListOfClasses dim -> ListOfClasses dim

public export
length : ListOfClasses _ -> Nat
length Nil = Z
length (_ :: xs) = S (length xs)

public export
data Contains : ListOfClasses dim -> Class dim -> Type where
    Single   : Contains (ty :: other) ty
    Multiple : Contains tys ty -> Contains (new :: tys) ty

public export
data IndexIn : ListOfClasses dim -> Type where
    Here  : IndexIn $ x :: xs
    There : IndexIn xs -> IndexIn $ x :: xs

public export
data AtIndex : {xs : ListOfClasses dim} ->
               (idx : IndexIn xs) ->
               (methods : VectOfBool dim) -> Type where
    [search xs idx]
    Here'  : AtIndex {xs = (NewClass methods) :: xs} Here methods
    There' : AtIndex {xs} i methods -> AtIndex {xs = x :: xs} (There i) methods

namespace AtIndex
    public export
    data AtIndex : {xs : ListOfClasses dim} ->
                   (idx : IndexIn xs) ->
                   (cls : Class dim) -> Type where
        [search xs idx]
        Here'  : AtIndex {xs = cls :: xs} Here cls
        There' : AtIndex {xs} i cls -> AtIndex {xs = x :: xs} (There i) cls

