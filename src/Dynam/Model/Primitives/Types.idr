module Dynam.Model.Primitives.Types

import public Data.List
import public Data.List.Quantifiers

import public Decidable.Equality
import public Decidable.Decidable


public export
data BasicType : (isVoid : Bool) -> Type where
    Void    : BasicType True
    Number  : BasicType False
    -- Str     : BasicType
    Boolean : BasicType False

public export
data ListOfBasicTypes : Type where
    Nil : ListOfBasicTypes
    (::) : BasicType False -> ListOfBasicTypes -> ListOfBasicTypes

public export
Biinjective Dynam.Model.Primitives.Types.(::) where
    biinjective Refl = (Refl, Refl)

public export
data IndexIn : ListOfBasicTypes -> Type where
    Here  : IndexIn $ x :: sx
    There : IndexIn sx -> IndexIn $ x :: sx

||| @ idx Index in ListOfBasicTypes
||| @ ty Return type
public export
data AtIndex : {sx : ListOfBasicTypes} -> (idx : IndexIn sx) -> (ty : BasicType False) -> Type where
    [search sx idx]
    Here'  : AtIndex {sx = ty :: sx} Here ty
    There' : AtIndex {sx} i ty -> AtIndex {sx = x :: sx} (There i) ty

public export
data Contains : ListOfBasicTypes -> BasicType False -> Type where
    Single : Contains (ty :: other) ty
    Multiple : Contains tys ty -> Contains (new :: tys) ty

public export
length : ListOfBasicTypes -> Nat
length [] = Z
length (_ :: sx) = S (length sx)

public export
(.length) : ListOfBasicTypes -> Nat
(.length) = length



public export
data TypeDeclaration : BasicType isVoid -> Type where
    I : Nat    -> TypeDeclaration Number
    B : Bool   -> TypeDeclaration Boolean
    -- S : String -> TypeDeclaration Str

public export
DecEq (BasicType isVoid) where
    decEq Number  Number  = Yes Refl
    -- decEq Number  Str     = No $ \case Refl impossible
    decEq Number  Boolean = No $ \case Refl impossible
    -- decEq Str     Number  = No $ \case Refl impossible
    -- decEq Str     Str     = Yes Refl
    -- decEq Str     Boolean = No $ \case Refl impossible
    decEq Boolean Number  = No $ \case Refl impossible
    -- decEq Boolean Str     = No $ \case Refl impossible
    decEq Boolean Boolean = Yes Refl

    decEq Void    Void    = Yes Refl


public export
Eq (BasicType isVoid) where
    x == y = isYes $ decEq x y

public export
DecEq ListOfBasicTypes where
    decEq [] [] = Yes Refl
    decEq (x :: xs) [] = No $ \case Refl impossible
    decEq [] (x :: xs) = No $ \case Refl impossible
    decEq (x :: xs) (y :: ys) = decEqCong2 (decEq x y) (decEq xs ys)

public export
Eq (ListOfBasicTypes) where
    x == y = isYes $ decEq x y