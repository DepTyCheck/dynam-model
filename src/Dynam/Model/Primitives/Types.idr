module Dynam.Model.Primitives.Types

import public Data.List
import public Data.List.Quantifiers

import public Decidable.Equality
import public Decidable.Decidable


public export
data BasicType : Type where
    Number  : BasicType
    -- Str     : BasicType
    Boolean : BasicType

public export
data MaybeVoidableType : Type where
    Void : MaybeVoidableType
    NonVoidable : BasicType -> MaybeVoidableType

public export
data ListOfBasicTypes : Type where
    Nil : ListOfBasicTypes
    (::) : BasicType -> ListOfBasicTypes -> ListOfBasicTypes

public export
Biinjective Dynam.Model.Primitives.Types.(::) where
    biinjective Refl = (Refl, Refl)

-- public export
-- data IndexIn : (list : ListOfBasicTypes) -> (ty : BasicType) -> Type where
--     Here  : IndexIn (ty :: xs) ty
--     There : IndexIn xs ty -> IndexIn (_ :: xs) ty

public export
data IndexIn : ListOfBasicTypes -> Type where
    Here  : IndexIn $ x :: sx
    There : IndexIn sx -> IndexIn $ x :: sx

||| @ idx Index in ListOfBasicTypes
||| @ ty Return type
public export
data AtIndex : {xs : ListOfBasicTypes} -> (idx : IndexIn xs) -> (val : BasicType) -> Type where
    [search xs idx]
    Here'  : AtIndex {xs = val :: _} Here val
    There' : AtIndex {xs} i val -> AtIndex {xs = _ :: xs} (There i) val

public export
data Contains : ListOfBasicTypes -> BasicType -> Type where
    Single   : Contains (ty :: other) ty
    Multiple : Contains tys ty -> Contains (new :: tys) ty

public export
length : ListOfBasicTypes -> Nat
length [] = Z
length (_ :: sx) = S (length sx)

public export
(.length) : ListOfBasicTypes -> Nat
(.length) = length



public export
data TypeDeclaration : BasicType -> Type where
    I : Nat    -> TypeDeclaration Number
    B : Bool   -> TypeDeclaration Boolean
    -- S : String -> TypeDeclaration Str

public export
DecEq BasicType where
    decEq Number  Number  = Yes Refl
    -- decEq Number  Str     = No $ \case Refl impossible
    decEq Number  Boolean = No $ \case Refl impossible
    -- decEq Str     Number  = No $ \case Refl impossible
    -- decEq Str     Str     = Yes Refl
    -- decEq Str     Boolean = No $ \case Refl impossible
    decEq Boolean Number  = No $ \case Refl impossible
    -- decEq Boolean Str     = No $ \case Refl impossible
    decEq Boolean Boolean = Yes Refl

public export
[nvoid] Injective (\ty => NonVoidable ty) where
    injective Refl = Refl

public export
DecEq MaybeVoidableType where
    decEq Void Void = Yes Refl
    decEq (NonVoidable ty1) (NonVoidable ty2) = decEqCong @{nvoid} $ decEq ty1 ty2
    decEq Void (NonVoidable _) = No $ \case Refl impossible
    decEq (NonVoidable _) Void = No $ \case Refl impossible

public export
DecEq ListOfBasicTypes where
    decEq [] [] = Yes Refl
    decEq (x :: xs) [] = No $ \case Refl impossible
    decEq [] (x :: xs) = No $ \case Refl impossible
    decEq (x :: xs) (y :: ys) = decEqCong2 (decEq x y) (decEq xs ys)
