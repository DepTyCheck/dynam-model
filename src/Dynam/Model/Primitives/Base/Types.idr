module Dynam.Model.Primitives.Base.Types

import public Data.List
import public Data.List.Quantifiers

import public Decidable.Equality
import public Decidable.Decidable


public export
data BasicType : Type where
    Number  : BasicType
    Str     : BasicType
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
Biinjective Dynam.Model.Primitives.Base.Types.(::) where
    biinjective Refl = (Refl, Refl)

public export
data IndexIn : (tys : ListOfBasicTypes) -> Type where
    Here  : IndexIn $ x :: xs
    There : IndexIn xs -> IndexIn $ x :: xs

public export
data AtIndex : {xs : ListOfBasicTypes} -> (idx : IndexIn xs) -> (val : BasicType) -> Type where
    [search xs idx]
    Here'  : AtIndex {xs = val :: _} Here val
    There' : AtIndex {xs} i val -> AtIndex {xs = _ :: xs} (There i) val

public export
(++) : ListOfBasicTypes -> ListOfBasicTypes -> ListOfBasicTypes
(++) Nil list = list
(++) (x :: xs) list = x :: (xs ++ list)

public export
replace : (old : ListOfBasicTypes) -> (pos : IndexIn old) -> (new : BasicType) -> ListOfBasicTypes
replace [] _ _ = []
replace (_ :: rest) Here ty = ty :: rest
replace (curr :: rest) (There idx) ty = curr :: replace rest idx ty


public export
DecEq BasicType where
    decEq Number  Number  = Yes Refl
    decEq Number  Str     = No $ \case Refl impossible
    decEq Number  Boolean = No $ \case Refl impossible
    decEq Str     Number  = No $ \case Refl impossible
    decEq Str     Str     = Yes Refl
    decEq Str     Boolean = No $ \case Refl impossible
    decEq Boolean Number  = No $ \case Refl impossible
    decEq Boolean Str     = No $ \case Refl impossible
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
