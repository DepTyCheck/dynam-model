module Js.Playground.Js

import Data.List
import Data.List.Quantifiers

import Data.Fuel
import Test.DepTyCheck.Gen

import Decidable.Equality
import Decidable.Decidable


-- Supported Types
public export
data BasicType : Type where
    Number  : BasicType
    Str     : BasicType
    Boolean : BasicType

-- Available Casts
public export
record SupportedTypecast where
    constructor Typedef
    MainType : BasicType
    ConvertableTo : List BasicType


-- do we intend to omit them ?!
public export
data TypeDeclaration : BasicType -> Type where
  I : Nat    -> TypeDeclaration Number
  B : Bool   -> TypeDeclaration Boolean
  S : String -> TypeDeclaration Str

-- public export
-- data MaybeDeclare : SupportedTypes -> Type where
--     Null    : MaybeDeclare sts
--     NonNull : TypeDeclaration sts ->  MaybeDeclare sts

export
DecEq BasicType where
  decEq Number Number = Yes Refl
  decEq Str Str = Yes Refl
  decEq Boolean Boolean = Yes Refl
  decEq Number Str = No $ \case Refl impossible
  decEq Str Number = No $ \case Refl impossible
  decEq Number Boolean = No $ \case Refl impossible
  decEq Boolean Number = No $ \case Refl impossible
  decEq Boolean Str = No $ \case Refl impossible
  decEq Str Boolean = No $ \case Refl impossible

export
Eq BasicType where
  x == y = isYes $ decEq x y

export infix 1 ==>

public export
record Function where
    constructor (==>)
    From : List BasicType
    To : BasicType

-- export
-- Biinjective (==>) where
--     biinjective Refl = (Refl, Refl)

-- export
-- DecEq Function where
--     decEq (f ==> t) (f' ==> t') = decEqCong2 (decEq f f') (decEq t t')

namespace Types
  public export
  data IndexIn : List BasicType -> Type where
    Here  : IndexIn $ x :: sx
    There : IndexIn sx -> IndexIn $ x :: sx

  public export
  data AtIndex : {sx : List BasicType} -> (idx : IndexIn sx) -> BasicType -> Type where
    [search sx idx]
    Here'  : AtIndex {sx = ty :: sx} Here ty -- sx is redundant?
    There' : AtIndex {sx} i ty -> AtIndex {sx = x :: sx} (There i) ty

  public export
  data Contains : List BasicType -> BasicType -> Type where
    Single : Contains (ty :: other) ty
    Multiple : Contains tys ty -> Contains (new :: tys) ty

-- namespace Funs
--   public export
--   data IndexIn : List Function -> Type where
--       Here  : IndexIn $ x :: sx
--       There : IndexIn sx -> IndexIn $ x :: sx

--   public export
--   data AtIndex : {sx : List Function} -> (idx : IndexIn sx) -> Function -> Type where
--     [search sx idx]
--     Here'  : AtIndex {sx = sig :: sx} Here sig
--     There' : AtIndex {sx} i sig -> AtIndex {sx = x :: sx} (There i) sig

-- casts -> funs -> 
public export
data ExprList : List SupportedTypecast
             -> List Function
             -> List BasicType
             -> List BasicType
             -> Type

namespace Casts
  public export
  data IsCastable : SupportedTypecast -> BasicType -> BasicType -> Type where
      MakeCast : Contains (ConvertableTo casts) to => IsCastable casts (MainType casts) to

  public export
  data Match : List SupportedTypecast -> BasicType -> BasicType -> Type where
      FirstCasr : IsCastable cst ty to => Match (cst :: other) ty to
      NextCast  : Match casts ty to -> Match (another :: casts) ty to

-- available casts -> functions' scope -> variables' scope -> type
public export
data Expr : List SupportedTypecast -> List Function -> List BasicType -> BasicType -> Type where
    -- const _
    Const : (x : TypeDeclaration ty) -> Expr casts funs vars ty
    -- let _
    Let : (n : IndexIn vars) -> -- rename
        AtIndex n ty =>
        Expr casts funs vars ty
    -- function () => {}
    -- Func : (n : IndexIn funs) ->
    --     AtIndex n (from ==> to) =>
    --     (actualArgs : ExprList casts funs vars retType) -> -- All (..) from
    --     CastArgs actualArgs from => 
    --     Expr casts funs vars to

public export
data TypeMatch : List SupportedTypecast -> BasicType -> BasicType -> Type where
    Id : (casts : List SupportedTypecast) -> (ty : BasicType) -> TypeMatch casts ty ty
    -- DirCast : ((Typedef ty (new :: otherPoss)) :: others) -> (req : BasicType) -> TypeMatch ()
        

public export
data ExprList : List SupportedTypecast -> List Function -> List BasicType -> List BasicType -> Type where
    Nil : ExprList casts vars funs []
    (::) : Expr casts funs vars ty -> ExprList casts funs vars sx -> ExprList casts funs vars (ty :: sx)


-- include : BasicType -> List BasicType -> Bool
-- include ty Nil = False
-- include ty (ty2 :: other) = if ty == ty2 then True else include ty other
-- include ty (ty :: others) = Inside ty (ty :: others)
-- include ty (x :: others) = Inside ty others => Inside ty (x :: others)

namespace Casts
  public export
  data CastArgs : ExprList casts funs vars initialTypes -> List BasicType -> Type where
      Nil : CastArgs Nil Nil
      (::) : CastArgs others reqOthers -> (n : Expr Nil funs vars type)
              -> CastArgs (n :: others) (type :: reqOthers)
      -- ()

public export
data Stmts : (casts: List SupportedTypecast) ->
             (funs : List Function) ->
             (vars : List BasicType) ->
             (retTy : BasicType) -> Type where

  NewV : (ty : BasicType) ->
         (initial : Expr casts funs vars ty) ->
         (cont : Stmts casts funs ((::) ty vars) retTy) ->
         Stmts casts funs vars retTy

  -- NewF : (sig : Function) ->
  --        (body : Stmts funs (vars ++ sig.From) sig.To) ->
  --        (cont : Stmts (sig :: funs) vars retTy) ->
  --        Stmts funs vars retTy

  (#=) : (n : IndexIn vars) ->
         AtIndex n ty =>
         (v : Expr casts funs vars ty) ->
         (cont : Stmts casts funs vars retTy) ->
         Stmts casts funs vars retTy

--   If   : (cond : Expr funs vars Boolean) ->
--          (th, el : Stmts funs vars Boolean) -> -- FIXME: return undef
--          (cont : Stmts funs vars retTy) ->
--          Stmts funs vars retTy

--   Call : (n : IndexIn funs) ->
--          AtIndex funs n (from ==> Boolean) => -- FIXME: return undef
--          ExprList funs vars from ->
--          (cont : Stmts funs vars retTy) ->
--          Stmts funs vars retTy

--   Ret  : Expr funs vars retTy -> Stmts funs vars retTy

--   Nop  : Stmts funs vars Boolean
-- -- ----------------------------------------------------------------
-- -- -- Unify & randomise print??
-- -- --   DoWhile : (cond : Expr funs vars Boolean)  ->
-- -- --             (body : Stmts funs vars Boolean) -> -- FIXME: undef
-- -- --             (cont : Stmts funs vars retType) ->
-- -- --             Stmts funs vars retTy
    
-- --   While : (cond : Expr funs vars Boolean)  ->
-- --           (body : Stmts funs vars Boolean) -> -- FIXME: undef
-- --           (cont : Stmts funs vars retType) ->
-- --           Stmts funs vars retTy

-- --   For : (decl   : Expr funs vars decType)    ->
-- --         (cond   : Expr funs args Boolean)    ->
-- --         (update : Expr funs vars updateType) ->
-- --         (body   : Stmts funs vars Boolean)   -> -- FIXME: undef
-- --         (cont   : Stmts funs vars retType)   ->
-- --         Stmts funs vars retTy


export
genStmts : Fuel ->
           (casts : List SupportedTypecast) ->
           (funs : List Function) ->
           (vars : List BasicType) ->
           (retTy : BasicType) ->
           Gen MaybeEmpty $ Stmts casts funs vars retTy
