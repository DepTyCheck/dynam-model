module Dynam.Model.Main

import public Dynam.Model.Primitives
import public Dynam.Model.Exprs

import Data.List
import Data.List.Quantifiers

import Data.Fuel
import Test.DepTyCheck.Gen

import public Decidable.Equality
import public Decidable.Decidable
import public Dynam.Run.CastGens


export infix 2 #=

public export
data Stmts : (casts : ListOfSupportedCasts) ->
             (funs  : ListOfFunctions) ->
             (vars  : ListOfBasicTypes) ->
             (retTy : BasicType True) -> Type where -- RM retTy?

  NewV : (ty : BasicType False) ->
         (initial : Expr casts funs vars ty) ->
         (cont : Stmts casts funs ((::) ty vars) retTy) ->
         Stmts casts funs vars retTy

--   NewF : (sig : Function) ->
--          (body : Stmts funs (vars ++ sig.From) sig.To) ->
--          (cont : Stmts (sig :: funs) vars retTy) ->
--          Stmts funs vars retTy

  ||| lhs #= rhs
  ||| @ lhs Variable that has already been defined
  ||| @ rhs Expression 
  (#=) : {lhsTy : BasicType False} ->
         {rhsTy : BasicType False} ->
         (lhs : IndexIn vars) ->
         AtIndex lhs lhsTy =>
         (rhs : Expr casts funs vars rhsTy) ->
         Castable casts rhsTy lhsTy =>
         (cont : Stmts casts funs vars retTy) ->
         Stmts casts funs vars retTy

  Ret : Stmts casts funs vars Void

  If   : (cond : Expr casts funs vars Boolean) ->
         (th, el : Stmts casts funs vars Void) ->
         (cont : Stmts casts funs vars retTy) ->
         Stmts casts funs vars retTy


--   Call : (n : IndexIn funs) ->
--          AtIndex n (argTypes ==> Void) =>
--          ExprList casts funs vars retTypes ->
--          ArgsCastable casts retTypes argTypes =>
--          (cont : Stmts casts funs vars retTy) ->
--          Stmts casts funs vars retTy

        --  (n : IndexIn funs) ->
        -- AtIndex n (argTypes ==> Void) =>
        -- (actualArgs : ExprList casts funs vars retTypes) ->
        -- ArgsCastable casts retTypes argTypes => 
        -- Expr casts funs vars to  

-- ----------------------------------------------------------------
-- -- Unify & randomise print??
-- --   DoWhile : (cond : Expr funs vars Boolean)  ->
-- --             (body : Stmts funs vars Boolean) -> -- FIXME: undef
-- --             (cont : Stmts funs vars retType) ->
-- --             Stmts funs vars retTy
    
--   While : (cond : Expr casts funs vars Boolean)  ->
--           (body : Stmts casts funs vars Void) -> -- FIXME: undef
--           (cont : Stmts casts funs vars retTy) ->
--           Stmts casts funs vars retTy

-- --   For : (decl   : Expr funs vars decType)    ->
-- --         (cond   : Expr funs args Boolean)    ->
-- --         (update : Expr funs vars updateType) ->
-- --         (body   : Stmts funs vars Boolean)   -> -- FIXME: undef
-- --         (cont   : Stmts funs vars retType)   ->
-- --         Stmts funs vars retTy


export
genStmts' : Fuel ->
           (csts : ListOfSupportedCasts) ->
           (funcs : ListOfFunctions) ->
           (varrs : ListOfBasicTypes) ->
           (rettTy : BasicType True) ->
           (Fuel -> (tys : ListOfBasicTypes) -> (ty : BasicType False) -> Gen MaybeEmpty (Contains tys ty)) =>
           (Fuel -> (cast : SupportedTypecast) -> (from : BasicType False) -> (to : BasicType False) -> Gen MaybeEmpty (IsCastable cast from to)) =>
           (Fuel -> (casts : ListOfSupportedCasts) -> (from : BasicType False) -> (to : BasicType False) -> Gen MaybeEmpty (Castable casts from to)) =>
           (Fuel -> (casts : ListOfSupportedCasts) -> (froms : ListOfBasicTypes) -> (tos : ListOfBasicTypes) -> Gen MaybeEmpty (ArgsCastable casts froms tos)) =>
           (Fuel -> (casts : ListOfSupportedCasts) -> (funs : ListOfFunctions) -> (vars : ListOfBasicTypes) -> (resTy : BasicType False) -> Gen MaybeEmpty (Expr casts funs vars resTy)) =>
           (Fuel -> (casts : ListOfSupportedCasts) -> (funs : ListOfFunctions) -> (vars : ListOfBasicTypes) -> (resTys : ListOfBasicTypes) -> Gen MaybeEmpty (ExprList casts funs vars resTys)) =>
           Gen MaybeEmpty $ Stmts csts funcs varrs rettTy

export
genStmts : Fuel ->
           (casts : ListOfSupportedCasts) ->
           (funs : ListOfFunctions) ->
           (vars : ListOfBasicTypes) ->
           (retTy : BasicType True) ->
           Gen MaybeEmpty $ Stmts casts funs vars retTy
genStmts fl casts funs vars retTy = genStmts' @{genContains} @{genIsCastable} @{genCastable} @{genArgsCastable} @{genExpr'} @{genExprList} fl casts funs vars retTy
