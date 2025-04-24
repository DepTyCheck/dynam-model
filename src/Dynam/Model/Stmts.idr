module Dynam.Model.Stmts

import public Dynam.Model.Primitives
import public Dynam.Model.Exprs

import Data.List
import Data.List.Quantifiers

import Data.Fuel
import Test.DepTyCheck.Gen

import public Decidable.Equality
import public Decidable.Decidable
-- import public Dynam.Run.CastGens


export infix 2 #=

public export
data Stmts : (casts : ListOfSupportedCasts) ->
             (funs  : ListOfFunctions) ->
             (vars  : ListOfBasicTypes) -> Type where -- RM retTy?

  NewV : (ty : BasicType) ->
         (initial : Expr casts funs vars ty) ->
         (cont : Stmts casts funs (ty :: vars)) ->
         Stmts casts funs vars

--   NewF : (sig : Function) ->
--          (body : Stmts funs (vars ++ sig.From) sig.To) ->
--          (cont : Stmts (sig :: funs) vars retTy) ->
--          Stmts funs vars retTy

  ||| lhs #= rhs
  ||| @ lhs Variable that has already been defined
  ||| @ rhs Expression 
  (#=) : {ty : BasicType} ->
         (lhs : IndexIn vars) ->
         AtIndex lhs ty =>
         (rhs : Expr casts funs vars ty) ->
         (cont : Stmts casts funs vars) ->
         Stmts casts funs vars

  Ret : Stmts casts funs vars

  If   : (cond : Expr casts funs vars Boolean) ->
         (th, el : Stmts casts funs vars) ->
         (cont : Stmts casts funs vars) ->
         Stmts casts funs vars


  Call : (lhs : IndexIn funs) ->
         AtIndex lhs argTypes resTy =>
         (args : ExprList casts funs vars argTypes) ->
         (cont : Stmts casts funs vars) ->
         Stmts casts funs vars

-- ----------------------------------------------------------------

  While : (cond : Expr casts funs vars Boolean)  ->
          (body : Stmts casts funs vars) ->
          (cont : Stmts casts funs vars) ->
          Stmts casts funs vars

export
genStmts' : Fuel ->
           (csts : ListOfSupportedCasts) ->
           (funcs : ListOfFunctions) ->
           (varrs : ListOfBasicTypes) ->
       --     (Fuel -> (tys : ListOfBasicTypes) -> (ty : BasicType False) -> Gen MaybeEmpty (Contains tys ty)) =>
       --     (Fuel -> (cast : SupportedTypecast) -> (from : BasicType False) -> (to : BasicType False) -> Gen MaybeEmpty (IsCastable cast from to)) =>
       --     (Fuel -> (casts : ListOfSupportedCasts) -> (from : BasicType False) -> (to : BasicType False) -> Gen MaybeEmpty (Castable casts from to)) =>
       --     (Fuel -> (casts : ListOfSupportedCasts) -> (froms : ListOfBasicTypes) -> (tos : ListOfBasicTypes) -> Gen MaybeEmpty (ArgsCastable casts froms tos)) =>
       --     (Fuel -> (casts : ListOfSupportedCasts) -> (funs : ListOfFunctions) -> (vars : ListOfBasicTypes) -> (resTy : BasicType False) -> Gen MaybeEmpty (Expr casts funs vars resTy)) =>
       --     (Fuel -> (casts : ListOfSupportedCasts) -> (funs : ListOfFunctions) -> (vars : ListOfBasicTypes) -> (resTys : ListOfBasicTypes) -> Gen MaybeEmpty (ExprList casts funs vars resTys)) =>
           Gen MaybeEmpty $ Stmts csts funcs varrs

export
genStmts : Fuel ->
           (casts : ListOfSupportedCasts) ->
           (funs : ListOfFunctions) ->
           (vars : ListOfBasicTypes) ->
           Gen MaybeEmpty $ Stmts casts funs vars
genStmts fl casts funs vars = genStmts' fl casts funs vars
