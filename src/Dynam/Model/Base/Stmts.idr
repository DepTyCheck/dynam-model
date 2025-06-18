module Dynam.Model.Base.Stmts

import public Dynam.Model.Base.Exprs

import Data.List
import Data.List.Quantifiers

import Data.Fuel
import Test.DepTyCheck.Gen

import public Decidable.Equality
import public Decidable.Decidable


export infix 2 #=

public export
data Stmts : (casts : ListOfSupportedCasts) ->
             (funs  : ListOfFunctions)  ->
             (vars  : ListOfBasicTypes) -> Type where

    NewV : (ty : BasicType) ->
           (initial : Expr casts funs vars ty) ->
           (cont : Stmts casts funs (ty :: vars)) ->
           Stmts casts funs vars

    NewFun : (ty : BasicType) ->
             (args : ListOfBasicTypes) ->
             (body : Stmts casts funs (args ++ vars)) ->
             (ret  : Expr casts funs vars ty) ->
             (cont : Stmts casts ((args ==> NonVoidable ty) :: funs) vars) ->
             Stmts casts funs vars

    NewProc : (args : ListOfBasicTypes) ->
              (body : Stmts casts funs (args ++ vars)) ->
              (cont : Stmts casts ((args ==> Void) :: funs) vars) ->
              Stmts casts funs vars

    (#=) : (lhs : IndexIn vars) ->
           AtIndex lhs ty =>
           (rhs : Expr casts funs vars ty) ->
           (cont : Stmts casts funs vars) ->
           Stmts casts funs vars

    Ret : Stmts casts funs vars

    If : (cond : Expr casts funs vars Boolean) ->
         (th, el : Stmts casts funs vars) ->
         (cont : Stmts casts funs vars) ->
         Stmts casts funs vars

    Call : {0 ty : _} ->
           (lhs : IndexIn funs) ->
           AtIndex lhs argTypes ty =>
           (args : ExprList casts funs vars argTypes) ->
           (cont : Stmts casts funs vars) ->
           Stmts casts funs vars

    While : (cond : Expr casts funs vars Boolean)  ->
            (body : Stmts casts funs vars) ->
            (cont : Stmts casts funs vars) ->
            Stmts casts funs vars

export
genStmts : Fuel ->
           (csts : ListOfSupportedCasts) ->
           (funcs : ListOfFunctions)  ->
           (varrs : ListOfBasicTypes) ->
           Gen MaybeEmpty $ Stmts csts funcs varrs
