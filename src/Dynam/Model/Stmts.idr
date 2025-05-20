module Dynam.Model.Stmts

import public Dynam.Model.Primitives
import public Dynam.Model.Primitives.HighOrder
import public Dynam.Model.Exprs

import Data.List
import Data.List.Quantifiers

import Data.Fuel
import Test.DepTyCheck.Gen

import public Decidable.Equality
import public Decidable.Decidable


export infix 2 #=


-- (dim   : Nat) ->
--             (hofs  : VectOfHOF dim dim) ->
--             (hots  : ListOfHOT dim) ->
--             (hotvars : ListOfHOT dim) ->
--             (casts : ListOfSupportedCasts) ->
--             (funs  : ListOfFunctions)  ->
--             (vars  : ListOfBasicTypes) ->

public export
data Stmts : (hofs  : VectOfHOF dim dim) ->
             (hots  : ListOfHOT dim) ->
             (hotvars : ListOfHOT dim) ->
             (casts : ListOfSupportedCasts) ->
             (funs  : ListOfFunctions)  ->
             (vars  : ListOfBasicTypes) -> Type where

    NewV : (ty : BasicType) ->
           (initial : Expr hofs hots hotvars casts funs vars ty) ->
           (cont : Stmts hofs hots hotvars casts funs (ty :: vars)) ->
           Stmts hofs hots hotvars casts funs vars

    -- NewHotVar : (tyMeta : IndexIn hots) ->
    --        AtIndex hots tyMeta ty =>
    --        (cont : Stmts hofs hots (ty :: hotvars) casts funs vars) ->
    --        Stmts hofs hots hotvars casts funs vars

    --   NewF : (sig : Function) ->
    --          (body : Stmts funs (vars ++ sig.From) sig.To) ->
    --          (cont : Stmts (sig :: funs) vars retTy) ->
    --          Stmts funs vars retTy

    ||| lhs #= rhs
    ||| @ lhs Variable that has already been defined
    ||| @ rhs Expression 
    (#=) : {0 ty : BasicType} ->
           (lhs : IndexIn vars) ->
           AtIndex lhs ty =>
           (rhs : Expr hofs hots hotvars casts funs vars ty) ->
           (cont : Stmts hofs hots hotvars casts funs vars) ->
           Stmts hofs hots hotvars casts funs vars

    Ret : Stmts hofs hots hotvars casts funs vars

    If : (cond : Expr hofs hots hotvars casts funs vars Boolean) ->
         (th, el : Stmts hofs hots hotvars casts funs vars) ->
         (cont : Stmts hofs hots hotvars casts funs vars) ->
         Stmts hofs hots hotvars casts funs vars

    Call : (lhs : IndexIn funs) ->
           AtIndex lhs argTypes Void =>
           (args : ExprList hofs hots hotvars casts funs vars argTypes) ->
           (cont : Stmts hofs hots hotvars casts funs vars) ->
           Stmts hofs hots hotvars casts funs vars

    While : (cond : Expr hofs hots hotvars casts funs vars Boolean)  ->
            (body : Stmts hofs hots hotvars casts funs vars) ->
            (cont : Stmts hofs hots hotvars casts funs vars) ->
            Stmts hofs hots hotvars casts funs vars

export
genStmts : Fuel ->
           {dm : Nat} ->
           (hfs  : VectOfHOF dm dm) ->
           (hts  : ListOfHOT dm) ->
           (hotvrs : ListOfHOT dm) ->
           (csts : ListOfSupportedCasts) ->
           (funcs : ListOfFunctions) ->
           (varrs : ListOfBasicTypes) ->
    Gen MaybeEmpty $ Stmts hfs hts hotvrs csts funcs varrs
