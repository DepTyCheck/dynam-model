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

public export
data Stmts : (hod : HOData dim) ->
             (casts : ListOfSupportedCasts) ->
             (funs  : ListOfFunctions)  ->
             (vars  : ListOfBasicTypes) -> Type where

    NewV : (ty : BasicType) ->
           (initial : Expr hod casts funs vars ty) ->
           (cont : Stmts hod casts funs (ty :: vars)) ->
           Stmts hod casts funs vars

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
    (#=) : (lhs : IndexIn vars) ->
           AtIndex lhs ty =>
           (rhs : Expr hod casts funs vars ty) ->
           (cont : Stmts hod casts funs vars) ->
           Stmts hod casts funs vars

    Ret : Stmts hod casts funs vars

--     If : (cond : Expr hofs hots hotvars casts funs vars Boolean) ->
--          (th, el : Stmts hofs hots hotvars casts funs vars) ->
--          (cont : Stmts hofs hots hotvars casts funs vars) ->
--          Stmts hofs hots hotvars casts funs vars

--     Call : {ty : _} ->
--            (lhs : IndexIn funs argTypes ty) ->
--        --     AtIndex lhs argTypes ty =>
--            (args : ExprList hofs hots hotvars casts funs vars argTypes) ->
--            (cont : Stmts hofs hots hotvars casts funs vars) ->
--            Stmts hofs hots hotvars casts funs vars

    While : (cond : Expr hod casts funs vars Boolean)  ->
            (body : Stmts hod casts funs vars) ->
            (cont : Stmts hod casts funs vars) ->
            Stmts hod casts funs vars

export
genStmts : Fuel ->
           {dim : Nat} ->
           (hd : HOData dim) ->
           (csts : ListOfSupportedCasts) ->
           (funcs : ListOfFunctions) ->
           (varrs : ListOfBasicTypes) ->
    Gen MaybeEmpty $ Stmts hd csts funcs varrs
