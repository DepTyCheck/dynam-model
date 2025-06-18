module Dynam.Model.Objects.Stmts

import public Dynam.Model.Objects.Exprs
import public Dynam.Model.Primitives.Objects
import public Dynam.Model.Base

import Data.List
import Data.List.Quantifiers

import Data.Fuel
import Test.DepTyCheck.Gen

import public Decidable.Equality
import public Decidable.Decidable


export infix 2 #=

public export
data Stmts : (meths : VectOfFuns dim) ->
             (clss  : ListOfClasses dim) ->
             (objs  : ListOfClasses dim) -> 
             (casts : ListOfSupportedCasts) ->
             (funs  : ListOfFunctions)  ->
             (vars  : ListOfBasicTypes) -> Type where

    NewV : (ty : BasicType) ->
           (initial : Expr meths clss objs casts funs vars ty) ->
           (cont : Stmts meths clss objs casts funs (ty :: vars)) ->
           Stmts meths clss objs casts funs vars

    NewFun : (ty : BasicType) ->
             (args : ListOfBasicTypes) ->
             (body : Stmts meths clss objs casts funs (args ++ vars)) ->
             (ret  : Expr meths clss objs casts funs vars ty) ->
             (cont : Stmts meths clss objs casts ((args ==> NonVoidable ty) :: funs) vars) ->
             Stmts meths clss objs casts funs vars

    NewProc : (args : ListOfBasicTypes) ->
              (body : Stmts meths clss objs casts funs (args ++ vars)) ->
              (cont : Stmts meths clss objs casts ((args ==> Void) :: funs) vars) ->
              Stmts meths clss objs casts funs vars
    
    NewClass : (methods : VectOfBool dim) ->
               (cont : Stmts meths (NewClass methods :: clss) objs casts funs vars) ->
               Stmts meths clss objs casts funs vars 
    
    NewObject : (cls : IndexIn clss) ->
                AtIndex cls obj =>
                (cont : Stmts meths clss (obj :: objs) casts funs vars) ->
                Stmts meths clss objs casts funs vars 

    (#=) : (lhs : IndexIn vars) ->
           AtIndex lhs ty =>
           (rhs : Expr meths clss objs casts funs vars ty) ->
           (cont : Stmts meths clss objs casts funs vars) ->
           Stmts meths clss objs casts funs vars

    Ret : Stmts meths clss objs casts funs vars

    If : (cond : Expr meths clss objs casts funs vars Boolean) ->
         (th, el : Stmts meths clss objs casts funs vars) ->
         (cont : Stmts meths clss objs casts funs vars) ->
         Stmts meths clss objs casts funs vars

    Call : {0 ty : _} ->
           (lhs : IndexIn funs) ->
           AtIndex lhs argTypes ty =>
           (args : ExprList meths clss objs casts funs vars argTypes) ->
           (cont : Stmts meths clss objs casts funs vars) ->
           Stmts meths clss objs casts funs vars

    CallMethod : {0 ty : _} ->
                 (this : IndexIn objs) ->
                 (method : Fin dim) ->
                 AtIndex this allowedMethods =>
                 TrueIn allowedMethods method => 
                 AtIndex {methods} method args ty =>
                 (actualArgs : ExprList methods clss objs casts funs vars args) ->
                 (cont : Stmts methods clss objs casts funs vars) ->
                 Stmts methods clss objs casts funs vars

    While : (cond : Expr meths clss objs casts funs vars Boolean)  ->
            (body : Stmts meths clss objs casts funs vars) ->
            (cont : Stmts meths clss objs casts funs vars) ->
            Stmts meths clss objs casts funs vars

export
genStmts : Fuel ->
           (dm : Nat) ->
           (mths : VectOfFuns dim) ->
           (css  : ListOfClasses dim) ->
           (ojs  : ListOfClasses dim) -> 
           (csts : ListOfSupportedCasts) ->
           (funcs : ListOfFunctions) ->
           (varrs : ListOfBasicTypes) ->
    Gen MaybeEmpty $ Stmts mths css ojs csts funcs varrs
