module Dynam.Model.DSL

import Dynam.Model.Stmts
import Dynam.Model.Primitives

import Data.Nat


namespace DSLUtils
    public export
    weakenLT : {n : _} -> n `LT` m -> n `LTE` m
    weakenLT {n=Z}   (LTESucc x) = LTEZero
    weakenLT {n=S n} (LTESucc x) = LTESucc $ weakenLT x

    public export
    reverseLTMinus : {m, n : Nat} -> n `LT` m => (m `minus` S n) `LT` m
    reverseLTMinus {n = Z} {m=S m} = rewrite minusZeroRight m in reflexive
    reverseLTMinus {m=S m} {n=S n} @{LTESucc xx} = LTESucc $ weakenLT reverseLTMinus

namespace FunDSL
    public export
    natToIndexIn : (n : Nat) -> {sx : ListOfFunctions} -> n `LT` length sx => IndexIn sx
    natToIndexIn 0     {sx=x::sx}              = Here
    natToIndexIn (S k) {sx=x::sx} @{LTESucc l} = There $ natToIndexIn k

    public export
    fromInteger : {sx : ListOfFunctions} ->
                (n : Integer) -> 
                (cast n `LT` length sx) => {- (x >= the Integer 0 = True) =>-}
                IndexIn sx
    fromInteger n with (cast {to=Nat} n)
        _ | n' = natToIndexIn (length sx `minus` S n') @{reverseLTMinus}

namespace VarDSL
    public export
    natToIndexIn : (n : Nat) -> {sx : ListOfBasicTypes} -> n `LT` length sx => IndexIn sx
    natToIndexIn 0     {sx=x::sx}              = Here
    natToIndexIn (S k) {sx=x::sx} @{LTESucc l} = There $ natToIndexIn k

    public export
    fromInteger : {sx : ListOfBasicTypes} ->
                (n : Integer) -> 
                (cast n `LT` length sx) => {- (x >= the Integer 0 = True) =>-}
                IndexIn sx
    fromInteger n with (cast {to=Nat} n)
        _ | n' = natToIndexIn (length sx `minus` S n') @{reverseLTMinus}

public export %inline
(>>) : (Stmts c' f' v' -> Stmts c f v) -> Stmts c' f' v' -> Stmts c f v
(>>) = id

