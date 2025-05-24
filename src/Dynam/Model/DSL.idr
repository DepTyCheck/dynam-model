module Dynam.Model.DSL

import Dynam.Model.Stmts
import Dynam.Model.Primitives

import Data.Nat
import Data.Fin


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

namespace HofDSL
    public export
    natToFin : {dim : Nat} -> (n : Nat) -> {sx : VectOfHOF dim size} -> n `LT` size => Fin size
    natToFin 0     {sx=x::sx}              = FZ
    natToFin (S k) {sx=x::sx} @{LTESucc l} = FS $ natToFin {dim} {sx} k

    public export
    fromInteger : {size : Nat} ->
                {dim : Nat} ->
                {sx : VectOfHOF dim size} ->
                (n : Integer) -> 
                (cast n `LT` size) => {- (x >= the Integer 0 = True) =>-}
                Fin size
    fromInteger n with (cast {to=Nat} n)
        _ | n' = natToFin {dim} {sx} (size `minus` S n') @{reverseLTMinus} 

namespace HotVarDSL
    public export
    natToIndexIn : (n : Nat) -> {sx : ListOfHOT dim} -> n `LT` length sx => IndexIn sx
    natToIndexIn 0     {sx=x::sx}              = Here
    natToIndexIn (S k) {sx=x::sx} @{LTESucc l} = There $ natToIndexIn k

    public export
    fromInteger : {sx : ListOfHOT dim} ->
                (n : Integer) -> 
                (cast n `LT` length sx) => {- (x >= the Integer 0 = True) =>-}
                IndexIn sx
    fromInteger n with (cast {to=Nat} n)
        _ | n' = natToIndexIn (length sx `minus` S n') @{reverseLTMinus}

namespace VarDSL
    -- public export
    -- natToIndexIn : (n : Nat) -> {ty : BasicType} -> {sx : ListOfBasicTypes} -> n `LT` length sx => IndexIn sx ty
    -- natToIndexIn 0  {ty}   {sx=ty::_}            = Here
    -- natToIndexIn (S k) {sx=x::sx} @{LTESucc l} = There $ natToIndexIn k

    -- public export
    -- fromInteger : {sx : ListOfBasicTypes} ->
    --             (n : Integer) -> 
    --             (cast n `LT` length sx) => {- (x >= the Integer 0 = True) =>-}
    --             IndexIn sx ty
    -- fromInteger n with (cast {to=Nat} n)
    --     _ | n' = natToIndexIn (length sx `minus` S n') @{reverseLTMinus}

public export %inline
(>>) : (Stmts ht' hf' hv' c' f' v' -> Stmts ht hf hv c f v) -> Stmts ht' hf' hv' c' f' v' -> Stmts ht hf hv c f v
(>>) = id

