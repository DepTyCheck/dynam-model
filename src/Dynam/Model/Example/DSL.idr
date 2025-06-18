module Dynam.Model.Example.DSL

import public Dynam.Model.Base
import public Dynam.Model.Objects

import public Data.Nat
import public Data.Fin


namespace LengthTY
    public export
    length : ListOfBasicTypes -> Nat
    length [] = Z
    length (_ :: sx) = S (length sx)

    public export
    (.length) : ListOfBasicTypes -> Nat
    (.length) = length

namespace LengthFN
    public export
    length : ListOfFunctions -> Nat
    length [] = Z
    length (_ :: sx) = S (length sx)

    public export
    (.length) : ListOfFunctions -> Nat
    (.length) = length


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
                (cast n `LT` length sx) =>
                IndexIn sx
    fromInteger n with (cast {to=Nat} n)
        _ | n' = natToIndexIn (length sx `minus` S n') @{reverseLTMinus}

namespace MethodDSL
    public export
    natToFin : {xs : VectOfFuns dim} -> (n : Nat) -> n `LT` dim => Fin dim
    natToFin              {xs = x :: xs} 0     = FZ
    natToFin @{LTESucc l} {xs = x :: xs} (S k) = FS $ natToFin {xs} k

    public export
    fromInteger : {dim : Nat} ->
                  {xs : VectOfFuns dim} ->
                  (n : Integer) -> 
                  (cast n `LT` dim) =>
                  Fin dim
    fromInteger n with (cast {to=Nat} n)
        _ | n' = natToFin {xs} (dim `minus` S n') @{reverseLTMinus} 

namespace ClassDSL
    public export
    natToIndexIn : (n : Nat) -> {sx : ListOfClasses dim} -> n `LT` length sx => IndexIn sx
    natToIndexIn 0     {sx=x::sx}              = Here
    natToIndexIn (S k) {sx=x::sx} @{LTESucc l} = There $ natToIndexIn k

    public export
    fromInteger : {sx : ListOfClasses dim} ->
                (n : Integer) -> 
                (cast n `LT` length sx) =>
                IndexIn sx
    fromInteger n with (cast {to=Nat} n)
        _ | n' = natToIndexIn (length sx `minus` S n') @{reverseLTMinus}

    public export %inline
    (>>) : (Stmts m' t' o' c' f' v' -> Stmts m t o c f v) -> Stmts m' t' o' c' f' v' -> Stmts m t o c f v
    (>>) = id

namespace VarDSL
    public export
    natToIndexIn : (n : Nat) -> {sx : ListOfBasicTypes} -> n `LT` length sx => IndexIn sx
    natToIndexIn 0     {sx=ty::_}              = Here
    natToIndexIn (S k) {sx=x::sx} @{LTESucc l} = There $ natToIndexIn k

    public export
    fromInteger : {sx : ListOfBasicTypes} ->
                (n : Integer) -> 
                (cast n `LT` length sx) =>
                IndexIn sx
    fromInteger n with (cast {to=Nat} n)
        _ | n' = natToIndexIn (length sx `minus` S n') @{reverseLTMinus}

namespace DeclDSL
    public export
    fromInteger : (n : Integer) -> BasicType
    fromInteger n = Number

    public export
    fromString : (s : String) -> BasicType
    fromString s = Str

    public export
    True : BasicType
    True = Boolean

    public export
    False : BasicType
    False = Boolean


public export %inline
(>>) : (Stmts c' f' v' -> Stmts c f v) -> Stmts c' f' v' -> Stmts c f v
(>>) = id

