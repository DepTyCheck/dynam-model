module Dynam.Pretty.Objects.Global

import public Dynam.Pretty.Base
import public Dynam.Pretty.Objects.Utils
import public Dynam.Model.Objects


import public Test.DepTyCheck.Gen
import public Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

import public Data.Alternative
import public Data.List
import public Data.Fuel
import public Data.SortedSet

%default total

public export
rawNewName : Fuel ->
             (Fuel -> Gen MaybeEmpty String) =>
             (meths : VectOfFuns dim)    ->
             (clss  : ListOfClasses dim) ->
             (objs  : ListOfClasses dim) ->
             (funs  : ListOfFunctions)   ->
             (vars  : ListOfBasicTypes)  ->
             (names : UniqNames meths clss objs funs vars) ->
             Gen MaybeEmpty (s ** NameIsNew meths clss objs funs vars names s)

export
genNewName : Fuel ->
             Gen MaybeEmpty String ->
             NamesRestrictions =>
             (meths : VectOfFuns dim)    ->
             (clss  : ListOfClasses dim) ->
             (objs  : ListOfClasses dim) ->
             (funs  : ListOfFunctions)   ->
             (vars  : ListOfBasicTypes)  ->
             (names : UniqNames meths clss objs funs vars) ->
             Gen MaybeEmpty (s ** NameIsNew meths clss objs funs vars names s)
genNewName fl genStr meths clss objs funs vars names = do
    nn@(nm ** _) <- rawNewName fl @{const genStr} meths clss objs funs vars names
    if nm `contains` reservedKeywords
        then assert_total $ genNewName fl genStr meths clss objs funs vars names
        else pure nn

public export
genNewVars : NamesRestrictions =>
          {meths : _} -> {clss  : _} -> {objs  : _} -> {funs  : _} -> {vars  : _} ->
          Fuel ->
          (newNames : Gen0 String) ->
          (extraVars : _) ->
          UniqNames meths clss objs funs vars ->
          Gen0 (UniqNames meths clss objs funs (extraVars ++ vars), List (String, BasicType))
genNewVars fl newNames Nil names = pure (names, [])
genNewVars fl newNames (v :: vs) names = do
    (nms, vts) <- genNewVars fl newNames vs names
    (nm ** _)  <- genNewName fl newNames _ _ _ _ _ nms
    pure (NewVar @{nms} nm, (nm, v)::vts)
