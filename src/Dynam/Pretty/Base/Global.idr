module Dynam.Pretty.Base.Global


import public Dynam.Pretty.Base.Utils
import public Dynam.Model.Base

import public Test.DepTyCheck.Gen
import public Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

import public Data.Alternative
import public Data.List
import public Data.Vect
import public Data.Fuel
import public Data.SortedSet
import public Data.String

%default total

public export
interface NamesRestrictions where
    reservedKeywords : SortedSet String

public export
NamesRestrictions where
    reservedKeywords = fromList
        [ "abstract", "case"  , "catch"   , "class"  , "def"    , "do"       , "else"
        , "enum"    , "export", "extends" , "false"  , "final"  , "finally"  , "for"
        , "given"   , "if"    , "implicit", "import" , "lazy"   , "match"    , "new"
        , "null"    , "object", "override", "package", "private", "protected", "return"
        , "sealed"  , "super" , "then"    , "throw"  , "trait"  , "true"     , "try"
        , "type"    , "val"   , "var"     , "while"  , "with"   , "yield"    , "as"
        , ":"       , "="     , "<-"      , "=>"     , "<:"     , ">:"       , "#"
        , "@"       , "=>>"   , "?=>"
        ]

public export
unaryOps : List String
unaryOps = ["+", "-", "!", "~"]

public export
isUnaryOp : String -> List arg -> Bool
isUnaryOp str xs = elem str unaryOps && length xs == 1

public export
rawNewName : Fuel ->
             (Fuel -> Gen MaybeEmpty String) =>
             (funs : ListOfFunctions) ->
             (vars : ListOfBasicTypes) ->
             (names : UniqNames funs vars) ->
             Gen MaybeEmpty (s ** NameIsNew funs vars names s)

export
genNewName : Fuel ->
             Gen MaybeEmpty String ->
             NamesRestrictions =>
             (funs : ListOfFunctions) ->
             (vars : ListOfBasicTypes) ->
             (names : UniqNames funs vars) ->
             Gen MaybeEmpty (s ** NameIsNew funs vars names s)
genNewName fl genStr funs vars names = do
    nn@(nm ** _) <- rawNewName fl @{const genStr} funs vars names
    if nm `contains` reservedKeywords
        then assert_total $ genNewName fl genStr funs vars names
        else pure nn

public export
namesGen : Gen0 String
namesGen = pack <$> listOf {length = choose (1, 10)} (choose ('a', 'z'))

public export
genNewVars : NamesRestrictions =>
          {funs : _} ->
          {vars : _} ->
          Fuel ->
          (newNames : Gen0 String) ->
          (extraVars : _) ->
          UniqNames funs vars ->
          Gen0 (UniqNames funs (extraVars ++ vars), List (String, BasicType))
genNewVars fl newNames Nil names = pure (names, [])
genNewVars fl newNames (v :: vs) names = do
    (nms, vts) <- genNewVars fl newNames vs names
    (nm ** _)  <- genNewName fl newNames _ _ nms
    pure (NewVar @{nms} nm, (nm, v)::vts)

public export
genRange : Integer -> List Integer
genRange max = rangeFromTo 0 max
