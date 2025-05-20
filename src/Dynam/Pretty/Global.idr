module Dynam.Pretty.Global

import public Dynam.Pretty.Utils

import public Dynam.Model.Stmts
import public Dynam.Model.Primitives


import public Test.DepTyCheck.Gen
import public Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

import public Data.Alternative
import public Data.List
import public Data.Fuel
import public Data.SortedSet

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
        , "type"    , "val"   , "var"     , "while"  , "with"   , "yield"
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
