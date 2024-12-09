module Js.Playground.Demo.Pretty

import Js.Playground.Js
-- import public Js.Playground.Pretty

import Test.DepTyCheck.Gen
import public Text.PrettyPrint.Bernardy
import System.Random.Pure.StdGen
import Deriving.DepTyCheck.Util.Alternative
import Data.List
import Data.Fuel
import public Data.So
import public Data.SortedSet

%default total

public export
data UniqNames : (funs : List Function) -> (vars : List BasicType) -> Type
public export
data NameIsNew : (funs : List Function) -> (vars : List BasicType) -> UniqNames funs vars -> String -> Type

data UniqNames : (funs : List Function) -> (vars : List BasicType) -> Type where
  [search funs vars]
  Empty   : UniqNames [] []
  JustNew : (ss : UniqNames funs vars) => (s : String) -> (0 _ : NameIsNew funs vars ss s) => UniqNames funs vars
  NewFun  : (ss : UniqNames funs vars) => (s : String) -> (0 _ : NameIsNew funs vars ss s) =>
            {default False isInfix : Bool} -> {default False isPure : Bool} ->
            UniqNames (fun :: funs) vars
  NewVar  : (ss : UniqNames funs vars) => (s : String) -> (0 _ : NameIsNew funs vars ss s) => UniqNames funs ((::) var vars)

public export
interface NamesRestrictions where
  reservedKeywords : SortedSet String

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

rawNewName : Fuel ->
             (Fuel -> Gen MaybeEmpty String) =>
             (funs : List Function) -> (vars : List BasicType) -> (names : UniqNames funs vars) ->
             Gen MaybeEmpty (s ** NameIsNew funs vars names s)

export
genNewName : Fuel -> Gen MaybeEmpty String ->
             NamesRestrictions =>
             (funs : List Function) -> (vars : List BasicType) -> (names : UniqNames funs vars) ->
             Gen MaybeEmpty (s ** NameIsNew funs vars names s)
genNewName fl genStr funs vars names = do
  nn@(nm ** _) <- rawNewName fl @{const genStr} funs vars names
  if nm `contains` reservedKeywords
    then assert_total $ genNewName fl genStr funs vars names -- we could reduce fuel instead of `assert_total`
    else pure nn

varName : UniqNames funs vars -> IndexIn vars -> String
varName (JustNew @{ss} _) i         = varName ss i
varName (NewFun @{ss} _)  i         = varName ss i
varName (NewVar s)        Here      = s
varName (NewVar @{ss} _)  (There i) = varName ss i


printExpr : {funs : _} -> {vars : _} -> {opts : _} ->
            (names : UniqNames funs vars) =>
            Prec -> Expr casts funs vars ty -> Gen0 $ Doc opts

printExpr p $ Const $ I k = pure $ line $ show k
printExpr p $ Const $ B False = pure $ "false"
printExpr p $ Const $ B True = pure $ "true"
printExpr p $ Const $ S str = pure $ line $ str
printExpr p $ Let var = pure $ line $ varName names var


printStmts : {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
             (names : UniqNames funs vars) =>
             (newNames : Gen0 String) =>
             Fuel ->
             (toplevel : Bool) ->
             Stmts casts funs vars retTy -> Gen0 $ Doc opts


--------------------------------------------------------------------------------
-- Main

wrapMain : {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
           (names : UniqNames funs vars) =>
           (newNames : Gen0 String) =>
          --  (0 _ : IfUnsolved retTy Nothing) =>
           Fuel ->
           (indeed : Bool) ->
           (cont : Maybe $ Stmts casts funs vars retTy) ->
           Gen0 (Doc opts) -> Gen0 (Doc opts)
wrapMain fl False Nothing x = x
wrapMain fl False (Just cont) x = [| x `vappend` assert_total printStmts fl False cont |]
wrapMain fl True cont body = do
  (nm ** _) <- genNewName fl newNames _ _ names
  b <- body
  cnt <- for cont $ assert_total $ printStmts @{JustNew nm} fl False
  let b = maybe b (b `vappend`) cnt
  pure $ vsep $
    [ ""
    , "static void main(String[] args) {"
    , indent' 4 b
    , "}"
    ]

-------------------------------------------------------------


printStmts fl tl $ NewV ty initial cont = do
  (nm ** _) <- genNewName fl newNames _ _ names
  rest <- printStmts @{NewVar nm} fl tl cont
  let tyAscr = "def"
  let lhs = line nm <+> tyAscr <++> "="
  rhs <- printExpr Open initial
  pure $ flip vappend rest $ hangSep' 2 lhs rhs

printStmts fl tl $ (#=) n v cont = wrapMain fl tl (Just cont) $ do
  pure $ line (varName names n) <++> "=" <++> !(printExpr Open v)


namesGenGroovy : Gen0 String
namesGenGroovy = pack <$> listOf {length = choose (1, 10)} (choose ('a', 'z'))

export
printGroovy : {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
              (names : UniqNames funs vars) =>
              Fuel ->
              Stmts casts funs vars retTy -> Gen0 $ Doc opts
printGroovy fl = printStmts {names} {newNames = namesGenGroovy} fl True
