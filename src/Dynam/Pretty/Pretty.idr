module Dynam.Pretty.Pretty

import Dynam.Model.Main
import Dynam.Model.Primitives

import Test.DepTyCheck.Gen
import public Text.PrettyPrint.Bernardy
import System.Random.Pure.StdGen
import Data.Alternative
import Data.List
import Data.Fuel
import public Data.SortedSet

import Dynam.Pretty.Utils

%default total

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

unaryOps : List String
unaryOps = ["+", "-", "!", "~"]

-- public export
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




printExpr : {funs : _} -> {vars : _} -> {opts : _} ->
            (names : UniqNames funs vars) =>
            Prec ->
            Expr casts funs vars ty ->
            Gen0 $ Doc opts

printFunCall : {funs : _} -> {vars : _} -> {opts : _} ->
               (names : UniqNames funs vars) =>
               Prec ->
               IndexIn funs -> ExprList casts funs vars argTys -> Gen0 $ Doc opts
printFunCall p name args = do
  let fn = funName names name
  let f = line fn
  let args = toList $ getExprs args
  let tupledArgs = \as => map tuple $ for as $ \(Evidence _ e) => printExpr Open e
  case (isFunInfix names name, args, !(chooseAnyOf Bool)) of
    -- Call for bitwise infix extension method
    (True, [Evidence _ l, Evidence _ r], True) => pure $ parenthesise (p >= App) $ !(printExpr App l) <++> f <++> !(printExpr App r)
    -- Call for appropriate extension method with 0, 2 or more arguments
    (True, Evidence _ head :: args, _) => pure $ parenthesise (p >= App) $ !(printExpr App head) <+> "." <+> f <+> !(tupledArgs args)
    -- Call for normal function
    _ => pure $ parenthesise (p >= App && isUnaryOp fn args) $ hang' 2 f !(tupledArgs args)


printExpr p $ Const $ B False  = pure $ "false"
printExpr p $ Const $ B True   = pure $ "true"

printExpr p $ Const $ I num    = pure $ line $ show num
-- printExpr p $ Const $ S str = pure $ line $ str

printExpr p $ Var var          = pure $ line $ varName names var

printExpr p $ Invoke name args = assert_total printFunCall p name args


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
        [ "static void main(String[] args) {"
        , indent' 4 b
        , "}"
        ]

-------------------------------------------------------------


printStmts fl tl $ NewV ty initial cont = do
    (nm ** _) <- genNewName fl newNames _ _ names
    rest <- printStmts @{NewVar nm} fl tl cont
    let tyAscr = "def "
    let lhs = tyAscr <+> line nm <++> "="
    rhs <- printExpr Open initial
    pure $ flip vappend rest $ hangSep' 2 lhs rhs

printStmts fl tl $ Ret = wrapMain {casts} {funs} {vars} {retTy=Void} fl tl Nothing $ pure empty


printStmts fl tl $ (#=) n v cont = wrapMain fl tl (Just cont) $ do
    pure $ line (varName names n) <++> "=" <++> !(printExpr Open v)

printStmts fl tl $ If cond th el cont = wrapMain fl tl (Just cont) $ do
    -- thenBody  <- printStmts fl tl th
    -- elseBody  <- printStmts fl tl el
    -- condition <- printExpr Open cond
    let pre  = "if (" 
    let post = ") {"
    let header = pre <+> !(printExpr Open cond) <++> post
    pure $ vsep $
        [ header
        , indent' 4 !(printStmts fl False th)
        , "} else {"
        , indent' 4 !(printStmts fl False el)
        , "}"
        ]

namesGenGroovy : Gen0 String
namesGenGroovy = pack <$> listOf {length = choose (1, 10)} (choose ('a', 'z'))

export
printGroovy : {funs : _} -> {vars : _} -> {retTy : _} -> {opts : _} ->
              (names : UniqNames funs vars) =>
              Fuel ->
              Stmts casts funs vars retTy -> Gen0 $ Doc opts
printGroovy fl = printStmts {names} {newNames = namesGenGroovy} fl True
