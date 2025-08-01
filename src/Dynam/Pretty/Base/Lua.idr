module Dynam.Pretty.Base.Lua

import Dynam.Pretty.Base.Global

%default total
%hide Test.DepTyCheck.Gen.(<**>)
%hide Text.PrettyPrint.Bernardy.Core.Doc.(>>=)

printComment : {opts: LayoutOpts} -> Gen0 $ Doc opts
printComment = do
    linesCnt    <- choose (0, 5)
    isMultiline <- chooseAnyOf Bool

    case (linesCnt, isMultiline) of
        (0, _) => do
            pure empty
        (_, True) => do
            lines <- traverse id [ pack <$> listOf {length = choose (1, 80)} (choose ('+', '~')) | _ <- (genRange linesCnt) ]
            let lines = lines <&> \ln => line $ "  " ++ ln
            pure $ vsep [
                  line "--[["
                , vsep lines
                , line "]]"
            ]
        (_, False) => do
            lines <- traverse id [ pack <$> listOf {length = choose (1, 80)} (choose ('+', '~')) | _ <- (genRange linesCnt) ]
            let lines = lines <&> \ln => line $ "-- " ++ ln
            pure $ vsep lines

printInlineComment : {opts: LayoutOpts} -> Gen0 $ Doc opts
printInlineComment = do
    isEmpty <- chooseAnyOf Bool

    case isEmpty of
        False => do
            pure empty
        True  => do
            text <- pack <$> listOf {length = choose (1, 3)} (choose ('+', '~'))
            pure $ "--[[" <++> line text <++> "]]"

namespace CommentBase
    export infixr 6 <**>

    export
    (<**>) : {opts : LayoutOpts} -> Doc opts -> Doc opts -> Gen0 $ Doc opts
    (<**>) lhs rhs = pure $ lhs <++> !(printInlineComment) <++> rhs

namespace CommentRight
    export infixr 6 <**>
    
    export
    (<**>) : {opts : LayoutOpts} -> Doc opts -> Gen0 (Doc opts) -> Gen0 $ Doc opts
    (<**>) lhs rhs = do
        comment <- printInlineComment
        rhs <- rhs
        pure $ lhs <++> comment <++> rhs

namespace CommentLeft
    export infixr 6 <**>
    
    export
    (<**>) : {opts : LayoutOpts} -> Gen0 (Doc opts) -> Doc opts -> Gen0 $ Doc opts
    (<**>) lhs rhs = do
        comment <- printInlineComment
        lhs <- lhs
        pure $ lhs <++> comment <++> rhs

---------------------------------------------------------------------------------------------

printExpr : {funs : ListOfFunctions} ->
            {vars : ListOfBasicTypes} ->
            {opts: LayoutOpts} ->
            (names : UniqNames funs vars) =>
            Prec ->
            Expr casts funs vars ty ->
            Gen0 $ Doc opts

printFunCall : {funs : ListOfFunctions} ->
               {vars : ListOfBasicTypes} ->
               {opts : LayoutOpts} ->
               (names : UniqNames funs vars) =>
               Prec ->
               IndexIn funs ->
               ExprList casts funs vars argTys ->
               Gen0 $ Doc opts
printFunCall p name args = do
    let funName = genFunName names name
    let func = line funName
    let args = toList $ getExprs args
    let tupledArgs = \as => map tuple $ for as $ \(Evidence _ e) => printExpr {opts=opts} Open e

    case (isFunInfix names name, args) of
        (True, [Evidence _ l, Evidence _ r]) => do
            lhs <- printExpr App l
            rhs <- printExpr App r
            pure $ parenthesise (p >= App) $ lhs <++> !(printInlineComment) <++> func <++> !(printInlineComment) <++> rhs

        _ => do
            arguments <- tupledArgs args
            pure $ parenthesise (p >= App && isUnaryOp funName args) $ hang' 2 func arguments


printExpr p $ Literal Boolean  = do
    value <- chooseAnyOf Bool
    case value of
        False => pure "false"
        True  => pure "true"
printExpr p $ Literal Number = do
    value <- chooseAnyOf Int32
    pure $ line $ show value
printExpr p $ Literal Str = do
    str <- pack <$> listOf {length = choose (1, 6)} (choose ('0', '9'))
    pure $ "\"" <+> line str <+> "\""

printExpr p $ Var var = pure $ line $ genVarName names var

printExpr p $ Invoke name args = assert_total printFunCall p name args


printStmts : {funs : ListOfFunctions} ->
             {vars : ListOfBasicTypes} ->
             {opts : LayoutOpts} ->
             (names : UniqNames funs vars) =>
             (newNames : Gen0 String) =>
             Fuel ->
             (toplevel : Bool) ->
             Stmts casts funs vars -> Gen0 $ Doc opts


printStmts fl tl $ NewV ty initial cont = do
    (nm ** _) <- genNewName fl newNames _ _ names
    rest      <- printStmts @{NewVar nm} fl tl cont
    comment   <- printComment

    lhs <- "local" <**> line nm <**> "="
    rhs <- printExpr Open initial

    pure $ vsep [ 
          comment
        , hangSep' 2 lhs rhs
        , rest
    ]

printStmts fl tl $ Ret = do
    cmt <- chooseAnyOf Bool
    case cmt of
        True  => printComment
        False => pure empty

printStmts fl tl $ (#=) n v cont = do
    value   <- printExpr Open v
    rest    <- printStmts fl tl cont
    comment <- printComment

    let name = line $ genVarName names n

    assign <- name <**> "=" <**> value

    pure $ vsep [
          comment
        , assign
        , rest
    ]

printStmts fl tl $ If cond th el cont = do
    header <- "if" <**> printExpr Open cond <**> "then"
    rest   <- printStmts fl tl cont

    comment <- printComment

    pure $ vsep [
          comment
        , header
        , indent' 4 !(printStmts fl False th)
        , "else"
        , indent' 4 !(printStmts fl False el)
        , !(printInlineComment) <++> "end" <++> !(printInlineComment)
        , rest
    ]

printStmts fl tl $ While cond body cont = do
    (nm ** _) <- genNewName fl newNames _ _ names
    rest      <- printStmts @{JustNew nm} {opts} fl tl cont
    condExpr  <- printExpr {opts} Open cond
    body      <- printStmts @{JustNew nm} {opts} fl False body
    comment   <- printComment

    incr <- line nm <**> "=" <**> line nm <**> "+" <**> "1"
    decl <- "local" <**> line nm <**> "=" <**> "1"


    rand <- chooseAnyOf Bool

    case (tl, rand) of
        (True, True) => do
            fst   <- "(" <**> condExpr <**> ")" <**> "and" 
            snd   <- "(" <**> line nm <**> "<" <**> "1000" <**> ")"
            cond  <- fst <**> snd
            while <- "while" <**> cond <**> "do"

            pure $ vsep [
                  comment
                , decl
                , while
                , indent' 4 body
                , indent' 4 incr 
                , !(printInlineComment) <++> "done" <++> !(printInlineComment)
                , rest
            ]
        (False, True) => do
            fst   <- "(" <**> condExpr <**> ")" <**> "and" 
            snd   <- "(" <**> line nm <**> "<" <**> "100" <**> ")"
            cond  <- fst <**> snd
            while <- "while" <**> cond <**> "do"

            pure $ vsep [
                  comment
                , decl
                , while
                , indent' 4 body
                , indent' 4 incr 
                , !(printInlineComment) <++> "done" <++> !(printInlineComment)
                , rest
            ]
        _ => do
            ifdecl <- "if" <**> condExpr <**> "then"
            pure $ vsep [
                  comment
                , ifdecl
                , indent' 4 body
                , !(printInlineComment) <++> "end" <++> !(printInlineComment)
                , rest
            ]

printStmts fl tl $ Call name args cont = do
    func <- printFunCall Open name args
    rest <- printStmts fl tl cont

    comment <- printComment

    pure $ vsep [
          comment
        , func
        , rest
    ]
    

printStmts fl tl $ NewProc args body cont = do
    (nm ** _) <- genNewName fl newNames _ _ names
    rest <- printStmts {opts} fl tl cont

    (unique, argNames) <- genNewVars fl newNames args names
    let names : List String = argNames <&> \(name, ty) => name
    let argString = joinBy ", " names

    body <- printStmts @{unique} {opts} fl False body
    rand <- chooseAnyOf Bool

    comment <- printComment 

    arg  <- "(" <**> line argString <**> ")"
    decl <- "function" <**> line nm <**> arg

    pure $ vsep [
          comment
        , decl
        , indent' 4 body
        , !(printInlineComment) <++> "end" <++> !(printInlineComment)
        , rest
    ]

printStmts fl tl $ NewFun ty args body retExpr cont = do
    (nm ** _) <- genNewName fl newNames _ _ names
    retEx <- printExpr {opts} Open retExpr
    rest  <- printStmts {opts} fl tl cont

    (unique, argNames) <- genNewVars fl newNames args names
    let names : List String = argNames <&> \(name, tty) => name
    let argString = joinBy ", " names

    body <- printStmts @{unique} {opts} fl False body
    rand <- chooseAnyOf Bool

    comment <- printComment 

    arg  <- "(" <**> line argString <**> ")"
    decl <- "function" <**> line nm <**> arg
    ret  <- "return" <**> retEx

    pure $ vsep [
          comment
        , decl
        , indent' 4 body
        , indent' 4 ret
        , !(printInlineComment) <++> "end" <++> !(printInlineComment)
        , rest
    ]


export
printLua : {funs : ListOfFunctions} ->
          {vars : ListOfBasicTypes} ->
          {opts : LayoutOpts} ->
          (names : UniqNames funs vars) =>
          Fuel ->
          Stmts casts funs vars -> Gen0 $ Doc opts
printLua fl = printStmts {names} {newNames = namesGen} fl True
